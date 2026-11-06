'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const INDEX = path.join(__dirname, 'public', 'index.html');
const ROOM_TTL_MS = 6 * 60 * 60 * 1000;
const MAX_PLAYERS = 16;
const MIN_PLAYERS = 4;

const ROLE_NAME = { wolf: 'หมาป่า', villager: 'ชาวบ้าน', seer: 'ผู้หยั่งรู้', doctor: 'หมอ' };
const rooms = new Map();

/* ---------- helpers ---------- */
function dist(n) {
  const w = n >= 12 ? 3 : n >= 8 ? 2 : 1;
  const s = n >= 5 ? 1 : 0;
  const d = n >= 6 ? 1 : 0;
  return { w, s, d, v: n - w - s - d };
}
function genCode() {
  const a = 'ABCDEFGHJKMNPQRSTUVWXYZ';
  for (let k = 0; k < 50; k++) {
    let s = '';
    for (let i = 0; i < 4; i++) s += a[crypto.randomInt(a.length)];
    if (!rooms.has(s)) return s;
  }
  return null;
}
const pid = () => crypto.randomBytes(4).toString('hex');
function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
function cleanName(s) {
  return String(s || '').replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, 16);
}
function winner(room) {
  let w = 0, o = 0;
  for (const p of room.players.values()) {
    if (!room.roles[p.id] || !room.alive[p.id]) continue;
    if (room.roles[p.id] === 'wolf') w++; else o++;
  }
  if (w === 0) return 'village';
  if (w >= o) return 'wolf';
  return null;
}

/* ---------- room model ---------- */
function newRoom(code) {
  return {
    code, hostToken: null, phase: 'lobby', game: pid(), round: 0,
    players: new Map(), // token -> {token,id,name,ts,ws}
    roles: {}, alive: {}, acts: {}, log: [], seer: null, winner: null,
    touched: Date.now(),
  };
}
function resetToLobby(room) {
  room.phase = 'lobby'; room.game = pid(); room.round = 0;
  room.roles = {}; room.alive = {}; room.acts = {}; room.log = [];
  room.seer = null; room.winner = null;
}
function byId(room, id) {
  for (const p of room.players.values()) if (p.id === id) return p;
  return null;
}
function nameOf(room, id) { const p = byId(room, id); return p ? p.name : 'ผู้เล่น'; }
function connected(p) { return !!(p.ws && p.ws.readyState === 1); }
function hostOf(room) {
  const h = room.players.get(room.hostToken);
  if (h && connected(h)) return h;
  for (const p of room.players.values()) if (connected(p)) return p; // host fallback
  return h || null;
}
function aliveIds(room) {
  return [...room.players.values()].map(p => p.id).filter(id => room.roles[id] && room.alive[id]);
}
function nightNeeded(room) {
  return aliveIds(room).filter(id => ['wolf', 'seer', 'doctor'].includes(room.roles[id]));
}
function hasValidAct(room, id) {
  const to = room.acts[id];
  return !!to && !!room.alive[to];
}

/* ---------- game flow ---------- */
function startGame(room) {
  const ids = [...room.players.values()].map(p => p.id);
  const d = dist(ids.length);
  const list = [];
  for (let i = 0; i < d.w; i++) list.push('wolf');
  for (let i = 0; i < d.s; i++) list.push('seer');
  for (let i = 0; i < d.d; i++) list.push('doctor');
  for (let i = 0; i < d.v; i++) list.push('villager');
  shuffle(list);
  room.roles = {}; room.alive = {};
  ids.forEach((id, i) => { room.roles[id] = list[i]; room.alive[id] = true; });
  room.phase = 'night'; room.round = 1; room.acts = {}; room.seer = null; room.winner = null;
  room.log = [{ r: 1, k: 'info', t: 'เกมเริ่มแล้ว มี ' + ids.length + ' คน' }];
}
function resolveNight(room) {
  const ids = aliveIds(room);
  const valid = (id, pred) => {
    const to = room.acts[id];
    if (!to || !room.alive[to]) return null;
    return !pred || pred(to) ? to : null;
  };
  const tally = {};
  ids.filter(i => room.roles[i] === 'wolf').forEach(w => {
    const t = valid(w, t => room.roles[t] !== 'wolf');
    if (t) tally[t] = (tally[t] || 0) + 1;
  });
  let victim = null;
  const ent = Object.entries(tally);
  if (ent.length) {
    const m = Math.max(...ent.map(e => e[1]));
    const top = ent.filter(e => e[1] === m).map(e => e[0]);
    victim = top[crypto.randomInt(top.length)];
  }
  const docId = ids.find(i => room.roles[i] === 'doctor');
  const prot = docId ? valid(docId) : null;
  const seerId = ids.find(i => room.roles[i] === 'seer');
  const seen = seerId ? valid(seerId, t => t !== seerId) : null;
  const killed = victim && victim !== prot ? victim : null;
  if (killed) {
    room.alive[killed] = false;
    room.log.push({ r: room.round, k: 'night', t: nameOf(room, killed) + ' ถูกหมาป่ากัดตายในคืนนี้' });
  } else {
    room.log.push({ r: room.round, k: 'night', t: 'คืนนี้ไม่มีใครตาย' });
  }
  room.seer = seen ? { r: room.round, by: seerId, to: seen, wolf: room.roles[seen] === 'wolf' } : null;
  room.acts = {};
  const win = winner(room);
  room.phase = win ? 'end' : 'day';
  room.winner = win;
}
function resolveVote(room) {
  const tally = {};
  aliveIds(room).forEach(v => {
    const to = room.acts[v];
    if (to && room.alive[to] && to !== v) tally[to] = (tally[to] || 0) + 1;
  });
  const ent = Object.entries(tally).sort((a, b) => b[1] - a[1]);
  if (ent.length) {
    room.log.push({ r: room.round, k: 'vote', t: 'ผลโหวต: ' + ent.map(e => nameOf(room, e[0]) + ' ' + e[1] + ' คะแนน').join(' · ') });
    if (ent.length === 1 || ent[0][1] > ent[1][1]) {
      const out = ent[0][0];
      room.alive[out] = false;
      room.log.push({ r: room.round, k: 'vote', t: nameOf(room, out) + ' ถูกประหาร และเป็น' + ROLE_NAME[room.roles[out]] });
    } else {
      room.log.push({ r: room.round, k: 'vote', t: 'คะแนนเสมอ ไม่มีใครถูกประหาร' });
    }
  } else {
    room.log.push({ r: room.round, k: 'vote', t: 'ไม่มีใครโหวต ไม่มีใครถูกประหาร' });
  }
  room.acts = {};
  const win = winner(room);
  room.winner = win;
  if (win) room.phase = 'end';
  else { room.phase = 'night'; room.round += 1; }
}
function autoAdvance(room) {
  if (room.phase === 'night' && nightNeeded(room).every(id => hasValidAct(room, id))) resolveNight(room);
  else if (room.phase === 'vote' && aliveIds(room).every(id => hasValidAct(room, id))) resolveVote(room);
}
// A player who left or died mid-phase can make the phase complete.
function dropPlayer(room, p) {
  if (room.phase === 'lobby') {
    room.players.delete(p.token);
    if (room.hostToken === p.token) {
      const next = room.players.values().next().value;
      room.hostToken = next ? next.token : null;
    }
    if (!room.players.size) rooms.delete(room.code);
    return;
  }
  // in a running game the player stays (as a disconnected seat) so they can come back
}

/* ---------- views (each player only sees what they may) ---------- */
function viewFor(room, p) {
  const me = p.id;
  const myRole = room.roles[me] || null;
  const host = hostOf(room);
  const end = room.phase === 'end';
  const players = [...room.players.values()].map(q => {
    const r = room.roles[q.id];
    let role = null;
    if (r && (end || q.id === me || (myRole === 'wolf' && r === 'wolf'))) role = r;
    return {
      id: q.id, name: q.name, connected: connected(q),
      inGame: !!r, alive: !!room.alive[q.id], role,
      isHost: !!host && host.id === q.id,
    };
  });
  const v = {
    code: room.code, phase: room.phase, round: room.round, game: room.game,
    me: { id: me, role: myRole, alive: !!room.alive[me], isHost: !!host && host.id === me },
    players, log: room.log, winner: room.winner,
    myAct: room.acts[me] || null,
  };
  if (myRole === 'wolf') {
    v.mates = players.filter(q => q.id !== me && q.role === 'wolf').map(q => ({ id: q.id, to: room.acts[q.id] || null }));
  }
  if (myRole === 'seer' && room.seer && room.seer.by === me) v.seer = { to: room.seer.to, wolf: room.seer.wolf, r: room.seer.r };
  if (v.me.isHost) {
    if (room.phase === 'night') { const need = nightNeeded(room); v.progress = { done: need.filter(id => hasValidAct(room, id)).length, total: need.length }; }
    if (room.phase === 'vote') { const al = aliveIds(room); v.progress = { done: al.filter(id => hasValidAct(room, id)).length, total: al.length }; }
  }
  if (room.phase === 'lobby') v.dist = dist(Math.max(room.players.size, MIN_PLAYERS));
  return v;
}
function send(ws, obj) { if (ws && ws.readyState === 1) ws.send(JSON.stringify(obj)); }
function broadcast(room) {
  room.touched = Date.now();
  for (const p of room.players.values()) if (connected(p)) send(p.ws, { t: 'state', v: viewFor(room, p) });
}

/* ---------- websocket ---------- */
const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/' || url === '/index.html') {
    fs.readFile(INDEX, (err, data) => {
      if (err) { res.writeHead(500); res.end('server error'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(data);
    });
  } else if (url === '/healthz') {
    res.writeHead(200); res.end('ok');
  } else {
    res.writeHead(404); res.end('not found');
  }
});
const wss = new WebSocketServer({ server, maxPayload: 4096 });

function attach(ws, room, token) {
  const p = room.players.get(token);
  if (p.ws && p.ws !== ws) { try { p.ws.close(4000, 'replaced'); } catch (e) {} }
  p.ws = ws;
  ws.ctx = { code: room.code, token };
}

wss.on('connection', (ws) => {
  ws.alive = true;
  ws.on('pong', () => { ws.alive = true; });
  ws.on('message', (raw) => {
    let m;
    try { m = JSON.parse(raw.toString()); } catch (e) { return; }
    if (!m || typeof m.t !== 'string') return;
    try { handle(ws, m); } catch (e) { console.error(e); send(ws, { t: 'err', m: 'เกิดข้อผิดพลาดในเซิร์ฟเวอร์' }); }
  });
  ws.on('close', () => {
    const c = ws.ctx; if (!c) return;
    const room = rooms.get(c.code); if (!room) return;
    const p = room.players.get(c.token);
    if (!p || p.ws !== ws) return;
    p.ws = null;
    if (room.phase === 'lobby') dropPlayer(room, p);
    if (rooms.has(room.code)) broadcast(room);
  });
});

function handle(ws, m) {
  const token = typeof m.token === 'string' ? m.token.slice(0, 64) : '';
  if (m.t === 'create') {
    const name = cleanName(m.name);
    if (!name || token.length < 8) return send(ws, { t: 'err', m: 'ใส่ชื่อเล่นก่อน' });
    if (rooms.size >= 300) return send(ws, { t: 'err', m: 'เซิร์ฟเวอร์เต็ม ลองใหม่ภายหลัง' });
    const code = genCode();
    if (!code) return send(ws, { t: 'err', m: 'สร้างห้องไม่สำเร็จ ลองอีกครั้ง' });
    const room = newRoom(code);
    room.hostToken = token;
    room.players.set(token, { token, id: pid(), name, ts: Date.now(), ws: null });
    rooms.set(code, room);
    attach(ws, room, token);
    return broadcast(room);
  }
  if (m.t === 'join' || m.t === 'resume') {
    const code = String(m.code || '').toUpperCase().slice(0, 4);
    const room = rooms.get(code);
    if (!room) return send(ws, { t: m.t === 'resume' ? 'gone' : 'err', m: 'ไม่พบห้องรหัส ' + code });
    const existing = room.players.get(token);
    if (existing) {
      const name = cleanName(m.name);
      if (name && m.t === 'join') existing.name = name;
      attach(ws, room, token);
      return broadcast(room);
    }
    if (m.t === 'resume') return send(ws, { t: 'gone', m: 'คุณไม่ได้อยู่ในห้องนี้แล้ว' });
    const name = cleanName(m.name);
    if (!name || token.length < 8) return send(ws, { t: 'err', m: 'ใส่ชื่อเล่นก่อน' });
    if (room.phase !== 'lobby') return send(ws, { t: 'err', m: 'ห้องนี้เริ่มเล่นไปแล้ว เข้าใหม่ไม่ได้' });
    if (room.players.size >= MAX_PLAYERS) return send(ws, { t: 'err', m: 'ห้องเต็มแล้ว (สูงสุด ' + MAX_PLAYERS + ' คน)' });
    for (const q of room.players.values()) if (q.name === name) return send(ws, { t: 'err', m: 'มีคนใช้ชื่อ "' + name + '" ในห้องแล้ว เปลี่ยนชื่อนิดหนึ่ง' });
    room.players.set(token, { token, id: pid(), name, ts: Date.now(), ws: null });
    attach(ws, room, token);
    return broadcast(room);
  }

  // everything below needs a seat in a room
  const c = ws.ctx;
  const room = c && rooms.get(c.code);
  const p = room && room.players.get(c.token);
  if (!p) return send(ws, { t: 'gone', m: 'หลุดจากห้องแล้ว' });
  const host = hostOf(room);
  const isHost = !!host && host.token === p.token;

  switch (m.t) {
    case 'leave': {
      ws.ctx = null; p.ws = null;
      if (room.phase === 'lobby') dropPlayer(room, p);
      if (rooms.has(room.code)) broadcast(room);
      return send(ws, { t: 'gone', m: '' });
    }
    case 'start':
      if (!isHost || room.phase !== 'lobby' || room.players.size < MIN_PLAYERS) return;
      startGame(room); break;
    case 'act': {
      const to = String(m.to || '');
      const target = byId(room, to);
      if (!target) return;
      if (room.phase !== 'night' && room.phase !== 'vote') return;
      if (!room.alive[p.id] || !room.alive[to]) return;
      const role = room.roles[p.id];
      if (room.phase === 'night') {
        if (!['wolf', 'seer', 'doctor'].includes(role)) return;
        if (role === 'wolf' && room.roles[to] === 'wolf') return;
        if (role === 'seer' && to === p.id) return;
      } else if (to === p.id) return;
      room.acts[p.id] = to;
      autoAdvance(room); break;
    }
    case 'toVote':
      if (!isHost || room.phase !== 'day') return;
      room.phase = 'vote'; room.acts = {}; break;
    case 'forceNight':
      if (!isHost || room.phase !== 'night') return;
      resolveNight(room); break;
    case 'forceVote':
      if (!isHost || room.phase !== 'vote') return;
      resolveVote(room); break;
    case 'rematch':
      if (!isHost || room.phase !== 'end') return;
      resetToLobby(room); break;
    default: return;
  }
  broadcast(room);
}

/* ---------- housekeeping ---------- */
setInterval(() => {
  wss.clients.forEach((ws) => {
    if (!ws.alive) return ws.terminate();
    ws.alive = false; try { ws.ping(); } catch (e) {}
  });
  const now = Date.now();
  for (const [code, room] of rooms) if (now - room.touched > ROOM_TTL_MS) rooms.delete(code);
}, 25000);

if (require.main === module) {
  server.listen(PORT, '0.0.0.0', () => console.log('คืนหมาป่า รันอยู่ที่ http://localhost:' + PORT));
}
module.exports = { server, rooms, dist };
