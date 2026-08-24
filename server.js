/**
 * 盖帽/百分 —— 四人联机纸牌游戏（服务端）
 *
 * 规则要点：
 *  - 4 人分两对（南北 vs 东西），座位按加入顺序固定：第1人=南，第2人=西，第3人=北，第4人=东。
 *  - 54 张牌（含大小王），每人 12 张，底牌 6 张；只能单张出牌。
 *    发牌约 80% 为均衡牌型（四家手牌每种花色至少各 1 张），约 20% 保持纯随机（保留极端牌型增添趣味）。
 *  - 分数牌 5/10/K 共 100 分；本轮赢家若属于非庄家方，分数牌归其并累入 P，否则作废。
 *  - 叫分逆时针进行（右手边为下家），每人只叫一次（最多4次）：80 起，每次加价至少 5 分；
 *    每局首位叫分者必须叫分（最低80），后续叫分必须高于当前叫分，叫到 100 分立即停止进入“板百”。
 *  - 叫分最高者为庄家：庄家直接补入 6 张底牌并先暗弃 6 张（不公开），然后选择主牌花色再开始出牌；
 *    板百模式下底牌与弃牌均公开。
 *  - 大小王在确定主牌后视为“主牌花色”的牌：领出王视为领出主牌；跟主牌时可直接出王（王就是主牌）。
 *  - 板百途中非庄家一旦拉到分（P>=5）立即结束整局；每墩结束后保留四张牌展示，直到赢家出下一墩第一张牌。
 *  - 每墩之间庄家方可申请“成牌”：公开申请人手牌并全员表决；一致同意则本局按正常计分提前结束，
 *    有人不同意则继续出牌（已公开的手牌保持公开）。
 *  - 每局首叫玩家按固定座位顺序轮转（南→东→北→西→南），与谁当庄家无关；新的大局从南家重新开始，
 *    积分清零；大局（整局）胜利数跨大局累计。
 *  - 第 12 轮若赢家属于非庄家方，立即“翻底”，非庄家方整局胜利。
 *  - 常规局计分：P=0 庄家方 +200；成 (0<P<=100-B) 庄家方 100-P、非庄家 P；
 *    破 (P>100-B) 庄家方 -B，非庄家 P（P>=40 时 4P）。
 *  - 任意一方累计分先达 +300 胜、-300 负（板百/翻底优先）。
 *
 * 运行：npm install ws && node server.js （默认端口 8080，浏览器访问 http://IP:8080）
 */

const WebSocket = require('ws');
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = parseInt(process.env.PORT, 10) || 8080;
const HOST = process.env.HOST || '0.0.0.0';
// 断线玩家自动操作延时 / 离线踢出延时（测试时可缩短）
const AUTO_ACT_DELAY = parseInt(process.env.AUTO_ACT_DELAY, 10) || 30000;
const KICK_DELAY = parseInt(process.env.KICK_DELAY, 10) || 120000;

const SEATS = ['south', 'west', 'north', 'east'];
const SUITS = ['S', 'H', 'D', 'C'];
const RANKS = ['2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K', 'A'];
const SCORE_MAP = { '5': 5, '10': 10, 'K': 10 };
const ALLOWED_BIDS = [80, 85, 90, 95, 100];
const PARTNER = { south: 'north', north: 'south', west: 'east', east: 'west' };
// 逆时针（右手边为下家）：南 → 东 → 北 → 西
const NEXT_SEAT = { south: 'east', east: 'north', north: 'west', west: 'south' };
// 左手边（上一手）：南←西←北←东←南
const PREV_SEAT = { south: 'west', west: 'north', north: 'east', east: 'south' };
const SEAT_LABELS = { south: '南', west: '西', north: '北', east: '东' };
const TEAM_OF_SEAT = { south: 'ns', north: 'ns', west: 'ew', east: 'ew' };
const OTHER_TEAM = { ns: 'ew', ew: 'ns' };
const TEAM_NAMES = { ns: '南北队', ew: '东西队' };
const SUIT_ORDER = { H: 3, S: 2, D: 1, C: 0 };
// 每局首个叫分玩家按固定座位顺序轮转：南 → 东 → 北 → 西 → 南……
const START_ORDER = ['south', 'east', 'north', 'west'];

const rooms = new Map(); // roomCode -> room

/* ================= 账号系统 ================= */
/* 配置 DATABASE_URL（PostgreSQL）时账号持久化存储；否则退化为内存存储（服务重启后失效）。 */

function createMemoryUsersStore() {
  const users = new Map(); // username -> user
  return {
    async init() {},
    async findUserByUsername(username) { return users.get(username) || null; },
    async findUserByToken(token) {
      if (!token) return null;
      for (const u of users.values()) if (u.token === token) return u;
      return null;
    },
    async createUser({ username, passwordHash, nickname }) {
      const user = { username, passwordHash, nickname, token: null, createdAt: new Date().toISOString(), lastLogin: null, totalGames: 0, wins: 0 };
      users.set(username, user);
      return user;
    },
    async setToken(username, token) { const u = users.get(username); if (u) u.token = token; },
    async updateLastLogin(username) { const u = users.get(username); if (u) u.lastLogin = new Date().toISOString(); },
    async recordGame(username, won) {
      const u = users.get(username);
      if (u) { u.totalGames += 1; if (won) u.wins += 1; }
    }
  };
}

function createPgUsersStore() {
  const { Pool } = require('pg');
  const pool = new Pool({
    connectionString: process.env.DATABASE_URL,
    ssl: process.env.DATABASE_SSL === 'false' ? false : { rejectUnauthorized: false }
  });
  const q = (text, params) => pool.query(text, params);
  const toUser = (row) => ({
    username: row.username,
    passwordHash: row.password_hash,
    nickname: row.nickname,
    token: row.token,
    createdAt: row.created_at,
    lastLogin: row.last_login,
    totalGames: row.total_games,
    wins: row.wins
  });
  return {
    async init() {
      await q(`CREATE TABLE IF NOT EXISTS users (
        id SERIAL PRIMARY KEY,
        username VARCHAR(50) UNIQUE NOT NULL,
        password_hash VARCHAR(255) NOT NULL,
        nickname VARCHAR(50) NOT NULL,
        token VARCHAR(64),
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        last_login TIMESTAMP,
        total_games INT DEFAULT 0,
        wins INT DEFAULT 0
      )`);
    },
    async findUserByUsername(username) {
      const r = await q('SELECT * FROM users WHERE username = $1', [username]);
      return r.rows[0] ? toUser(r.rows[0]) : null;
    },
    async findUserByToken(token) {
      if (!token) return null;
      const r = await q('SELECT * FROM users WHERE token = $1', [token]);
      return r.rows[0] ? toUser(r.rows[0]) : null;
    },
    async createUser({ username, passwordHash, nickname }) {
      const r = await q('INSERT INTO users (username, password_hash, nickname) VALUES ($1,$2,$3) RETURNING *', [username, passwordHash, nickname]);
      return toUser(r.rows[0]);
    },
    async setToken(username, token) {
      await q('UPDATE users SET token = $1 WHERE username = $2', [token, username]);
    },
    async updateLastLogin(username) {
      await q('UPDATE users SET last_login = CURRENT_TIMESTAMP WHERE username = $1', [username]);
    },
    async recordGame(username, won) {
      await q('UPDATE users SET total_games = total_games + 1, wins = wins + $1 WHERE username = $2', [won ? 1 : 0, username]);
    }
  };
}

const usersStore = process.env.DATABASE_URL ? createPgUsersStore() : createMemoryUsersStore();
if (!process.env.DATABASE_URL) {
  console.log('未配置 DATABASE_URL，账号保存在内存中（服务重启后失效）。需要持久化请配置 PostgreSQL。');
}

function genToken() {
  return crypto.randomBytes(32).toString('hex');
}

/* ================= 纯逻辑工具 ================= */

function buildDeck() {
  const deck = [];
  for (const s of SUITS) {
    for (const r of RANKS) deck.push(`${s}_${r}`);
  }
  deck.push('JOKER_BIG', 'JOKER_SMALL');
  return deck;
}

function shuffle(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function cardSuit(card) {
  if (card === 'JOKER_BIG' || card === 'JOKER_SMALL') return 'JOKER';
  return String(card).split('_')[0];
}

function cardRank(card) {
  if (card === 'JOKER_BIG') return 'BIG';
  if (card === 'JOKER_SMALL') return 'SMALL';
  return String(card).split('_')[1];
}

function cardPoints(card) {
  return SCORE_MAP[cardRank(card)] || 0;
}

function isJoker(card) {
  return card === 'JOKER_BIG' || card === 'JOKER_SMALL';
}

function rankValue(rank) {
  const i = RANKS.indexOf(rank);
  return i === -1 ? 0 : i + 1; // A=13 ... 2=1
}

function sortCards(cards) {
  // 手牌排序：大王、小王、红桃、黑桃、方块、梅花，同花色按 A>K>...>2
  const v = (c) => {
    if (c === 'JOKER_BIG') return 10000;
    if (c === 'JOKER_SMALL') return 9999;
    return SUIT_ORDER[cardSuit(c)] * 100 + rankValue(cardRank(c));
  };
  return cards.slice().sort((a, b) => v(b) - v(a));
}

/**
 * 单张牌的吃墩价值：
 * 大王 > 小王 > 主牌(A>K>...>2) > 跟出同花色的副牌 > 垫牌(最小)
 * 若领出的是王（无花色），则其余牌按“主牌 > 副牌比点数”。
 */
function cardPlayValue(card, trump, ledSuit) {
  if (card === 'JOKER_BIG') return 1000;
  if (card === 'JOKER_SMALL') return 999;
  const rv = rankValue(cardRank(card));
  if (cardSuit(card) === trump) return 500 + rv;
  if (ledSuit === null) return rv;
  if (cardSuit(card) === ledSuit) return rv;
  return 0;
}

/**
 * 跟牌校验。大小王在确定主牌后视为“主牌花色”，出牌时直接算主牌：
 *  - 领出的是主牌时：手中有任何主牌（含王）必须跟主牌，可直接出王；没有任何主牌时可任意垫牌。
 *  - 领出的是副牌时：手中有该花色必须跟出（王不算该花色）。
 */
function canPlayCard(hand, card, ledSuit, trump) {
  if (ledSuit === null) return true;
  if (ledSuit === trump) {
    const hasTrump = hand.some((c) => isJoker(c) || cardSuit(c) === trump);
    if (hasTrump) return isJoker(card) || cardSuit(card) === trump;
    return true;
  }
  const hasLed = hand.some((c) => !isJoker(c) && cardSuit(c) === ledSuit);
  if (hasLed) return !isJoker(card) && cardSuit(card) === ledSuit;
  return true;
}

function evaluateTrick(trick, order, trump, ledSuit) {
  let winner = order[0];
  let best = -1;
  for (const seat of order) {
    const v = cardPlayValue(trick[seat], trump, ledSuit);
    if (v > best) {
      best = v;
      winner = seat;
    }
  }
  return winner;
}

function trickPoints(trick) {
  let sum = 0;
  for (const s of SEATS) {
    if (trick[s]) sum += cardPoints(trick[s]);
  }
  return sum;
}

/**
 * 常规局计分（B=叫分，P=非庄家本局得分）。
 * 注：规格中“破”只明确了 25<=P<40 得 P、P>=40 得 4P；
 * 对于 P<25 的“破”，按同样得 P 处理。
 */
function scoreRound(bid, p) {
  if (p === 0) return { dealer: 200, nonDealer: 0, label: '干推' };
  if (p <= 100 - bid) return { dealer: 100 - p, nonDealer: p, label: '庄家成' };
  const nonDealer = p >= 40 ? 4 * p : p;
  return { dealer: -bid, nonDealer, label: '庄家破' };
}

/* ================= 房间 / 对局管理 ================= */

function publicPlayers(room) {
  const players = {};
  for (const seat of SEATS) {
    const rec = room.players[seat];
    players[seat] = rec
      ? { name: room.names[seat], connected: rec.online }
      : { name: room.names[seat] || null, connected: false };
  }
  return players;
}

function publicState(room) {
  const base = {
    phase: 'waiting',
    players: publicPlayers(room),
    scores: room.match ? room.match.scores : { ns: 0, ew: 0 },
    matchWins: room.stats ? room.stats.matchWins : { ns: 0, ew: 0 },
    gameCount: room.match ? room.match.gameCount : 0
  };
  const g = room.game;
  if (!g) return base;
  return {
    phase: g.phase,
    players: base.players,
    bid: g.bid,
    bidder: g.bidder,
    turn: g.turn,
    dealer: g.dealer,
    dealerTeam: g.dealerTeam,
    trump: g.trump,
    bottomRevealed: g.bottomRevealed,
    bottom: g.bottomRevealed ? g.bottom : null,
    pickupTarget: g.pickupTarget,
    discarder: g.discarder,
    discardCards: g.bottomRevealed ? g.discardCards : null,
    round: g.round,
    trick: g.trick,
    trickOrder: g.trickOrder,
    trickWinner: g.trickWinner,
    ledSuit: g.ledSuit,
    p: g.p,
    lastResult: g.lastResult,
    claimSeat: g.claimSeat,
    claimVotes: g.claimVotes,
    revealedSeat: g.revealedSeat,
    revealedCards: g.revealedSeat ? g.hands[g.revealedSeat] : null,
    scores: room.match ? room.match.scores : { ns: 0, ew: 0 },
    matchWins: room.stats ? room.stats.matchWins : { ns: 0, ew: 0 },
    gameCount: room.match ? room.match.gameCount : 0,
    over: g.over,
    handCounts: {
      south: g.hands.south.length,
      west: g.hands.west.length,
      north: g.hands.north.length,
      east: g.hands.east.length
    }
  };
}

function send(ws, msg) {
  if (ws && ws.readyState === WebSocket.OPEN) {
    try { ws.send(JSON.stringify(msg)); } catch (e) { /* ignore */ }
  }
}

function sendError(ws, text) {
  send(ws, { type: 'error', text });
}

function playerWs(room, seat) {
  const rec = room.players[seat];
  return rec ? rec.ws : null;
}

function sendToSeat(room, seat, msg) {
  send(playerWs(room, seat), msg);
}

function broadcast(room, msg) {
  for (const seat of SEATS) {
    sendToSeat(room, seat, msg);
  }
}

function broadcastState(room) {
  broadcast(room, { type: 'state', public: publicState(room) });
  scheduleTurnAutoAct(room);
}

function broadcastRoom(room) {
  broadcast(room, { type: 'room', players: publicPlayers(room) });
  broadcastState(room);
}

function seatName(room, seat) {
  return room.names[seat] ? `${room.names[seat]}（${SEAT_LABELS[seat]}家）` : SEAT_LABELS[seat] + '家';
}

function genPlayerId() {
  return Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 10);
}

/**
 * 发牌：约 80% 概率发出均衡牌型（四家手牌每种花色至少各 1 张），约 20% 概率纯随机。
 * 实测纯随机发牌时“四手每种花色均≥1张”的比例约 69.06%，因此强制均衡的概率取 35%，
 * 使最终约 80% 的牌局为均衡牌型、约 20% 为极端牌型（保留游戏趣味性）。
 */
function dealHands() {
  if (Math.random() < 0.35) {
    for (let attempt = 0; attempt < 200; attempt++) {
      const deck = shuffle(buildDeck());
      const hands = {};
      let ok = true;
      SEATS.forEach((seat, i) => {
        hands[seat] = deck.slice(i * 12, i * 12 + 12);
        for (const s of SUITS) {
          if (hands[seat].filter((c) => cardSuit(c) === s).length < 1) ok = false;
        }
      });
      if (ok) return { hands, bottom: deck.slice(48, 54) };
    }
  }
  // 纯随机发牌（允许极端牌型）
  const deck = shuffle(buildDeck());
  const hands = {};
  SEATS.forEach((seat, i) => {
    hands[seat] = deck.slice(i * 12, i * 12 + 12);
  });
  return { hands, bottom: deck.slice(48, 54) };
}

function dealNewRound(room) {
  // 首叫玩家由本大局已完成的局数决定（固定座位顺序轮转，与谁当庄家无关）
  const firstBidder = START_ORDER[room.match.gameCount % 4];
  const { hands, bottom } = dealHands();
  const g = {
    phase: 'bidding',
    firstBidder,
    bid: 0,
    bidder: null,
    acted: { south: false, west: false, north: false, east: false },
    turn: firstBidder,
    dealer: null,
    dealerTeam: null,
    trump: null,
    bottom,
    bottomRevealed: false,
    pickupTarget: null,
    discarder: null,
    discardCards: null,
    hands,
    round: 0,
    trick: { south: null, west: null, north: null, east: null },
    trickOrder: [],
    trickWinner: null,
    ledSuit: null,
    p: 0,
    lastResult: null,
    claimSeat: null,
    claimVotes: null,
    revealedSeat: null,
    over: null
  };
  room.game = g;
  for (const seat of SEATS) {
    sendToSeat(room, seat, { type: 'hand', cards: sortCards(hands[seat]) });
  }
  broadcast(room, { type: 'notice', text: `第${room.match.gameCount + 1}局开始，${seatName(room, firstBidder)}先叫分` });
  broadcastState(room);
  broadcast(room, { type: 'turn', player: g.turn });
}

function startNewGame(room) {
  room.match = { scores: { ns: 0, ew: 0 }, gameCount: 0 };
  dealNewRound(room);
}

function assignSeat(room, ws, name, seat) {
  const playerId = genPlayerId();
  room.players[seat] = { ws, playerId, name, account: ws.account || null, online: true, offlineAt: null, autoTimer: null, kickTimer: null };
  room.names[seat] = name;
  ws.playerId = playerId;
  ws.roomCode = room.code;
  ws.seat = seat;
  // 对局进行中：接管该座位的现有手牌继续玩；否则空手牌
  const existingHand = room.game ? room.game.hands[seat].slice() : [];
  send(ws, { type: 'init', room: room.code, seat, name, hand: existingHand, playerId });
  broadcastRoom(room);
  if (room.game) {
    broadcast(room, { type: 'notice', text: `${name}（${SEAT_LABELS[seat]}家）加入并接管该座位（牌保留）` });
    send(ws, { type: 'state_sync', room: room.code, seat, hand: existingHand, public: publicState(room) });
  } else if (SEATS.every((s) => room.players[s])) {
    if (room.nextStart === 'resume') {
      room.nextStart = null;
      broadcast(room, { type: 'notice', text: '房间已满，从当前分数接续，自动发牌！' });
      dealNewRound(room);
    } else {
      room.nextStart = null;
      broadcast(room, { type: 'notice', text: '房间已满，自动发牌！' });
      startNewGame(room);
    }
  }
}

function finishBidding(room, dealer) {
  const g = room.game;
  g.dealer = dealer;
  g.dealerTeam = [dealer, PARTNER[dealer]];
  g.turn = dealer;
  if (g.bid === 100) {
    g.phase = 'pickup_choose';
    g.bottomRevealed = true;
    broadcast(room, { type: 'notice', text: `${seatName(room, dealer)} 叫分100！板百！底牌亮出，庄家方协商由谁补牌` });
  } else {
    // 常规局：庄家直接补入底牌，先暗弃6张
    g.hands[dealer].push(...g.bottom);
    g.hands[dealer] = sortCards(g.hands[dealer]);
    g.pickupTarget = dealer;
    g.discarder = dealer;
    g.phase = 'discard';
    sendToSeat(room, dealer, { type: 'hand', cards: g.hands[dealer].slice() });
    broadcast(room, {
      type: 'notice',
      text: `${seatName(room, dealer)} 以 ${g.bid} 分坐庄，补入6张底牌，请先从手中弃掉6张（不公开）`
    });
  }
  broadcastState(room);
  broadcast(room, { type: 'turn', player: g.turn });
}

function endMatch(room, winnerTeam, reason) {
  const g = room.game;
  // 大局（整局）胜利计数：跨大局累计，不随新大局清零
  room.stats.matchWins[winnerTeam] += 1;
  // 账号战绩：有账号的玩家记录总局数与胜局数
  for (const seat of SEATS) {
    const rec = room.players[seat];
    if (rec && rec.account) {
      usersStore.recordGame(rec.account, TEAM_OF_SEAT[seat] === winnerTeam).catch(() => {});
    }
  }
  g.phase = 'game_over';
  g.over = {
    winnerTeam,
    reason,
    scores: { ns: room.match.scores.ns, ew: room.match.scores.ew },
    matchWins: { ns: room.stats.matchWins.ns, ew: room.stats.matchWins.ew }
  };
  broadcast(room, {
    type: 'game_over',
    winner: winnerTeam,
    reason,
    scores: { ns: room.match.scores.ns, ew: room.match.scores.ew },
    matchWins: { ns: room.stats.matchWins.ns, ew: room.stats.matchWins.ew }
  });
  broadcast(room, { type: 'notice', text: `整局结束：${TEAM_NAMES[winnerTeam]}获胜（${reason}）` });
  broadcastState(room);
  // 自动开始新的大局（积分清零、从南家重新叫分）
  const gRef = g;
  setTimeout(() => {
    if (room.game === gRef && room.game.phase === 'game_over') {
      broadcast(room, { type: 'notice', text: '新的大局即将开始，积分清零，从南家重新叫分！' });
      startNewGame(room);
    }
  }, 8000);
}

/**
 * 常规局结算（正常打完第12轮或“成牌”申请成功时共用）：
 * 按 干推/成/破 计分、累加累计分与胜局数，再判断整局是否结束。
 */
function settleRegularRound(room) {
  const g = room.game;
  const dealerTeamKey = TEAM_OF_SEAT[g.dealer];
  const nonDealerTeamKey = OTHER_TEAM[dealerTeamKey];
  const res = scoreRound(g.bid, g.p);
  room.match.scores[dealerTeamKey] += res.dealer;
  room.match.scores[nonDealerTeamKey] += res.nonDealer;
  room.match.gameCount += 1;
  g.lastResult = {
    label: res.label,
    bid: g.bid,
    p: g.p,
    dealerTeam: dealerTeamKey,
    dealerDelta: res.dealer,
    nonDealerDelta: res.nonDealer,
    scores: { ns: room.match.scores.ns, ew: room.match.scores.ew }
  };

  const s = room.match.scores;
  let winnerTeam = null;
  let reason = null;
  if (s.ns >= 300 || s.ew >= 300) {
    winnerTeam = s.ns === s.ew ? 'ns' : s.ns > s.ew ? 'ns' : 'ew';
    reason = '累计分达到 +300';
  } else if (s.ns <= -300) {
    winnerTeam = 'ew';
    reason = '南北队累计分达到 -300';
  } else if (s.ew <= -300) {
    winnerTeam = 'ns';
    reason = '东西队累计分达到 -300';
  }
  if (winnerTeam) {
    endMatch(room, winnerTeam, reason);
    return;
  }

  g.phase = 'round_end';
  broadcastState(room);
  const gRef = g;
  setTimeout(() => {
    if (room.game === gRef && room.game.phase === 'round_end') dealNewRound(room);
  }, 2600);
}

function resolveTrick(room) {
  const g = room.game;
  const winner = evaluateTrick(g.trick, g.trickOrder, g.trump, g.ledSuit);
  const isNonDealer = !g.dealerTeam.includes(winner);
  const total = trickPoints(g.trick);
  const counted = isNonDealer ? total : 0;
  if (counted) g.p += counted;
  g.trickWinner = winner;
  const isLast = g.round === 12;

  broadcast(room, {
    type: 'round_result',
    winner,
    points: counted,
    total_trick_points: total,
    p_total: g.p,
    last: isLast
  });

  if (isLast) {
    const dealerTeamKey = TEAM_OF_SEAT[g.dealer];
    const nonDealerTeamKey = OTHER_TEAM[dealerTeamKey];

    // 翻底：最后一张牌由非庄家方赢走，非庄家方整局胜利
    if (isNonDealer) {
      endMatch(room, nonDealerTeamKey, '翻底');
      return;
    }

    // 板百：忽略累计分，直接判整局胜负
    if (g.bid === 100) {
      if (g.p >= 5) {
        endMatch(room, nonDealerTeamKey, '板百：非庄家得分≥5');
      } else {
        endMatch(room, dealerTeamKey, '板百：干推，庄家方获胜（不加200分）');
      }
      return;
    }

    // 常规计分（与正常打完一局一致）
    settleRegularRound(room);
    return;
  }

  // 板百途中：非庄家一拉到分（P>=5）立即结束整局，无需打完
  if (g.bid === 100 && g.p >= 5) {
    const dealerTeamKey = TEAM_OF_SEAT[g.dealer];
    const nonDealerTeamKey = OTHER_TEAM[dealerTeamKey];
    endMatch(room, nonDealerTeamKey, '板百：非庄家得分≥5');
    return;
  }

  // 进入下一墩：保留四张牌展示与赢家，直到赢家打出下一墩第一张牌才消失
  g.round += 1;
  g.turn = winner;
  g.ledSuit = null;
  broadcastState(room);
  broadcast(room, { type: 'turn', player: winner });
}

/* ================= 消息处理 ================= */

function handleJoin(ws, msg) {
  if (ws.roomCode) {
    sendError(ws, '你已经在一个房间中了');
    return;
  }
  const code = String(msg.room || '').trim();
  if (!/^\d{4}$/.test(code)) {
    sendError(ws, '房间号应为4位数字');
    return;
  }
  let room = rooms.get(code);
  if (!room) {
    room = { code, players: {}, names: {}, game: null, match: null, stats: { matchWins: { ns: 0, ew: 0 } }, nextStart: null };
    rooms.set(code, room);
  }
  const token = String(msg.token || '');
  const legacyPid = String(msg.playerId || '');
  const finishJoin = (effectiveName) => {
    const freeSeat = SEATS.find((s) => !room.players[s]);
    if (!freeSeat) {
      // 房间满：若自己的座位还保留（断线未踢出），直接恢复该座位（刷新页面后重进也能续上）
      for (const seat of SEATS) {
        const rec = room.players[seat];
        if (!rec || rec.online) continue;
        const byPid = legacyPid && rec.playerId === legacyPid;
        const byAcc = ws.account && rec.account === ws.account;
        if (!byPid && !byAcc) continue;
        rec.ws = ws;
        rec.online = true;
        rec.offlineAt = null;
        if (rec.autoTimer) { clearTimeout(rec.autoTimer); rec.autoTimer = null; }
        if (rec.kickTimer) { clearTimeout(rec.kickTimer); rec.kickTimer = null; }
        ws.roomCode = room.code;
        ws.seat = seat;
        ws.playerId = rec.playerId; // 保持原 playerId，后续断线仍可识别
        const name = room.names[seat] || effectiveName;
        if (room.game) {
          send(ws, { type: 'state_sync', room: room.code, seat, hand: room.game.hands[seat], public: publicState(room) });
          broadcast(room, { type: 'notice', text: `${name}（${SEAT_LABELS[seat]}家）已重连` });
        } else {
          send(ws, { type: 'init', room: room.code, seat, name, hand: [], playerId: rec.playerId });
        }
        broadcastRoom(room);
        return;
      }
      sendError(ws, '房间已满，无法加入');
      return;
    }
    assignSeat(room, ws, effectiveName, freeSeat);
  };
  if (token) {
    // 已登录：验证 token，绑定账号身份；昵称优先用输入的，其次用账号昵称
    usersStore.findUserByToken(token).then((user) => {
      if (user) {
        ws.account = user.username;
        usersStore.updateLastLogin(user.username).catch(() => {});
        const nm = String(msg.name || '').trim().slice(0, 12) || user.nickname;
        finishJoin(nm);
      } else {
        send(ws, { type: 'notice', text: '登录已失效，将以游客身份加入' });
        finishJoin(String(msg.name || '').trim().slice(0, 12) || '玩家');
      }
    }).catch(() => finishJoin(String(msg.name || '').trim().slice(0, 12) || '玩家'));
    return;
  }
  finishJoin(String(msg.name || '').trim().slice(0, 12) || '玩家');
}

function performCall(room, seat, score) {
  const g = room.game;
  if (!g || g.phase !== 'bidding' || g.turn !== seat) return;
  const isPass = score === 0 || score === 'pass';
  if (isPass) {
    if (g.bid === 0) return; // 首位叫分者不能放弃
    g.acted[seat] = true;
  } else {
    if (!ALLOWED_BIDS.includes(score) || score <= g.bid) return;
    g.bid = score;
    g.bidder = seat;
    g.acted[seat] = true;
    if (score === 100) {
      finishBidding(room, seat);
      return;
    }
  }
  // 每人只叫一次：找下一个还没叫分的玩家，四人都叫过后由叫分最高者坐庄
  const unacted = SEATS.filter((s) => !g.acted[s]);
  if (unacted.length === 0) {
    finishBidding(room, g.bidder);
    return;
  }
  let next = NEXT_SEAT[seat];
  while (!unacted.includes(next)) next = NEXT_SEAT[next];
  g.turn = next;
  broadcastState(room);
  broadcast(room, { type: 'turn', player: g.turn });
}

function performTrump(room, seat, suit) {
  const g = room.game;
  if (!g || g.phase !== 'trump' || seat !== g.dealer || !SUITS.includes(suit)) return;
  g.trump = suit;
  g.phase = 'playing';
  g.round = 1;
  g.turn = g.dealer;
  broadcast(room, { type: 'notice', text: `主牌为 ${suit}，庄家先出牌` });
  broadcastState(room);
  broadcast(room, { type: 'turn', player: g.turn });
}

function performPickup(room, seat, target) {
  const g = room.game;
  if (!g || g.phase !== 'pickup_choose' || !g.dealerTeam.includes(seat) || !g.dealerTeam.includes(target)) return;
  g.pickupTarget = target;
  g.hands[target].push(...g.bottom);
  g.hands[target] = sortCards(g.hands[target]);
  g.discarder = target;
  g.phase = 'discard';
  g.turn = target;
  sendToSeat(room, target, { type: 'hand', cards: g.hands[target].slice() });
  broadcast(room, { type: 'notice', text: `${seatName(room, target)} 补入6张底牌，请先从手中弃掉6张（将公开）` });
  broadcastState(room);
  broadcast(room, { type: 'turn', player: target });
}

function performDiscard(room, seat, cards) {
  const g = room.game;
  if (!g || g.phase !== 'discard' || seat !== g.discarder) return;
  if (!Array.isArray(cards) || cards.length !== 6) return;
  const hand = g.hands[seat];
  for (const c of cards) {
    if (typeof c !== 'string' || !hand.includes(c)) return;
  }
  for (const c of cards) hand.splice(hand.indexOf(c), 1);
  g.discardCards = cards.slice();
  g.phase = 'trump';
  g.turn = g.dealer;
  sendToSeat(room, seat, { type: 'hand', cards: hand.slice() });
  broadcast(room, {
    type: 'notice',
    text: g.bottomRevealed
      ? `${seatName(room, seat)} 弃牌完成（已公开），庄家请选择主牌花色`
      : `${seatName(room, seat)} 弃牌完成，庄家请选择主牌花色`
  });
  broadcastState(room);
  broadcast(room, { type: 'turn', player: g.dealer });
}

function performPlay(room, seat, card) {
  const g = room.game;
  if (!g || g.phase !== 'playing' || g.turn !== seat) return;
  const hand = g.hands[seat];
  if (!hand.includes(card) || !canPlayCard(hand, card, g.ledSuit, g.trump)) return;
  hand.splice(hand.indexOf(card), 1);
  if (g.trickOrder.length === 4) {
    // 上一墩的四张牌仍在展示，赢家打出下一墩第一张牌时清掉（其余情况无需清空）
    g.trick = { south: null, west: null, north: null, east: null };
    g.trickWinner = null;
    g.trickOrder = [];
  }
  g.trick[seat] = card;
  g.trickOrder.push(seat);
  sendToSeat(room, seat, { type: 'hand', cards: hand.slice() });
  if (g.trickOrder.length === 1) {
    // 大小王在确定主牌后视为主牌花色，领出王即领出主牌
    g.ledSuit = isJoker(card) ? g.trump : cardSuit(card);
  }
  if (g.trickOrder.length < 4) {
    g.turn = NEXT_SEAT[seat];
    broadcastState(room);
    broadcast(room, { type: 'turn', player: g.turn });
    return;
  }
  resolveTrick(room);
}

function performClaimVote(room, seat, agree) {
  const g = room.game;
  if (!g || g.phase !== 'claim' || g.claimVotes[seat] !== null) return;
  g.claimVotes[seat] = agree === true;
  broadcastState(room);
  if (!SEATS.every((s) => g.claimVotes[s] !== null)) return;

  const allAgree = SEATS.every((s) => g.claimVotes[s] === true);
  if (!allAgree) {
    g.phase = 'playing';
    g.claimVotes = null;
    broadcast(room, { type: 'notice', text: '成牌申请被拒绝，游戏继续（已公开的手牌保持公开）' });
    broadcastState(room);
    return;
  }

  // 全部同意：本局按正常规则提前结束
  broadcast(room, { type: 'notice', text: '所有玩家一致认同，庄家方成牌！本局提前结束' });
  if (g.bid === 100) {
    const dealerTeamKey = TEAM_OF_SEAT[g.dealer];
    const nonDealerTeamKey = OTHER_TEAM[dealerTeamKey];
    if (g.p >= 5) {
      endMatch(room, nonDealerTeamKey, '板百：非庄家得分≥5');
    } else {
      endMatch(room, dealerTeamKey, '板百：庄家成牌（干推）');
    }
    return;
  }
  settleRegularRound(room);
}

function handleCall(ws, room, msg) {
  const g = room.game;
  if (!g || g.phase !== 'bidding') { sendError(ws, '当前不是叫分阶段'); return; }
  if (g.turn !== ws.seat) { sendError(ws, '还没轮到你叫分'); return; }
  const isPass = msg.pass === true || msg.score === 0 || msg.score === 'pass';
  if (isPass && g.bid === 0) { sendError(ws, '你是本局第一位叫分者，不能放弃，必须叫分（最低80）'); return; }
  if (!isPass && !ALLOWED_BIDS.includes(msg.score)) { sendError(ws, '叫分无效，只能叫 80/85/90/95/100'); return; }
  if (!isPass && msg.score <= g.bid) { sendError(ws, '叫分必须高于当前叫分（至少加5分）'); return; }
  performCall(room, ws.seat, isPass ? 0 : msg.score);
}

function handleTrump(ws, room, msg) {
  const g = room.game;
  if (!g || g.phase !== 'trump') { sendError(ws, '当前不是选择主牌阶段'); return; }
  if (ws.seat !== g.dealer) { sendError(ws, '只有庄家能选择主牌'); return; }
  if (!SUITS.includes(msg.suit)) { sendError(ws, '主牌花色无效'); return; }
  performTrump(room, ws.seat, msg.suit);
}

function handlePickup(ws, room, msg) {
  const g = room.game;
  if (!g || g.phase !== 'pickup_choose') { sendError(ws, '当前不是补牌阶段'); return; }
  if (!g.dealerTeam.includes(ws.seat)) { sendError(ws, '只有庄家方能决定补牌'); return; }
  if (!g.dealerTeam.includes(msg.player)) { sendError(ws, '补牌对象无效'); return; }
  performPickup(room, ws.seat, msg.player);
}

function handleDiscard(ws, room, msg) {
  const g = room.game;
  if (!g || g.phase !== 'discard') { sendError(ws, '当前不是弃牌阶段'); return; }
  if (ws.seat !== g.discarder) { sendError(ws, '还没轮到你弃牌'); return; }
  const cards = Array.isArray(msg.cards) ? msg.cards : [];
  if (cards.length !== 6) { sendError(ws, '必须正好弃掉6张牌'); return; }
  const hand = g.hands[ws.seat];
  for (const c of cards) {
    if (typeof c !== 'string' || !hand.includes(c)) { sendError(ws, '弃牌中包含你手中没有的牌'); return; }
  }
  performDiscard(room, ws.seat, cards);
}

function handlePlay(ws, room, msg) {
  const g = room.game;
  if (!g || g.phase !== 'playing') { sendError(ws, '当前不是出牌阶段'); return; }
  if (g.turn !== ws.seat) { sendError(ws, '还没轮到你出牌'); return; }
  const card = String(msg.card || '');
  const hand = g.hands[ws.seat];
  if (!hand.includes(card)) { sendError(ws, '你手中没有这张牌'); return; }
  if (!canPlayCard(hand, card, g.ledSuit, g.trump)) { sendError(ws, '你有同花色牌，必须跟同花色'); return; }
  performPlay(room, ws.seat, card);
}

/** 庄家方申请“成牌”：公开申请人手牌，进入全员表决（仅限每墩之间）。 */
function handleClaim(ws, room) {
  const g = room.game;
  if (!g || g.phase !== 'playing') {
    sendError(ws, '当前不能申请成牌');
    return;
  }
  if (!g.dealerTeam.includes(ws.seat)) {
    sendError(ws, '只有庄家方可以申请成牌');
    return;
  }
  if (g.trickOrder.length !== 0 && g.trickOrder.length !== 4) {
    sendError(ws, '请在一墩结束之后（下家出牌前）再申请成牌');
    return;
  }
  g.claimSeat = ws.seat;
  g.revealedSeat = ws.seat; // 手牌公开给所有玩家（被拒绝后也保持公开）
  g.claimVotes = { south: null, west: null, north: null, east: null };
  g.phase = 'claim';
  broadcast(room, { type: 'notice', text: `${seatName(room, ws.seat)} 申请成牌，手牌已公开，请所有玩家表决` });
  broadcastState(room);
}

/** 成牌表决：全部同意则按正常计分提前结束本局；有人不同意则继续出牌。 */
function handleClaimVote(ws, room, msg) {
  const g = room.game;
  if (!g || g.phase !== 'claim') { sendError(ws, '当前不是成牌表决阶段'); return; }
  if (g.claimVotes[ws.seat] !== null) { sendError(ws, '你已经表决过了'); return; }
  performClaimVote(room, ws.seat, msg.agree === true);
}

/** 表情消息：校验文件存在后广播给所有玩家，并解析发送对象。 */
function handleEmoji(ws, room, msg) {
  const emoji = String(msg.emoji || '');
  const target = String(msg.target || 'all');
  // 文件名校验：禁止路径分隔符与 ..，必须是支持的图片格式；其余字符（中文、空格等）都允许
  if (
    emoji.length < 1 || emoji.length > 100 ||
    emoji.includes('/') || emoji.includes('\\') || emoji.includes('..') ||
    !IMAGE_EXTS.has(path.extname(emoji).toLowerCase())
  ) {
    sendError(ws, '表情文件名无效');
    return;
  }
  const dir = path.join(__dirname, 'emojis');
  fs.readdir(dir, (err, files) => {
    if (err || !Array.isArray(files) || !files.includes(emoji)) {
      sendError(ws, '表情不存在，请确认图片已放入 emojis 文件夹');
      return;
    }
    let to = 'all';
    if (target === 'partner') to = PARTNER[ws.seat];
    else if (target === 'left') to = PREV_SEAT[ws.seat];
    else if (target === 'right') to = NEXT_SEAT[ws.seat];
    else if (target !== 'all') {
      sendError(ws, '发送对象无效');
      return;
    }
    broadcast(room, { type: 'emoji', emoji, from: ws.seat, to });
  });
}

function handleMessage(ws, msg) {
  switch (msg.type) {
    case 'join':
      handleJoin(ws, msg);
      break;
    case 'reconnect':
      handleReconnect(ws, msg);
      break;
    case 'call': {
      const room = rooms.get(ws.roomCode);
      if (room) handleCall(ws, room, msg);
      break;
    }
    case 'trump': {
      const room = rooms.get(ws.roomCode);
      if (room) handleTrump(ws, room, msg);
      break;
    }
    case 'pickup': {
      const room = rooms.get(ws.roomCode);
      if (room) handlePickup(ws, room, msg);
      break;
    }
    case 'discard': {
      const room = rooms.get(ws.roomCode);
      if (room) handleDiscard(ws, room, msg);
      break;
    }
    case 'play': {
      const room = rooms.get(ws.roomCode);
      if (room) handlePlay(ws, room, msg);
      break;
    }
    case 'claim': {
      const room = rooms.get(ws.roomCode);
      if (room) handleClaim(ws, room);
      break;
    }
    case 'claim_vote': {
      const room = rooms.get(ws.roomCode);
      if (room) handleClaimVote(ws, room, msg);
      break;
    }
    case 'emoji': {
      const room = rooms.get(ws.roomCode);
      if (room) handleEmoji(ws, room, msg);
      break;
    }
    case 'end_game': {
      const room = rooms.get(ws.roomCode);
      if (room) handleEndGame(ws, room);
      break;
    }
    case 'match_choice': {
      const room = rooms.get(ws.roomCode);
      if (room) handleMatchChoice(ws, room, msg);
      break;
    }
    default:
      sendError(ws, '未知消息类型');
  }
}

function removeSeat(room, seat) {
  const rec = room.players[seat];
  if (rec) {
    if (rec.autoTimer) clearTimeout(rec.autoTimer);
    if (rec.kickTimer) clearTimeout(rec.kickTimer);
  }
  delete room.players[seat];
  delete room.names[seat];
}

function handleClose(ws) {
  const room = rooms.get(ws.roomCode);
  if (!room) return;
  const seat = ws.seat;
  const rec = room.players[seat];
  if (!seat || !rec || rec.ws !== ws) return; // 旧连接/已重连的旧 socket 忽略
  const name = room.names[seat] || seat;

  // 对局结束后的离开，或尚未开局：直接移除座位
  if (!room.game || room.game.phase === 'game_over') {
    removeSeat(room, seat);
    if (room.game && room.game.phase === 'game_over') room.game = null;
    broadcast(room, { type: 'notice', text: `${name}（${SEAT_LABELS[seat]}家）离开房间` });
    broadcastRoom(room);
    if (!SEATS.some((s) => room.players[s])) rooms.delete(room.code);
    return;
  }

  // 对局中退出：直接释放座位（不保留离线状态），牌保留，等待任意玩家加入接管
  removeSeat(room, seat);
  broadcast(room, { type: 'notice', text: `${name}（${SEAT_LABELS[seat]}家）已离开房间，其牌保留，等待新玩家加入接管` });
  broadcastState(room);
  if (!SEATS.some((s) => room.players[s])) rooms.delete(room.code);
}

/** 断线重连：按 playerId 找回座位，恢复状态快照。 */
function handleReconnect(ws, msg) {
  const pid = String(msg.playerId || '');
  const token = String(msg.token || '');
  const restore = (room, seat, rec) => {
    rec.ws = ws;
    rec.online = true;
    rec.offlineAt = null;
    if (rec.autoTimer) { clearTimeout(rec.autoTimer); rec.autoTimer = null; }
    if (rec.kickTimer) { clearTimeout(rec.kickTimer); rec.kickTimer = null; }
    ws.roomCode = room.code;
    ws.seat = seat;
    ws.playerId = pid;
    const name = room.names[seat] || '玩家';
    if (room.game) {
      // 恢复完整状态：公共状态 + 自己的手牌
      send(ws, { type: 'state_sync', room: room.code, seat, hand: room.game.hands[seat], public: publicState(room) });
      broadcast(room, { type: 'notice', text: `${name}（${SEAT_LABELS[seat]}家）已重连` });
      broadcastState(room);
    } else {
      send(ws, { type: 'game_ended', reason: '对局已结束，请重新开始' });
      send(ws, { type: 'state', public: publicState(room) });
    }
  };
  const scan = (match) => {
    for (const room of rooms.values()) {
      for (const seat of SEATS) {
        const rec = room.players[seat];
        if (rec && match(rec, seat)) return restore(room, seat, rec);
      }
    }
    return false;
  };
  const finish = () => {
    // 优先按账号匹配（跨设备），其次按 playerId 匹配（同浏览器）
    if (ws.account && scan((rec) => rec.account === ws.account)) return;
    if (pid && scan((rec) => rec.playerId === pid)) return;
    // 座位已释放（退出即离房）：若提供了房间号且对局仍在，接管一个空座位（牌保留）
    const code = String(msg.room || '');
    const room = rooms.get(code);
    if (room && room.game && room.game.phase !== 'game_over') {
      const freeSeat = SEATS.find((s) => !room.players[s]);
      if (freeSeat) {
        assignSeat(room, ws, '玩家', freeSeat);
        return;
      }
    }
    sendError(ws, '无法恢复对局，请重新进入房间');
  };
  if (token) {
    usersStore.findUserByToken(token).then((user) => {
      if (user) ws.account = user.username;
      finish();
    }).catch(() => finish());
    return;
  }
  finish();
}

/** 有人离线等太久时，在线玩家可主动结束对局，回到等待状态并选择接续方式。 */
function handleEndGame(ws, room) {
  const g = room.game;
  if (!g || g.phase === 'game_over' || g.phase === 'round_end') {
    sendError(ws, '当前不能结束对局');
    return;
  }
  // 有新规则下退出即释放座位：只要有空位（有人离开未补齐），即可主动结束
  const anyVacant = SEATS.some((s) => !room.players[s]);
  if (!anyVacant) {
    sendError(ws, '当前没有空位，无需结束对局');
    return;
  }
  // 座位已随退出释放，无需额外移除
  const scores = { ns: room.match.scores.ns, ew: room.match.scores.ew };
  const wins = { ns: room.stats.matchWins.ns, ew: room.stats.matchWins.ew };
  room.game = null;
  room.nextStart = null;
  broadcast(room, { type: 'game_ended', reason: '玩家主动结束对局' });
  broadcast(room, { type: 'abort_choice', scores, roundWins: wins });
  broadcast(room, { type: 'notice', text: '对局已结束，请选择重新开新大局或从当前分数接续' });
  broadcastRoom(room);
}

/** 结束对局后由在场玩家选择：重新开大局（积分清零）或从当前分数接续。 */
function handleMatchChoice(ws, room, msg) {
  const mode = String(msg.mode || '');
  if (mode !== 'new' && mode !== 'resume') {
    sendError(ws, '无效的选择');
    return;
  }
  if (room.game) {
    sendError(ws, '当前对局尚未结束，不能选择接续方式');
    return;
  }
  room.nextStart = mode;
  if (mode === 'new') {
    room.match = { scores: { ns: 0, ew: 0 }, gameCount: 0 };
    broadcast(room, { type: 'notice', text: `${seatName(room, ws.seat)} 选择重新开始新的大局，积分已清零，等待玩家加入` });
  } else {
    broadcast(room, { type: 'notice', text: `${seatName(room, ws.seat)} 选择从当前分数接续，等待新玩家加入后继续` });
  }
  broadcastRoom(room);
}

/* ================= 断线自动托管 ================= */

/** 该座位离线玩家当前是否需要系统代操作（轮到叫分/补牌/选主/弃牌/表决/出牌等）。 */
function needsAction(room, seat) {
  const g = room.game;
  if (!g) return false;
  switch (g.phase) {
    case 'bidding':
      return g.turn === seat;
    case 'pickup_choose':
      // 仅当庄家方全部离线时才自动补牌，避免和在线队友的操作冲突
      return g.dealerTeam.includes(seat) && !g.dealerTeam.some((s) => {
        const r = room.players[s];
        return r && r.online;
      });
    case 'trump':
      return g.turn === seat;
    case 'discard':
      return g.discarder === seat;
    case 'claim':
      return g.claimVotes ? g.claimVotes[seat] === null : false;
    case 'playing':
      return g.turn === seat;
    default:
      return false;
  }
}

function scheduleTurnAutoAct(room) {
  const g = room.game;
  if (!g) return;
  // 空座自动托管：座位已有人接管或不再需要操作时取消
  if (g.vacantTimer && g.vacantSeat) {
    const vs = g.vacantSeat;
    if (room.players[vs] || !needsAction(room, vs)) {
      clearTimeout(g.vacantTimer);
      g.vacantTimer = null;
      g.vacantSeat = null;
    }
  }
  for (const seat of SEATS) {
    const rec = room.players[seat];
    const vacant = !rec;
    if (!vacant && rec.online) continue;
    if (needsAction(room, seat)) {
      if (vacant) {
        // 玩家离开且无人接管：30秒后自动托管，保证游戏继续
        if (!g.vacantTimer) {
          g.vacantSeat = seat;
          g.vacantTimer = setTimeout(() => {
            g.vacantTimer = null;
            g.vacantSeat = null;
            if (room.game === g && !room.players[seat] && needsAction(room, seat)) autoAct(room, seat);
          }, AUTO_ACT_DELAY);
        }
      } else if (!rec.autoTimer) {
        rec.autoTimer = setTimeout(() => {
          rec.autoTimer = null;
          if (!room.players[seat] || rec.online || !needsAction(room, seat)) return;
          autoAct(room, seat);
        }, AUTO_ACT_DELAY);
      }
    } else if (rec && rec.autoTimer) {
      clearTimeout(rec.autoTimer);
      rec.autoTimer = null;
    }
  }
}

function autoPlayCard(hand, ledSuit, trump) {
  const legal = hand.filter((c) => canPlayCard(hand, c, ledSuit, trump));
  const byRank = (a, b) => rankValue(cardRank(a)) - rankValue(cardRank(b));
  const nontrump = legal.filter((c) => !isJoker(c) && cardSuit(c) !== trump).sort(byRank);
  if (nontrump.length) return nontrump[0];
  const trumps = legal.filter((c) => isJoker(c) || cardSuit(c) === trump).sort(byRank);
  if (trumps.length) return trumps[0];
  return legal[0];
}

function autoDiscardCards(hand) {
  // 弃掉最小的6张（先非主牌后主牌，按点数）
  const sorted = hand.slice().sort((a, b) => {
    const ta = cardSuit(a) === 'JOKER' ? 1 : 0;
    const tb = cardSuit(b) === 'JOKER' ? 1 : 0;
    return (ta - tb) || (rankValue(cardRank(a)) - rankValue(cardRank(b)));
  });
  return sorted.slice(0, 6);
}

function autoTrumpSuit(hand) {
  let best = 'S';
  let bestN = -1;
  for (const s of SUITS) {
    const n = hand.filter((c) => cardSuit(c) === s).length;
    if (n > bestN) { bestN = n; best = s; }
  }
  return best;
}

function autoAct(room, seat) {
  const g = room.game;
  if (!g) return;
  const name = room.names[seat] || SEAT_LABELS[seat] + '家';
  broadcast(room, {
    type: 'notice',
    text: room.players[seat] ? `${name} 已离线，系统自动操作…` : `${name} 座位空缺，系统自动托管…`
  });
  try {
    switch (g.phase) {
      case 'bidding':
        performCall(room, seat, g.bid === 0 ? 80 : 0);
        break;
      case 'pickup_choose':
        performPickup(room, seat, g.dealer);
        break;
      case 'trump':
        performTrump(room, seat, autoTrumpSuit(g.hands[seat]));
        break;
      case 'discard':
        performDiscard(room, seat, autoDiscardCards(g.hands[seat]));
        break;
      case 'claim':
        performClaimVote(room, seat, true);
        break;
      case 'playing':
        performPlay(room, seat, autoPlayCard(g.hands[seat], g.ledSuit, g.trump));
        break;
      default:
        break;
    }
  } catch (e) {
    console.error('自动操作失败:', e);
  }
}

/* ================= HTTP + WebSocket 服务器 ================= */

const MIME_TYPES = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'application/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.gif': 'image/gif',
  '.webp': 'image/webp',
  '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon',
  '.txt': 'text/plain; charset=utf-8'
};
const IMAGE_EXTS = new Set(['.png', '.jpg', '.jpeg', '.gif', '.webp', '.svg']);

function sendJson(res, status, obj) {
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8' });
  res.end(JSON.stringify(obj));
}

function readJsonBody(req, cb) {
  let body = '';
  req.on('data', (c) => { body += c; if (body.length > 10000) req.destroy(); });
  req.on('end', () => { try { cb(JSON.parse(body || '{}')); } catch (e) { cb(null); } });
  req.on('error', () => {});
}

async function handleRegister(res, body) {
  try {
    const username = String((body && body.username) || '').trim();
    const password = String((body && body.password) || '');
    const nickname = String((body && body.nickname) || '').trim().slice(0, 12) || '玩家';
    if (!/^[A-Za-z0-9_]{3,20}$/.test(username)) return sendJson(res, 400, { error: '账号需为3-20位字母/数字/下划线' });
    if (password.length < 6 || password.length > 64) return sendJson(res, 400, { error: '密码长度需为6-64位' });
    const existing = await usersStore.findUserByUsername(username);
    if (existing) return sendJson(res, 409, { error: '账号已存在' });
    const bcrypt = require('bcryptjs');
    const hash = await bcrypt.hash(password, 10);
    await usersStore.createUser({ username, passwordHash: hash, nickname });
    const token = genToken();
    await usersStore.setToken(username, token);
    sendJson(res, 200, { token, username, nickname });
  } catch (e) {
    console.error('注册失败:', e);
    sendJson(res, 500, { error: '服务器错误' });
  }
}

async function handleLogin(res, body) {
  try {
    const username = String((body && body.username) || '').trim();
    const password = String((body && body.password) || '');
    if (!username || !password) return sendJson(res, 400, { error: '请输入账号和密码' });
    const u = await usersStore.findUserByUsername(username);
    const bcrypt = require('bcryptjs');
    if (!u || !(await bcrypt.compare(password, u.passwordHash))) return sendJson(res, 401, { error: '账号或密码错误' });
    const token = genToken();
    await usersStore.setToken(username, token);
    usersStore.updateLastLogin(username).catch(() => {});
    sendJson(res, 200, { token, username, nickname: u.nickname });
  } catch (e) {
    console.error('登录失败:', e);
    sendJson(res, 500, { error: '服务器错误' });
  }
}

const server = http.createServer((req, res) => {
  let url;
  try {
    url = decodeURIComponent((req.url || '/').split('?')[0]);
  } catch (e) {
    res.writeHead(400, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Bad Request');
    return;
  }
  if (url === '/api/register' && req.method === 'POST') {
    readJsonBody(req, (body) => handleRegister(res, body));
    return;
  }
  if (url === '/api/login' && req.method === 'POST') {
    readJsonBody(req, (body) => handleLogin(res, body));
    return;
  }
  if (url === '/api/me' && req.method === 'GET') {
    const token = new URL(req.url, 'http://x').searchParams.get('token') || '';
    usersStore.findUserByToken(token).then((u) => {
      if (!u) return sendJson(res, 401, { error: '未登录' });
      sendJson(res, 200, { username: u.username, nickname: u.nickname });
    }).catch(() => sendJson(res, 500, { error: '服务器错误' }));
    return;
  }
  if (url === '/' || url === '/index.html') {
    fs.readFile(path.join(__dirname, 'index.html'), (err, data) => {
      if (err) {
        res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' });
        res.end('未找到 index.html（请把 index.html 与 server.js 放在同一目录）');
        return;
      }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(data);
    });
    return;
  }

  // 表情包目录列表（emojis 文件夹不存在/为空时返回空数组，方便客户端展示“暂无表情包”）
  if (url === '/emojis' || url === '/list-emojis' || url === '/emojis/') {
    const dir = path.join(__dirname, 'emojis');
    fs.readdir(dir, (err, files) => {
      let emojis = [];
      if (!err && Array.isArray(files)) {
        emojis = files.filter((f) => IMAGE_EXTS.has(path.extname(f).toLowerCase())).sort();
      }
      res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8' });
      res.end(JSON.stringify({ emojis }));
    });
    return;
  }

  // 静态资源托管（emojis 文件夹内的图片等），带路径穿越防护
  if (url.includes('..')) {
    res.writeHead(403, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Forbidden');
    return;
  }
  const filePath = path.normalize(path.join(__dirname, url));
  const rootPrefix = path.join(__dirname) + path.sep;
  if (!filePath.startsWith(rootPrefix)) {
    res.writeHead(403, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Forbidden');
    return;
  }
  const ext = path.extname(filePath).toLowerCase();
  fs.readFile(filePath, (err, data) => {
    if (err) {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      res.end('Not Found');
      return;
    }
    res.writeHead(200, { 'Content-Type': MIME_TYPES[ext] || 'application/octet-stream' });
    res.end(data);
  });
});

const wss = new WebSocket.Server({ server, path: '/ws' });

wss.on('connection', (ws) => {
  ws.isAlive = true;
  ws.on('pong', () => {
    ws.isAlive = true;
  });
  ws.on('message', (raw) => {
    let msg;
    try {
      msg = JSON.parse(raw.toString());
    } catch (e) {
      return;
    }
    if (!msg || typeof msg !== 'object') return;
    try {
      handleMessage(ws, msg);
    } catch (err) {
      console.error('处理消息出错:', err);
      sendError(ws, '服务器内部错误');
    }
  });
  ws.on('close', () => handleClose(ws));
  ws.on('error', () => {});
});

const heartbeat = setInterval(() => {
  for (const ws of wss.clients) {
    if (ws.isAlive === false) {
      ws.terminate();
      continue;
    }
    ws.isAlive = false;
    try {
      ws.ping();
    } catch (e) { /* ignore */ }
  }
}, 30000);
heartbeat.unref(); // 仅在测试 require 时避免挂起进程；正式运行时由 listen 保持进程常驻

wss.on('close', () => clearInterval(heartbeat));

if (require.main === module) {
  usersStore.init().catch((e) => console.error('账号存储初始化失败:', e));
  server.listen(PORT, HOST, () => {
    console.log('盖帽/百分 服务器已启动');
    console.log(`HTTP: http://${HOST}:${PORT}  （浏览器访问）`);
    console.log(`WS:   ws://${HOST}:${PORT}/ws`);
  });
}

module.exports = {
  buildDeck,
  shuffle,
  dealHands,
  cardSuit,
  cardRank,
  cardPoints,
  rankValue,
  sortCards,
  cardPlayValue,
  canPlayCard,
  evaluateTrick,
  trickPoints,
  scoreRound,
  SEATS,
  SUITS,
  RANKS,
  ALLOWED_BIDS,
  TEAM_NAMES
};
