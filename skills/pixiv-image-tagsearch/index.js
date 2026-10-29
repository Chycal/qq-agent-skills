// Pixiv「来张图」—— 按角色搜插画并发到当前会话，带 PID 索引去重
//
// 为什么 shell 出 curl 而不是用 api.fetch：
//   Pixiv 在国内必须走代理，而 Node 的 undici（globalThis.fetch）**不支持 socks5**，
//   只认 http(s) 代理，所以这里走 `curl --proxy socks5h://...`。
//   curl.exe 是 Windows 10 1803+ 自带的，无需额外安装。
//
// 核心设计：
//   1. 【选前过滤】爬过的作品（按 Pixiv 作品 ID 判定）在**挑选之前**就剔掉，
//      而不是挑完再逐个检查。后者在候选全是旧图时会空手而归、直接报失败。
//   2. 【PID 索引】<数据目录>/pixiv/pid-index.json 记录每个爬过的作品：
//      {pid: {file, folder, tags, author, title, bookmarks, likes,
//             firstSeen, lastSeen, sentCount, lastSent}}。
//      O(1) 查询，能回答"这张以前发过没、谁画的"。原子写，断电不会毁掉整个索引。
//      另有**目录扫描兜底**：按文件名里的 hash 后缀找已存在的文件，
//      这样从别的机器人迁移过来的图库也能被识别为"已入库"。
//   3. 【候选耗尽时降级】新图找完了就明说"这些是以前存过的"，而不是报失败。
//
// tag 翻译：模型在 tag 参数里直接给日文标签（它认识东方角色），工具把映射记进
// tag-dict.json，下次命中零成本。也支持从别处导入既有词典（见 legacyTagDict 设置）。

import { spawn } from 'node:child_process';   // 仅自动拉起 sing-box 用；网络层已不依赖外部进程
import fs from 'node:fs';
import path from 'node:path';
import net from 'node:net';
import tls from 'node:tls';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';

const PIXIV_REFERER = 'https://www.pixiv.net/';
const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36';
const IMG_EXT = new Set(['.png', '.jpg', '.jpeg', '.gif', '.webp']);
// 发图后/失败后提醒模型：QQ 里只显示 send_message 发出的内容，
// 模型回复里的普通文本不会进群——不提醒的话，配的短话经常被直接写在回复里，群里什么都看不到。
const RELAY_NOTE = '（重要：配的短话必须调用 send_message 工具发到当前会话，只写在回复文本里群里是看不到的。）';
const RELAY_NOTE_ERR = '（请用 send_message 工具把这个结果告诉当前会话，让群友知道这次没图；技术细节可以概括，不用照搬。只写在回复文本里群里看不到。）';

let cfg = () => ({});
let log = () => {};

// ── 数据目录（与程序其它数据同源，跟着一起备份）──────────────────────
function dataDir() {
  const base = process.env.QQ_AGENT_DATA_DIR
    || path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..', '..', '..', 'data');
  return path.join(base, 'pixiv');
}

// ── PID 索引 ────────────────────────────────────────────────────────
let ledger = null;

function ledgerFile() { return path.join(dataDir(), 'pid-index.json'); }

function loadLedger() {
  if (ledger) return ledger;
  try {
    const raw = JSON.parse(fs.readFileSync(ledgerFile(), 'utf8'));
    ledger = (raw && typeof raw === 'object' && !Array.isArray(raw)) ? raw : {};
  } catch {
    ledger = {};
  }
  return ledger;
}

function saveLedger() {
  try {
    fs.mkdirSync(dataDir(), { recursive: true });
    // 原子写：断电/崩溃时不会留下半截 JSON 把整个索引毁掉
    const p = ledgerFile();
    fs.writeFileSync(`${p}.tmp`, JSON.stringify(ledger, null, 2), 'utf8');
    fs.renameSync(`${p}.tmp`, p);
  } catch { /* 索引写不进去不该让这次爬图失败 */ }
}

function hasPid(pid) { return Boolean(loadLedger()[String(pid)]); }

function recordPid(pid, info = {}) {
  const l = loadLedger();
  const k = String(pid);
  const prev = l[k] || {};
  const sent = Boolean(info.sent);
  l[k] = {
    pid: Number(pid) || pid,
    file: info.file ?? prev.file ?? '',
    folder: info.folder ?? prev.folder ?? '',
    tags: info.tags ?? prev.tags ?? [],
    // 作品信息也一并存档：以后要回答"这张谁画的""有没有发过"时不用再联网查
    author: info.author ?? prev.author ?? '',
    title: info.title ?? prev.title ?? '',
    bookmarks: info.bookmarks ?? prev.bookmarks ?? 0,
    likes: info.likes ?? prev.likes ?? 0,
    firstSeen: prev.firstSeen || Date.now(),
    lastSeen: Date.now(),
    sentCount: (prev.sentCount || 0) + (sent ? 1 : 0),
    lastSent: sent ? Date.now() : (prev.lastSent || 0)
  };
  saveLedger();
}

// ── tag 词典（中/英 → Pixiv 日文标签）────────────────────────────────
let tagDict = null;

function tagDictFile() { return path.join(dataDir(), 'tag-dict.json'); }

function loadTagDict() {
  if (tagDict) return tagDict;
  tagDict = {};
  try {
    // 首次运行：如果配置了外部词典（从别的机器人迁移过来的），导入一次，已有翻译不浪费。
    // 两种格式都认：{"古明地恋": "古明地こいし"} 和 {"古明地恋": {"ja": "古明地こいし"}}
    const legacyPath = String(cfg()?.legacyTagDict || '').trim();
    if (!fs.existsSync(tagDictFile()) && legacyPath && fs.existsSync(legacyPath)) {
      const legacy = JSON.parse(fs.readFileSync(legacyPath, 'utf8'));
      for (const [name, v] of Object.entries(legacy || {})) {
        const ja = typeof v === 'string' ? v : (v && v.ja);
        if (ja) tagDict[name] = String(ja);
      }
      saveTagDict();
    } else {
      const raw = JSON.parse(fs.readFileSync(tagDictFile(), 'utf8'));
      if (raw && typeof raw === 'object' && !Array.isArray(raw)) tagDict = raw;
    }
  } catch { tagDict = {}; }
  return tagDict;
}

function saveTagDict() {
  try {
    fs.mkdirSync(dataDir(), { recursive: true });
    fs.writeFileSync(tagDictFile(), JSON.stringify(tagDict, null, 2), 'utf8');
  } catch { /* 同上，不影响本次 */ }
}

function rememberTag(name, ja) {
  const n = String(name || '').trim();
  const j = String(ja || '').trim();
  if (!n || !j || n === j) return;
  const d = loadTagDict();
  if (d[n] === j) return;
  d[n] = j;
  saveTagDict();
}

// ── 热度档位记忆（v1.1.3）───────────────────────────────────────────
// 记录每个词条当前用到的「N users入り」档位：热门档的新图发干净了就往下调，
// 下次直接从记住的档位开始，不再每次都从设定值重新走一遍已知的空档。
// 结构：{ [jaTag]: { floor: 900, updatedAt: 1698... } }
let floorState = null;

function floorFile() { return path.join(dataDir(), 'tag-floor.json'); }

function loadFloorState() {
  if (floorState) return floorState;
  try {
    const raw = JSON.parse(fs.readFileSync(floorFile(), 'utf8'));
    floorState = (raw && typeof raw === 'object' && !Array.isArray(raw)) ? raw : {};
  } catch { floorState = {}; }
  return floorState;
}

function saveFloorState() {
  try {
    fs.mkdirSync(dataDir(), { recursive: true });
    // 原子写，和 pid-index 一个套路
    const p = floorFile();
    fs.writeFileSync(`${p}.tmp`, JSON.stringify(floorState, null, 2), 'utf8');
    fs.renameSync(`${p}.tmp`, p);
  } catch { /* 档位记不进去不影响本次发图 */ }
}

function getFloor(jaTag, fallback) {
  const e = loadFloorState()[String(jaTag)];
  const f = Number(e?.floor);
  return Number.isFinite(f) && f > 0 ? f : fallback;
}

function setFloor(jaTag, floor) {
  const s = loadFloorState();
  const f = Number(floor);
  if (!Number.isFinite(f) || f <= 0) return;
  if (s[String(jaTag)]?.floor === f) return;
  s[String(jaTag)] = { floor: f, updatedAt: Date.now() };
  saveFloorState();
}

/**
 * 角色名 → Pixiv 标签 联想解析（v1.1.7）。
 * 用搜索框同款的联想接口 /ajax/search/tags/{词}：中文角色名能命中 Pixiv 官方
 * 的 pixpedia 翻译词典——比如「芙宁娜」的摘要写着『原神』の登場人物「フリーナ」の中国名，
 * parentTag 就是フリーナ。比让模型去外部搜索工具里查可靠得多（外部搜索常查到
 * 游戏/作品名，拿去当 tag 会搜出全作品的角色混图）。
 * 只在"摘要声明了查询词是 parentTag 的别名"时才采信（如「フリーナ」の中国名、
 * 「初音ミク」の正式な漢字表記），避免把原神/アークナイツ这类作品分类词解析出来。
 */
async function resolveTagViaSuggest(word, { proxy, timeoutMs, apiBase }) {
  const w = String(word || '').trim();
  if (!w) return null;
  try {
    const raw = await fetchViaNode(`${apiBase}/ajax/search/tags/${encodeURIComponent(w)}`, { proxy, timeoutMs });
    const data = JSON.parse(raw);
    if (data?.error || !data?.body) return null;
    const pp = data.body.pixpedia || {};
    const parent = String(pp.parentTag || '').trim();
    const abstract = String(pp.abstract || '');
    if (!parent || parent === w) return null;
    const esc = parent.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    if (new RegExp(`「${esc}」の.{0,8}(中国名|漢字表記|別名|英語名|正式名称|表記)`).test(abstract)) {
      return parent;
    }
  } catch { /* 联想挂了就走原流程，不阻塞搜图 */ }
  return null;
}

// ── HTTP 封装（纯 Node 实现，v1.1.2 起不再依赖 curl.exe）────────────
//
// 为什么从 curl.exe 换成 Node：
//   实测这台机器上 curl.exe+Schannel 不可靠——同一代理下，node(OpenSSL) 的
//   请求全部正常（搜索/详情/图片下载都 200），而 curl 时而
//   「schannel: AcquireCredentialsHandle failed」、时而 TLS 握手被 RST
//   （curl: (35) Recv failure: Connection was reset）。QQ Agent 本体走
//   Node/OpenSSL 不受影响，只有技能里的 curl 踩坑，所以网络层整体换成 Node：
//   http/https 代理走 CONNECT 隧道，socks5/socks5h 自己做 SOCKS5 握手
//   （socks5h 语义 = 域名交给代理远端解析），直连就是普通 TLS。
//   这样也顺带去掉了「依赖 curl.exe」和「旧版 curl TLS 兼容性」两条限制。
function parseProxy(proxy) {
  const s = String(proxy || '').trim();
  if (!s) return null;
  const m = /^(https?|socks5h?):\/\//i.exec(s);
  if (!m) return null;
  const scheme = m[1].toLowerCase();
  const rest = s.slice(m[0].length).replace(/\/+$/, '');
  const hp = /^([^:@/]+)(?::(\d+))?$/.exec(rest);
  if (!hp) return null;
  return { scheme, host: hp[1], port: Number(hp[2]) || (scheme === 'http' ? 80 : 1080) };
}

/** 建立到 targetHost:targetPort 的原始 TCP 隧道（http 代理 CONNECT / socks5 握手 / 直连） */
function openTunnel(targetHost, targetPort, proxy, timeoutMs) {
  return new Promise((resolve, reject) => {
    const p = parseProxy(proxy);
    const via = p && p.scheme !== 'direct' ? p : null;
    const sock = via
      ? net.connect({ host: via.host, port: via.port })
      : net.connect({ host: targetHost, port: targetPort });
    sock.setTimeout(timeoutMs);
    let settled = false;
    const ok = () => { if (!settled) { settled = true; sock.setTimeout(0); resolve(sock); } };
    const fail = (e) => {
      if (settled) return;
      settled = true;
      try { sock.destroy(); } catch { /* ignore */ }
      reject(new Error(e?.message ?? String(e)));
    };
    sock.once('error', fail);
    sock.once('timeout', () => fail(new Error(`连接${via ? '代理 ' + via.host + ':' + via.port : ' ' + targetHost} 超时（${timeoutMs}ms）`)));

    if (!via) { sock.once('connect', ok); return; }

    if (via.scheme === 'http' || via.scheme === 'https') {
      // HTTP 代理：CONNECT 建隧道（实测可行；https 代理此处仍以明文连代理口，仅支持本地 mixed 口）
      let buf = Buffer.alloc(0);
      sock.once('connect', () => {
        sock.write(`CONNECT ${targetHost}:${targetPort} HTTP/1.1\r\nHost: ${targetHost}:${targetPort}\r\nProxy-Connection: keep-alive\r\n\r\n`);
      });
      sock.on('data', (d) => {
        buf = Buffer.concat([buf, d]);
        const idx = buf.indexOf('\r\n\r\n');
        if (idx === -1) return;
        sock.removeAllListeners('data');
        const head = buf.slice(0, idx).toString('latin1');
        const rest = buf.slice(idx + 4);
        const code = Number(/^HTTP\/\S+\s+(\d+)/.exec(head)?.[1] ?? 0);
        if (code !== 200) { fail(new Error(`代理 CONNECT 失败：${head.split('\r\n')[0] || 'HTTP ' + code}`)); return; }
        if (rest.length) sock.unshift(rest);   // 极少见：代理提前发来的字节还给 TLS 层
        ok();
      });
      return;
    }

    // SOCKS5 / SOCKS5H：手写握手。socks5h 语义 = 域名直接交给代理解析（国内必须）
    const ATYP = { V4: 0x01, NAME: 0x03, V6: 0x04 };
    const isIp = net.isIPv4(targetHost);
    const stage = { greet: true };
    sock.once('connect', () => sock.write(Buffer.from([0x05, 0x01, 0x00])));  // 无认证
    sock.on('data', function onData(d) {
      if (stage.greet) {
        if (d.length < 2 || d[0] !== 0x05 || d[1] !== 0x00) { fail(new Error('SOCKS5 握手失败：代理不接受无认证方式')); return; }
        stage.greet = false;
        const name = Buffer.from(targetHost, 'utf8');
        const req = Buffer.alloc(6 + (isIp ? 4 : 1 + name.length));
        let off = 0;
        req[off++] = 0x05; req[off++] = 0x01; req[off++] = 0x00;
        if (isIp) { req[off++] = ATYP.V4; Buffer.from(targetHost.split('.').map(Number)).copy(req, off); off += 4; }
        else { req[off++] = ATYP.NAME; req[off++] = name.length; name.copy(req, off); off += name.length; }
        req.writeUInt16BE(targetPort, off);
        sock.write(req);
        return;
      }
      sock.removeListener('data', onData);
      if (d.length < 4 || d[0] !== 0x05 || d[1] !== 0x00) {
        const why = { 1: '一般性失败', 2: '不允许', 3: '网络不可达', 4: '主机不可达', 5: '连接被拒', 6: 'TTL 过期', 7: '不支持该命令', 8: '地址类型不支持' }[d[1]] ?? `应答码 ${d[1]}`;
        fail(new Error(`SOCKS5 连接失败：${why}`));
        return;
      }
      ok();
    });
  });
}

/**
 * HTTP GET：代理上 TLS，返回 { status, body: Buffer }。
 * binary=false 时另带 body 的 utf8 文本。重定向最多跟 3 跳（对应旧 curl 的 -L）。
 */
function httpGet(url, { proxy = '', referer = '', timeoutMs = 25000, binary = false, extraHeaders = {} } = {}, redirects = 0) {
  const u = new URL(url);
  const tlsPort = Number(u.port) || 443;
  const doRequest = () => openTunnel(u.hostname, tlsPort, proxy, Math.min(timeoutMs, 15000)).then((sock) =>
    new Promise((resolve, reject) => {
      const tlsSock = tls.connect({ socket: sock, servername: u.hostname, rejectUnauthorized: true }, () => {
        const headers = [
          `Host: ${u.hostname}`,
          `User-Agent: ${UA}`,
          `Referer: ${referer || PIXIV_REFERER}`,
          'X-Requested-With: XMLHttpRequest',
          ...(binary ? [] : ['Accept: application/json']),
          ...Object.entries(extraHeaders).map(([k, v]) => `${k}: ${v}`),
          'Connection: close'
        ];
        tlsSock.write(`GET ${u.pathname}${u.search} HTTP/1.1\r\n${headers.join('\r\n')}\r\n\r\n`);
      });
      tlsSock.setTimeout(timeoutMs);
      const chunks = [];
      let total = 0;
      let settled = false;
      const finish = (fn) => { if (!settled) { settled = true; tlsSock.destroy(); fn(); } };
      tlsSock.once('error', (e) => finish(() => reject(new Error(`TLS/请求失败：${e?.message ?? e}`))));
      tlsSock.once('timeout', () => finish(() => reject(new Error(`响应超时（${timeoutMs}ms）`))));
      tlsSock.on('data', (d) => { chunks.push(d); total += d.length; if (total > 64 * 1024 * 1024) finish(() => reject(new Error('响应超过 64MB，已中止'))); });
      tlsSock.once('close', () => {
        if (settled) return;
        settled = true;
        try {
          const raw = Buffer.concat(chunks);
          const idx = raw.indexOf('\r\n\r\n');
          if (idx === -1) return reject(new Error('响应缺少 HTTP 头（可能被中间设备重置）'));
          const head = raw.slice(0, idx).toString('latin1');
          const status = Number(/^HTTP\/\S+\s+(\d+)/.exec(head)?.[1] ?? 0);
          let body = raw.slice(idx + 4);
          if (/transfer-encoding:\s*chunked/i.test(head)) body = dechunk(body);
          const loc = (/^location:\s*(\S+)/im.exec(head)?.[1] || '').trim();
          if ([301, 302, 307, 308].includes(status) && loc && redirects < 3) {
            tlsSock.destroy();
            return resolve(httpGet(new URL(loc, url).href, { proxy, referer, timeoutMs, binary, extraHeaders }, redirects + 1));
          }
          tlsSock.destroy();
          resolve({ status, head, body: binary ? body : body.toString('utf8') });
        } catch (e) { reject(new Error(`解析响应失败：${e?.message ?? e}`)); }
      });
    })
  );
  return doRequest();
}

function dechunk(buf) {
  const out = [];
  let i = 0;
  while (i < buf.length) {
    const j = buf.indexOf('\r\n', i);
    if (j === -1) break;
    const size = parseInt(buf.slice(i, j).toString('latin1').split(';')[0], 16);
    if (!Number.isFinite(size) || size === 0) break;
    out.push(buf.slice(j + 2, j + 2 + size));
    i = j + 2 + size + 2;
  }
  return Buffer.concat(out);
}

/** 兼容旧调用的文本/二进制获取：成功返回文本或 Buffer，非 2xx 时抛错（错误里带状态码与片段） */
async function fetchViaNode(url, { proxy = '', referer = '', timeoutMs = 25000, binary = false } = {}) {
  const r = await httpGet(url, { proxy, referer, timeoutMs, binary });
  if (r.status < 200 || r.status >= 300) {
    const snip = binary ? `<二进制 ${r.body.length} 字节>` : String(r.body).slice(0, 120).replace(/\s+/g, ' ');
    throw new Error(`HTTP ${r.status}：${snip}`);
  }
  return r.body;
}

// ── 代理保活（移植自 char_img.py 的 _proxy_port_open / _ensure_proxy）──
//
// 注意：这套东西叫 v2rayN，但**核心是 sing-box** —— v2rayN 生成的
// binConfigs\config.json 是 sing-box 格式，所以原版启的是
// bin\sing_box\sing-box.exe run -c <config>，不是 xray。
// 配置里的入站是 mixed 类型监听 127.0.0.1:10808，socks5 和 http 共用这一个口。
let lastEnsureTs = 0;
let lastEnsureOk = null;
let ensureInFlight = null;

/** 代理地址里抽出可探测的 host:port（socks5h://127.0.0.1:10808 → 127.0.0.1:10808） */
function proxyHostPort(proxy) {
  const s = String(proxy || '').trim();
  if (!s) return null;
  const m = /^(?:[a-z0-9+.-]+:\/\/)?([^:/@]+):(\d+)/i.exec(s);
  if (!m) return null;
  return { host: m[1], port: Number(m[2]) };
}

function probeTcp(host, port, timeoutMs = 800) {
  return new Promise((resolve) => {
    const sock = net.connect({ host, port });
    let done = false;
    const finish = (ok) => {
      if (done) return;
      done = true;
      sock.destroy();
      resolve(ok);
    };
    sock.setTimeout(timeoutMs);
    sock.once('connect', () => finish(true));
    sock.once('timeout', () => finish(false));
    sock.once('error', () => finish(false));
  });
}

async function waitPort(host, port, totalMs) {
  const deadline = Date.now() + totalMs;
  while (Date.now() < deadline) {
    if (await probeTcp(host, port, 600)) return true;
    await new Promise((r) => setTimeout(r, 700));
  }
  return false;
}

/**
 * 确保代理端口可连。端口没开且开了 autoStart 时，后台静默拉起 sing-box。
 * 返回 { ok, started, reason }。
 *
 * 节流 60s + 单飞（in-flight）锁：群聊里连着几个人要图时，
 * 不能每个请求都去 spawn 一次核心 —— 第二次 spawn 会因端口占用直接失败。
 */
async function ensureProxy({ proxy, autoStart, coreDir }) {
  const hp = proxyHostPort(proxy);
  if (!hp) return { ok: false, started: false, reason: '代理地址解析不出来' };

  if (await probeTcp(hp.host, hp.port)) {
    lastEnsureOk = true;
    return { ok: true, started: false };
  }
  if (!autoStart) {
    return { ok: false, started: false, reason: `代理端口 ${hp.host}:${hp.port} 没在监听，且未开启自动拉起` };
  }
  if (ensureInFlight) return ensureInFlight;                 // 已有一次在跑，搭车
  if (Date.now() - lastEnsureTs < 60000 && lastEnsureOk === false) {
    return { ok: false, started: false, reason: '60 秒内已尝试过拉起代理且失败，先不重复试' };
  }
  lastEnsureTs = Date.now();

  ensureInFlight = (async () => {
    const dir = String(coreDir || '').trim();
    const exe = dir ? path.join(dir, 'bin', 'sing_box', 'sing-box.exe') : '';
    const conf = dir ? path.join(dir, 'binConfigs', 'config.json') : '';
    if (!dir || !fs.existsSync(exe) || !fs.existsSync(conf)) {
      lastEnsureOk = false;
      return { ok: false, started: false, reason: `找不到 sing-box 核心或配置（${dir || '未配置 proxyCoreDir'}）` };
    }
    try {
      const child = spawn(exe, ['run', '-c', conf], {
        cwd: path.dirname(exe),
        detached: true,          // 代理是基础设施，不跟着 QQ Agent 一起死
        stdio: 'ignore',         // 不弹窗、不占管道
        windowsHide: true
      });
      child.unref();
    } catch (e) {
      lastEnsureOk = false;
      return { ok: false, started: false, reason: `启动 sing-box 失败：${e?.message ?? e}` };
    }
    const up = await waitPort(hp.host, hp.port, 15000);
    lastEnsureOk = up;
    return up
      ? { ok: true, started: true }
      : { ok: false, started: true, reason: 'sing-box 已启动，但 15 秒内端口仍未就绪' };
  })();

  try { return await ensureInFlight; } finally { ensureInFlight = null; }
}

// ── Pixiv 工具函数（照抄原版语义）────────────────────────────────────
function pixivWorkId(url) {
  const m = /(\d{5,12})_p\d+_/.exec(String(url || ''));
  return m ? m[1] : null;
}

function imageHash(url, workId = null) {
  const key = workId ? `pixiv:${workId}` : String(url);
  return crypto.createHash('md5').update(key, 'utf8').digest('hex').slice(0, 8);
}

function normalizeExt(url) {
  const ext = path.extname(String(url).split('?')[0]).toLowerCase();
  return IMG_EXT.has(ext) ? ext : '.png';
}

/** 旧文件兜底：目录里已有同 hash 的文件就复用它（兼容原图库的命名） */
function findExistingFile(dir, hash, ext) {
  try {
    for (const f of fs.readdirSync(dir)) {
      if (f.endsWith(ext) && f.includes(`_${hash}${ext}`)) return path.join(dir, f);
    }
  } catch { /* 目录不存在 */ }
  return null;
}

/**
 * 取**一页**搜索结果（不含详情，所以此时还没有收藏数）。
 * 拆成"一页一取"是为了让调用方"够用就停"——每多一个候选就多一次详情请求。
 */
async function searchPage(query, page, opt) {
  const { proxy, timeoutMs, mode, type, skipMultiPage, apiBase } = opt;
  const kw = encodeURIComponent(query);
  // 【v1.1.1 修复根因】Pixiv 对「/ajax/search/illustrations + type=artwork」一律返回
  // 400「不正确的请求」（实测五种变体均如此），而旧代码写死 type=artwork，
  // 于是不管搜什么都 400。且 400 的响应体恰好是合法 JSON（{"error":true,"body":[]}），
  // JSON.parse 能成功、body.illust 取不到 → 静默变空数组 → 被报成「没搜到」。
  // 按设置的「作品类型」映射到实测可用的组合：
  //   artwork（只插画）→ illustrations 端点 + type=illust_and_ugoira（实测 200）
  //   all（含漫画）    → artworks 端点 + type=artwork（实测 200）
  const isAll = String(type).trim().toLowerCase() === 'all';
  const ep = isAll ? 'artworks' : 'illustrations';
  const typeParam = isAll ? 'artwork' : 'illust_and_ugoira';
  const url = `${apiBase}/ajax/search/${ep}/${kw}`
    + `?word=${kw}&order=date_d&mode=${mode}&p=${page}&s_mode=s_tag&type=${typeParam}&lang=zh`;
  // 【v1.1.1】失败不再吞成空数组：网络错误、非 JSON、Pixiv error JSON 都要带着真实原因抛出去，
  // 让上层给出可排查的错误信息，而不是伪装成「没搜到」。
  let raw;
  try { raw = await fetchViaNode(url, { proxy, timeoutMs }); }
  catch (e) { throw new Error(`请求 Pixiv 搜索接口失败：${e?.message ?? e}`); }
  let data;
  try { data = JSON.parse(raw); }
  catch { throw new Error(`Pixiv 搜索接口返回了非 JSON 内容（可能被拦截或限流），前 120 字：${String(raw).slice(0, 120)}`); }
  if (data?.error) throw new Error(`Pixiv 搜索接口报错：${data.message || JSON.stringify(data).slice(0, 120)}`);
  const body = data?.body || {};
  const items = body.illust?.data || body.illustManga?.data || [];
  const out = [];
  for (const it of items) {
    const id = String(it?.id ?? '');
    if (!id) continue;
    let u = it?.urls?.regular || it?.url || '';
    if (!u) continue;
    // 缩略图 -> master1200 大图
    u = u.replace('/c/250x250_80_a2/', '/').replace('_square1200.', '_master1200.');
    const pageCount = Number(it?.pageCount) || 1;
    if (skipMultiPage && pageCount > 1) continue;
    const tags = (Array.isArray(it?.tags) ? it.tags : [])
      .map((t) => (t && typeof t === 'object' ? t.tag : String(t || '')))
      .filter(Boolean);
    out.push({ id, url: u, bookmarks: 0, likes: 0, pageCount, tags });
  }
  return out;
}

/** 并发拉详情补收藏量/点赞量（原版用 6 线程，这里用 6 个协程等价实现） */
async function fetchDetails(cands, { proxy, timeoutMs, apiBase }) {
  let cursor = 0;
  const worker = async () => {
    while (cursor < cands.length) {
      const c = cands[cursor++];
      try {
        const d = JSON.parse(await fetchViaNode(`${apiBase}/ajax/illust/${c.id}`, { proxy, timeoutMs }));
        const b = d?.body || {};
        c.bookmarks = Number(b.bookmarkCount) || 0;
        c.likes = Number(b.likeCount) || 0;
        // 发图时要把这些一并带出去，所以在这一趟里取全（详情接口本来就返回了）
        c.author = String(b.userName || '').trim();
        c.authorId = String(b.userId || '').trim();
        c.title = String(b.title || '').trim();
        c.views = Number(b.viewCount) || 0;
        c.created = String(b.createDate || '').trim();
      } catch { /* 单张失败就保持 0，不拖垮整批 */ }
    }
  };
  await Promise.all(Array.from({ length: Math.min(6, cands.length) }, worker));
}

/** 按收藏+点赞加权不放回抽样（权重越大概率越高） */
function weightedSelect(items, n) {
  const pool = [...items];
  const picked = [];
  while (picked.length < n && pool.length) {
    const weights = pool.map((it) => Math.max(Number(it.bookmarks) || 0, 0) + Math.max(Number(it.likes) || 0, 0) + 1);
    const total = weights.reduce((a, b) => a + b, 0);
    let r = Math.random() * total;
    let chosen = null;
    for (let i = 0; i < pool.length; i++) {
      r -= weights[i];
      if (r <= 0) { chosen = pool.splice(i, 1)[0]; break; }
    }
    picked.push(chosen || pool.pop());
  }
  return picked;
}

async function downloadImage(url, destDir, { proxy, timeoutMs, name, workId, pageCount = 1 }) {
  fs.mkdirSync(destDir, { recursive: true });
  let realUrl = url;
  if (pageCount > 1) {
    const idx = Math.floor(Math.random() * pageCount);
    realUrl = url.replace(/_p\d+_/, `_p${idx}_`);
  }
  const ext = normalizeExt(realUrl);
  const hash = imageHash(realUrl, workId);

  const existing = findExistingFile(destDir, hash, ext);
  if (existing) return { file: existing, reused: true };

  const safe = String(name || 'img').replace(/[^\w\u4e00-\u9fff-]/g, '_').slice(0, 30) || 'img';
  const dest = path.join(destDir, `${Date.now()}_${safe}_${hash}${ext}`);
  const buf = await fetchViaNode(realUrl, { proxy, referer: PIXIV_REFERER, timeoutMs, binary: true });
  if (!buf || buf.length < 200) return null;   // 太小的基本是错误页
  fs.writeFileSync(dest, buf);
  return { file: dest, reused: false };
}

// ── 发图时附带的作品信息 ─────────────────────────────────────────────
/** 把万位数压成「1.2万」，聊天里比 12345 好读 */
function compactNum(n) {
  const v = Number(n) || 0;
  if (v < 10000) return String(v);
  return `${(v / 10000).toFixed(v >= 100000 ? 0 : 1).replace(/\.0$/, '')}万`;
}

function formatInfo(it) {
  const title = String(it.title || '').replace(/\s+/g, ' ').trim().slice(0, 40);
  const head = title ? `🎨 ${title}` : `🎨 pixiv #${it.id}`;
  const bits = [];
  if (it.author) bits.push(`👤 ${it.author}`);
  if (it.bookmarks) bits.push(`❤️ ${compactNum(it.bookmarks)}`);
  if (it.likes) bits.push(`⭐ ${compactNum(it.likes)}`);
  if (it.views) bits.push(`👁 ${compactNum(it.views)}`);
  bits.push(`#${it.id}`);
  return `${head}\n${bits.join(' ｜ ')}`;
}

// ── 工具注册 ────────────────────────────────────────────────────────
export function setup(api) {
  cfg = api.config;
  log = api.log;
  const d = loadLedger();
  const dict = loadTagDict();
  api.log(`Pixiv 技能已注册｜索引 ${Object.keys(d).length} 个 PID｜tag 词典 ${Object.keys(dict).length} 条`);

  api.registerTool({
    id: 'pixiv_image_tag',
    name: 'Pixiv 来张图（标签检索）',
    description:
      '从 Pixiv 按角色搜插画并发到当前会话：按「N users入り」热度档检索并按真实收藏数复核，当前档没有没发过的新图时自动下调收藏档（每次 100，最低 100users入り，最后普通检索兜底），档位按词条记住下次沿用；发过的作品绝不重发。' +
      '默认优先发**最新**的达标作品；用户明确要「高收藏/热门/经典」的图时传 hot=true，改按收藏+点赞加权挑。' +
      '当群友说「来张 XX」「来一张 XX」「找张 XX」时调用。' +
      'character 填角色名；tag 填该角色**本人**的日文标签（例如 古明地恋→古明地こいし）——不要拿游戏/作品名当 tag，那会搜出全作品的角色混图；不确定就别填，工具会用 Pixiv 联想把中文角色名解析成日文标签。' +
      '要壁纸/头像等特定主题时把筛选词翻成日文填进 extraTags（如 壁紙）；作品/游戏名适合填 extraTags 区分同名角色。',
    category: 'media',
    icon: '🖼️',
    parameters: {
      type: 'object',
      properties: {
        character: { type: 'string', description: '角色名，例如「古明地恋」「博丽灵梦」。' },
        tag: {
          type: 'string',
          description: '该角色**本人**在 Pixiv 的日文标签（可选但强烈建议），例如 古明地こいし。不要填游戏/作品名——那会搜出该作品所有角色的混图；不确定角色标签时留空，工具会用 Pixiv 联想自动解析。'
        },
        extraTags: {
          type: 'string',
          description: '附加筛选标签（可选，空格分隔多个，与角色标签 AND 组合）。想要壁纸/头像/表情包等特定主题时填，中文词要先翻成日文：壁纸→壁紙、头像→アイコン、表情包→リアクション画像。作品/游戏名也可填这里区分同名角色。'
        },
        count: { type: 'number', description: '发几张，1~3，默认 1。' },
        hot: {
          type: 'boolean',
          description: '用户明确要「高收藏/热门/经典」的图时传 true：按收藏+点赞加权挑。默认（只说"来张 XX"）不传：优先发最新达标的图。'
        }
      },
      required: ['character']
    },
    async execute(ctx, args) {
      const c = cfg() || {};
      const apiBase = String(c.apiBase || 'https://www.pixiv.net').trim().replace(/\/+$/, '');
      const proxy = String(c.proxy || '').trim();
      // 留空 = 存到程序数据目录下，随数据一起备份，开箱即用
      const imageDir = String(c.imageDir || '').trim() || path.join(dataDir(), 'images');
      const minBm = Math.max(0, Number(c.minBookmarks) || 0);
      // 上限从 3 放宽到 10：以前设 5 会被静默夹成 3，翻页等于没生效
      const pages = Math.min(10, Math.max(1, Number(c.candidatePages) || 3));
      const skipMultiPage = c.skipMultiPage !== false;
      const mode = String(c.mode || 'safe').trim();
      const type = String(c.type || 'artwork').trim();
      const timeoutMs = Math.min(60000, Math.max(5000, Number(c.timeoutMs) || 25000));

      const character = String(args?.character ?? '').trim();
      if (!character) return { content: '缺少 character：请告诉我要哪个角色的图。', isError: true };

      const count = Math.min(3, Math.max(1, Number(args?.count) || 1));
      // v1.1.4：默认优先最新达标作品；用户明确要高收藏/热门时才按收藏加权随机
      const hot = args?.hot === true;

      // tag 解析（v1.1.7 起四段式）：模型给的日文标签 > 词典 > Pixiv 联想解析 > 原名硬搜
      // extraTags：附加筛选标签（如 壁紙/アイコン），与角色标签 AND 组合检索（v1.1.5）
      const dict = loadTagDict();
      const given = String(args?.tag ?? '').trim();
      const extra = String(args?.extraTags ?? '').trim().replace(/\s+/g, ' ');

      // 代理可能没开：先探测，必要时按设置把 sing-box 拉起来（标签联想解析也要走代理，故提到解析前）
      const pre = await ensureProxy({
        proxy,
        autoStart: c.autoStartProxy === true,
        coreDir: String(c.proxyCoreDir || '').trim()
      });
      if (!pre.ok) {
        return {
          content: `拿不到图：${pre.reason}。请在技能设置里把代理开起来，或打开「代理没开时自动拉起」。`,
          isError: true
        };
      }

      const t0 = Date.now();
      let jaTag = given || dict[character] || '';
      if (!jaTag) {
        // 模型没给标签、词典也没有：用 Pixiv 联想接口把中文角色名解析成日文标签，
        // 比让模型去外部搜索查（常查到游戏名，拿来当 tag 会搜出全作品角色混图）可靠得多
        const sug = await resolveTagViaSuggest(character, { proxy, timeoutMs, apiBase });
        if (sug) {
          jaTag = sug;
          rememberTag(character, sug);   // 学进词典，下次零成本
          log(`标签联想：${character} → ${sug}`);
        }
      }
      if (!jaTag) jaTag = character;     // 联想没命中：退回原名硬搜（与旧行为一致）
      const baseQuery = [jaTag, extra].filter(Boolean).join(' ');
      const tagLabel = [jaTag, extra].filter(Boolean).join('＋');
      // 多词组合（含空格）只作本次检索，不写入词典——避免把「初音ミク 壁紙」这种组合词存成角色映射
      if (given && !/\s/.test(given)) rememberTag(character, given);
      // ── 检索策略（v1.1.3：热度阶梯下调 + 按词条记忆，绝不复用已发图）──
      // 背景知识（都是实测结论）：
      //   · 搜索接口在未登录时只给"最新优先"，order=popular_d / blt 会被直接忽略
      //     （实测「初音ミク」翻 5 页 142 个候选，最高 444），所以高收藏作品要靠
      //     上传者自己打的「N users入り」约定标签去找，且最终仍按详情里的
      //     真实收藏数复核（约定标签只是"更容易捞到"，不保证 100%）。
      // v1.1.3 规则（替代旧的"复用已存图"降级——观感太差）：
      //   ① 发过的作品（PID 索引）在搜索阶段就被剔除，任何情况都不会再发第二遍；
      //   ② 当前档位凑不齐没发过的新图，就把热度档下调 100 收藏
      //      （1000users入り → 900users入り → …，最低 100users入り，最后普通检索兜底）；
      //   ③ 每个词条实际用到的档位记进 tag-floor.json，下次直接从记住的档位开始，
      //      不再每次都从设定值重新走一遍；同时每次仍会先复查一次最高档（设定值），
      //      有新热门图就顺带把档位升回去。
      const FLOOR_STEP = 100;
      const FLOOR_MIN = 100;
      const strict = c.strictMinBookmarks === true;
      const plan = [];
      let startFloor = minBm;
      let effMin = minBm;
      if (minBm > 0 && c.usePopularTag !== false) {
        effMin = strict ? minBm : Math.min(minBm, FLOOR_MIN);
        startFloor = Math.min(minBm, Math.max(effMin, getFloor(tagLabel, minBm)));
        if (startFloor < minBm) plan.push({ floor: minBm, query: `${baseQuery} ${minBm}users入り` });   // 顶部复查：有新热门图就把档位升回去
        for (let L = startFloor; ; L -= FLOOR_STEP) {
          plan.push({ floor: L, query: `${baseQuery} ${L}users入り` });
          if (L - FLOOR_STEP < effMin) break;
        }
        plan.push({ floor: effMin, query: baseQuery });   // 兜底：不用约定标签的普通检索（搜最新）
        log(`热度阶梯：词条「${tagLabel}」从 ${startFloor} 档开始（最低 ${effMin}${strict ? '，严格门槛不下调' : ''}，共 ${plan.length} 档）`);
      } else {
        // 没设门槛或关了约定标签检索：普通检索一次，按 minBm 复核
        plan.push({ floor: minBm, query: baseQuery });
      }

      const seenIds = new Set();
      const cands = [];            // 本轮搜到且没发过的新候选（含详情，跨档共享，不重复拉详情）
      const DETAIL_BUDGET = 240;   // 详情请求总量上限：防止一路深降档时请求数失控
      let detailBudget = DETAIL_BUDGET;
      let pickedPool = [];         // 最终可发的新图（都达到 usedFloor 档）
      let usedFloor = null;        // 实际发图用到的档位
      let searchError = null;
      try {
        for (const rung of plan) {
          if (detailBudget <= 0) break;
          // 先看已攒的候选在当前档位够不够——够就不必再搜这一档
          let okNow = rung.floor > 0 ? cands.filter((x) => (Number(x.bookmarks) || 0) >= rung.floor) : cands.slice();
          if (okNow.length >= count) { pickedPool = okNow; usedFloor = rung.floor; break; }
          for (let page = 1; page <= pages; page++) {
            const got = (await searchPage(rung.query, page, { proxy, timeoutMs, mode, type, skipMultiPage, apiBase }))
              .filter((x) => !seenIds.has(x.id) && seenIds.add(x.id));
            if (!got.length) break;
            // 只给"没发过"的拉详情；发过的不发第二遍，也没必要再查收藏数
            const fresh = got.filter((x) => !hasPid(x.id));
            const toFetch = fresh.slice(0, detailBudget);
            detailBudget -= toFetch.length;
            await fetchDetails(toFetch, { proxy, timeoutMs, apiBase });
            cands.push(...toFetch);
            okNow = rung.floor > 0 ? cands.filter((x) => (Number(x.bookmarks) || 0) >= rung.floor) : cands.slice();
            if (okNow.length >= count) break;   // 这一档凑够了，收工
            if (detailBudget <= 0) break;
          }
          if (okNow.length >= count) { pickedPool = okNow; usedFloor = rung.floor; break; }
        }
        // 没有任何一档凑够 count：退而求其次，用最低档下能给出的全部新图（跨档累积）
        if (usedFloor == null && cands.length) {
          const lastRung = plan[plan.length - 1];
          pickedPool = lastRung.floor > 0 ? cands.filter((x) => (Number(x.bookmarks) || 0) >= lastRung.floor) : cands.slice();
          if (pickedPool.length) usedFloor = lastRung.floor;
        }
      } catch (e) {
        searchError = e;
      }
      // 【v1.1.1】searchPage 会把真实错误抛出来，这里分三种情况：
      //   ① 已经拿到部分达标候选 → 翻页中途的偶发失败不让整次报废，用现有结果继续；
      //   ② 一页没拿到 + 看着像网络/代理问题 → 给出代理指引；
      //   ③ 其余（含 Pixiv 接口报错）→ 原样带出真实原因。
      if (searchError) {
        const msg = String(searchError?.message || searchError);
        if (pickedPool.length > 0) {
          log(`翻页中途出错（已拿 ${pickedPool.length} 个达标候选，用现有结果继续）：${msg}`);
        } else if (/could not resolve|Failed to connect|Connection refused|timed out|ETIMEDOUT|超时|CONNECT|SOCKS|TLS|代理|curl/i.test(msg)) {
          return {
            content: '连不上 Pixiv（' + msg + '）。这个功能必须走代理，请确认代理已启动，'
              + '当前设置是「' + (proxy || '直连') + '」。' + RELAY_NOTE_ERR,
            isError: true
          };
        } else {
          return { content: '搜索 Pixiv 失败：' + msg + RELAY_NOTE_ERR, isError: true };
        }
      }
      if (!pickedPool.length) {
        // 一张可发的新图都没有。区分"压根没搜到"和"搜到了但都发过/都没达标"
        if (!cands.length && seenIds.size === 0) {
          return { content: `没搜到「${tagLabel}」的图。可以换个日文标签再试。${RELAY_NOTE_ERR}`, isError: true };
        }
        const saw = cands.length
          ? `本轮共看 ${seenIds.size} 个作品，新候选 ${cands.length} 个（收藏数都没够到能发的档）`
          : `搜到的 ${seenIds.size} 个作品之前全发过了`;
        const base = minBm > 0
          ? (strict
            ? `「${character}（${tagLabel}）」在 ${minBm} 收藏档没找到没发过的新图（严格门槛：不下调）。${saw}。`
            : `「${character}（${tagLabel}）」从 ${startFloor} 档一路降到 ${effMin} 收藏，还是没有没发过的新图。${saw}。`)
          : `「${character}（${tagLabel}）」搜到的新图都发过了。${saw}。`;
        return {
          content: base + '按设置不会重复发已发过的图；等这个标签有新图再来，或把「最低收藏数」调低。' + RELAY_NOTE,
          isError: true
        };
      }

      // v1.1.4 挑选策略（都只从"没发过"的达标新图里挑）：
      //   默认     → 按投稿时间从新到旧排，取最新的 count 张（同刻按收藏高的优先）；
      //   hot=true → 按收藏+点赞加权不放回随机，偏向高收藏（旧行为）。
      // 时间用详情接口的 createDate，候选跨档共享也不影响排序。
      const picked = hot
        ? weightedSelect(pickedPool, count)
        : [...pickedPool]
            .sort((a, b) => {
              const ta = Date.parse(a.created || '') || 0;
              const tb = Date.parse(b.created || '') || 0;
              return (tb - ta) || ((Number(b.bookmarks) || 0) - (Number(a.bookmarks) || 0));
            })
            .slice(0, count);

      const folder = character.replace(/[^\w\u4e00-\u9fff-]/g, '_').slice(0, 24) || 'misc';
      const destDir = path.join(imageDir, folder);
      const sent = [];
      const failed = [];

      const showInfo = c.showInfo !== false;
      for (const it of picked) {
        try {
          const got = await downloadImage(it.url, destDir, {
            proxy, timeoutMs, name: folder, workId: it.id, pageCount: it.pageCount
          });
          if (!got) {
            log('作品 %s 下载异常：HTTP 2xx 但内容过小，疑似错误页', it.id);
            failed.push(it.id); continue;
          }
          await ctx.sender.sendImage(ctx.chatKey, { file: got.file }, { note: `Pixiv ${it.id}` });
          // 作品信息紧跟图片单独发一条：图片气泡里塞不下文字，
          // 而模型的文本输出不会进 QQ，所以必须由工具自己发。
          if (showInfo) {
            try {
              await ctx.sender.sendTextBatch(ctx.chatKey, [formatInfo(it)]);
            } catch { /* 信息发失败不该把"图已经发出去了"变成失败 */ }
          }
          sent.push({ pid: it.id, file: got.file, bm: it.bookmarks, author: it.author });
          recordPid(it.id, {
            file: got.file, folder, tags: it.tags.slice(0, 8), sent: true,
            author: it.author, title: it.title, bookmarks: it.bookmarks, likes: it.likes
          });
        } catch (e) {
          // 【v1.1.2】下载失败不再无声：至少要留一条日志，否则"全部失败"没法排查
          log('作品 %s 下载失败：%s', it.id, String(e?.message ?? e).slice(0, 300));
          failed.push(it.id);
        }
      }

      if (!sent.length) {
        return {
          content: `找到 ${pickedPool.length} 个达标新作品，但都没能下载成功（可能是代理不稳）。稍后再试。${RELAY_NOTE_ERR}`,
          isError: true
        };
      }

      // 实际发出去图，才把词条的档位记下来（失败不记，避免把网络抖动当成"没图"）
      if (usedFloor != null && minBm > 0 && c.usePopularTag !== false) setFloor(tagLabel, usedFloor);

      const list = sent.map((s) => `PID ${s.pid}${s.bm ? `（收藏 ${s.bm}）` : ''}`).join('；');
      const ladderNote = (usedFloor != null && minBm > 0 && c.usePopularTag !== false)
        ? `热度档 ${usedFloor}${usedFloor < startFloor ? `（已从 ${startFloor} 下调）` : ''}`
        : '';
      return {
        content: `已发送 ${sent.length} 张「${character}」的图（标签 ${tagLabel}`
          + (ladderNote ? `，${ladderNote}` : '')
          + `，耗时 ${Math.round((Date.now() - t0) / 1000)}s）：${list}。`
          + (sent.length < count ? `当前档位下暂时只有这 ${sent.length} 张没发过的新图。` : '')
          + (failed.length ? `另有 ${failed.length} 张下载失败。` : '')
          + '图已经发出去了。' + RELAY_NOTE
          + '短话不要复述 PID 或标签；如果发生了降档，可以自然带一句"这个角色新图不多，先挑了张收藏稍低的"，也可以不提。'
      };
    }
  });
}

export function available() {
  return true;
}
