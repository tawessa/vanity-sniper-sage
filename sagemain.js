// published by tawessa - /v6
process.env.UV_THREADPOOL_SIZE = "10";
const { Worker, isMainThread, parentPort, workerData } = require('node:worker_threads');
const tls = require('node:tls');
const net = require('net');
const fs = require('fs');
const crypto = require('crypto');

const TOKEN = 'token'; // token
const GUILD = 'sw'; // guild
const REQ = 1; // request
const USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/132.0.0.0 Safari/537.36';
const SP = 'eyJvcyI6IldpbmRvd3MiLCJicm93c2VyIjoiQ2hyb21lIiwiZGV2aWNlIjoiIiwic3lzdGVtX2xvY2FsZSI6ImVuLVVTIiwiYnJvd3Nlcl91c2VyX2FnZW50IjoiTW96aWxsYS81LjAgKFdpbmRvd3MiLCJvc192ZXJzaW9uIjoiIiwicmVmZXJyZXIiOiIiLCJyZWZlcnJpbmdfZG9tYWluIjoiIiwicmVsZWFzZV9jaGFubmVsIjoic3RhYmxlIiwiY2xpZW50X2J1aWxkX251bWJlciI6MzQ1Njc4fQ==';

const IDENTIFY = JSON.stringify({
    op: 2,
    d: {
        token: TOKEN,
        intents: 1,
        properties: { os: 'Windows', browser: 'Chrome', device: '' }
    }
});
const IDENTIFY_BUF = Buffer.from(IDENTIFY);

const DISCORD_IPS = [
    '162.159.137.232',
    '162.159.135.232',
    '162.159.128.233',
    '162.159.136.232',
    '162.159.138.232'
];

const SAB_SIZE = 7 * 1024 * 1024;
const sabGlobal = new SharedArrayBuffer(SAB_SIZE);
const sabState = new SharedArrayBuffer(16);
const stateInt32 = new Int32Array(sabState);
const sharedPayloadBuffer = Buffer.from(sabGlobal);

const FRAGMENT_POOL_INIT = 256 * 1024;
const PREWARM_INTERVAL = 45000;

const STATIC_PATCH = Buffer.from(`PATCH /api/v9/guilds/${GUILD}/vanity-url HTTP/1.1\r\n`);
const STATIC_HOST = Buffer.from(`Host: canary.discord.com\r\n`);
const STATIC_AUTH = Buffer.from(`Authorization: ${TOKEN}\r\n`);
const STATIC_CONTENT_TYPE = Buffer.from(`Content-Type: application/json\r\n`);
const STATIC_USER_AGENT = Buffer.from(`User-Agent: ${USER_AGENT}\r\n`);
const STATIC_SP = Buffer.from(`x-super-properties: ${SP}\r\n`);
const STATIC_CONNECTION = Buffer.from(`Connection: keep-alive\r\n\r\n`);
const STATIC_BODY_START = Buffer.from(`{"code":"`);
const STATIC_BODY_END = Buffer.from(`"}`);

const GUILD_UPDATE = Buffer.from('"GUILD_UPDATE"');

function ParserState() {
    this.stage = 0;
    this.opcode = 0;
    this.isMasked = 0;
    this.maskOffset = 0;
    this.payloadLen = 0;
    this.extendedLenBytes = 0;
    this.extendedLenRead = 0;
    this.payloadOffset = 0;
    this.fragmentedOpcode = 0;
    this.maskKey = Buffer.allocUnsafe(4);
    this.extendedLenBuf = Buffer.allocUnsafe(8);
}

function CacheEntry(code, payload, bufferV) {
    this.c = code;
    this.p = payload;
    this.v = Buffer.from(bufferV);
    this.timestamp = Date.now();
}

if (isMainThread) {
    try {
        if (process.platform === "win32") {
            require("child_process").exec(`powershell -Command "[System.Diagnostics.Process]::GetCurrentProcess().PriorityClass = [System.Diagnostics.ProcessPriorityClass]::RealTime"`, () => {});
        } else if (typeof process.setPriority === "function") {
            process.setPriority(process.pid, -20);
        }
    } catch (e) {}

    let mfa = '';
    try { mfa = fs.readFileSync('mfa.txt', 'utf8').trim(); } catch (e) {}

    fs.watch('mfa.txt', (eventType) => {
        if (eventType === 'change') {
            try {
                mfa = fs.readFileSync('mfa.txt', 'utf8').trim();
                for (const id in cache) {
                    const entry = cache[id];
                    if (entry) entry.p = buildPayload(entry.c);
                }
            } catch (e) {}
        }
    });

    const cache = Object.create(null);
    const socksArray = new Array(REQ).fill(null);
    let socksCount = 0;
    let primarySock = null;
    let sniped = false;

    const buildPayload = (code) => {
        const codeBuf = Buffer.from(code);
        const contentLengthBuf = Buffer.from(`Content-Length: ${codeBuf.length + 11}\r\n`);
        let mfaBuf = null;
        if (mfa) mfaBuf = Buffer.from(`x-discord-mfa-authorization: ${mfa}\r\n`);
        const parts = [
            STATIC_PATCH, STATIC_HOST, STATIC_AUTH,
            ...(mfaBuf ? [mfaBuf] : []),
            contentLengthBuf, STATIC_CONTENT_TYPE, STATIC_USER_AGENT,
            STATIC_SP, STATIC_CONNECTION, STATIC_BODY_START, codeBuf, STATIC_BODY_END
        ];
        return Buffer.concat(parts);
    };

    const sharedCtx = tls.createSecureContext({
        minVersion: 'TLSv1.3',
        maxVersion: 'TLSv1.3',
        ciphers: 'TLS_AES_128_GCM_SHA256:TLS_CHACHA20_POLY1305_SHA256'
    });

    let sniperSessionCache = null;
    let sniperSessionTime = 0;
    const SESSION_TTL = 7200000;
    let currentIPIndex = 0;

    function getAvailableIP() {
        const ip = DISCORD_IPS[currentIPIndex];
        currentIPIndex = (currentIPIndex + 1) % DISCORD_IPS.length;
        return ip;
    }

    function getBestSock() {
        let best = null;
        let bestPending = Infinity;
        for (let i = 0; i < REQ; i++) {
            const s = socksArray[i];
            if (s && !s.destroyed && s.writable) {
                const pending = s.writableLength;
                if (pending < bestPending) {
                    bestPending = pending;
                    best = s;
                }
            }
        }
        return best;
    }

    function rebuildActiveSocks() {
        let count = 0;
        let newPrimary = null;
        let bestPending = Infinity;
        for (let i = 0; i < REQ; i++) {
            const s = socksArray[i];
            if (s && !s.destroyed && s.writable) {
                count++;
                const pending = s.writableLength;
                if (pending < bestPending) {
                    bestPending = pending;
                    newPrimary = s;
                }
            }
        }
        socksCount = count;
        primarySock = newPrimary;
    }

    function baglan(index) {
        const idx = index;
        if (socksArray[idx]) {
            try { socksArray[idx].destroy(); } catch (e) {}
            socksArray[idx] = null;
        }
        const targetIP = DISCORD_IPS[idx % DISCORD_IPS.length];
        const tcp = net.connect({
            host: targetIP,
            port: 443,
            keepAlive: true,
            noDelay: true,
            sendBufferSize: 1024 * 1024,
            receiveBufferSize: 1024 * 1024
        });
        tcp.setNoDelay(true);
        tcp.setKeepAlive(true, 0);

        const tlsSock = tls.connect({
            socket: tcp,
            servername: 'canary.discord.com',
            rejectUnauthorized: false,
            secureContext: sharedCtx,
            session: (sniperSessionCache && (Date.now() - sniperSessionTime) < SESSION_TTL) ? sniperSessionCache : null,
            noDelay: true,
            checkServerIdentity: () => {}
        });
        tlsSock.setNoDelay(true);

        tlsSock.on('secureConnect', () => {
            socksArray[idx] = tlsSock;
            tlsSock.resume();
            rebuildActiveSocks();
        });
        tlsSock.on('session', (ticket) => {
            if (ticket && ticket.length > 0) {
                sniperSessionCache = ticket;
                sniperSessionTime = Date.now();
            }
        });

        const cleanup = () => {
            if (socksArray[idx] === tlsSock) socksArray[idx] = null;
            rebuildActiveSocks();
            setTimeout(() => baglan(idx), 250);
        };
        tlsSock.on('close', cleanup);
        tlsSock.on('error', cleanup);
        tcp.on('error', cleanup);
    }

    const OP10 = Buffer.from('"op":10');
    const READY = Buffer.from('"t":"READY"');
    const OP7 = Buffer.from('"op":7');
    const ID_STR = Buffer.from('"id":"');

    function parseOP10(r) {
        try {
            const p = JSON.parse(r.toString());
            if (p.op === 10) {
                const interval = Math.max(p.d.heartbeat_interval, 1000);
                gwWorker.postMessage({ type: 'HEARTBEAT_INTERVAL', interval });
            } else {
                gwWorker.postMessage({ type: 'TERMINATE' });
            }
        } catch (e) {
            gwWorker.postMessage({ type: 'TERMINATE' });
        }
    }

    function parseREADY(r) {
        try {
            const startJson = r.indexOf(123);
            if (startJson === -1) return;
            const readyData = JSON.parse(r.toString('utf8', startJson));
            const user = readyData.d?.user;
            const guilds = readyData.d?.guilds || [];

            // LOG: READY
            if (user) {
                const vanityCount = guilds.filter(g => g.vanity_url_code && g.premium_tier === 3).length;
                console.log(`tarō ${vanityCount} guild`);
            }

            const newCache = Object.create(null);
            for (let i = 0; i < guilds.length; i++) {
                const g = guilds[i];
                if (g.vanity_url_code && g.premium_tier === 3) {
                    const existing = cache[g.id];
                    if (existing && existing.c === g.vanity_url_code) {
                        newCache[g.id] = existing;
                    } else {
                        newCache[g.id] = new CacheEntry(
                            g.vanity_url_code,
                            buildPayload(g.vanity_url_code),
                            `"vanity_url_code":"${g.vanity_url_code}"`
                        );
                    }
                }
            }
            for (const id in cache) if (!newCache[id]) delete cache[id];
            for (const id in newCache) if (!cache[id]) cache[id] = newCache[id];
        } catch (e) {}
    }

    function handleSnipeFastLane(r) {
        if (sniped) return;

        const updateIdx = r.indexOf(GUILD_UPDATE);
        if (updateIdx === -1) return;

        const idx = r.indexOf(ID_STR, updateIdx + 14);
        if (idx === -1) return;
        const startIdx = idx + 6;
        const end = r.indexOf(34, startIdx);
        if (end === -1) return;

        const guildId = r.toString('utf8', startIdx, end);
        const e = cache[guildId];
        if (!e || !e.p) return;

        if (r.indexOf(e.v, end) !== -1) return;

        // LOG: UPDATE alındı
        console.log(`tarō ${e.c}`);

        sniped = true;
        const payload = e.p;

        const best = getBestSock();
        if (best) {
            try {
                best.cork();
                best.write(payload);
                best.write(payload);
                best.uncork();
            } catch {}
            best.once('data', (res) => {
                try {
                    const raw = res.toString('utf8');
                    // HTTP status satırını bul
                    const statusMatch = raw.match(/HTTP\/1\.\d (\d{3})/);
                    const status = statusMatch ? parseInt(statusMatch[1]) : 0;
                    // JSON body'yi bul
                    const bodyStart = raw.indexOf('\r\n\r\n');
                    const body = bodyStart !== -1 ? raw.slice(bodyStart + 4).trim() : '';
                    let parsed = null;
                    try { parsed = JSON.parse(body); } catch {}

                    // LOG: CLAIM sonucu
                    if (status === 200) {
                        const code = parsed?.code ?? '?';
                        const uses = parsed?.uses ?? '?';
                        console.log(`200 tarō`);
                    } else {
                        const msg = parsed?.message ?? body.slice(0, 80);
                        const retry = parsed?.retry_after ? ` | retry: ${parsed.retry_after}ms` : '';
                        console.log(`${status} | ${msg}${retry}`);
                    }
                } catch (err) {}
            });
        }

        for (let i = 0; i < REQ; i++) {
            const s = socksArray[i];
            if (s && s !== best && !s.destroyed && s.writable) {
                try {
                    s.cork();
                    s.write(payload);
                    s.uncork();
                } catch {}
            }
        }
    }

    function handleControlMessage(r) {
        if (r.indexOf(OP10) !== -1) { parseOP10(r); return; }
        if (r.indexOf(READY) !== -1) { parseREADY(r); return; }
        if (r.indexOf(OP7) !== -1) { gwWorker.postMessage({ type: 'TERMINATE' }); }
    }

    for (let i = 0; i < REQ; i++) baglan(i);

    const gwWorker = new Worker(__filename, {
        workerData: { TOKEN, USER_AGENT, DISCORD_IPS, sabGlobal, sabState, IDENTIFY_BUF }
    });

    gwWorker.on('message', (msg) => {
        if (msg === 2) {
            const size = Atomics.load(stateInt32, 0);
            handleSnipeFastLane(sharedPayloadBuffer.subarray(0, size));
            Atomics.store(stateInt32, 1, 0);
        } else if (msg === 1) {
            const size = Atomics.load(stateInt32, 0);
            handleControlMessage(sharedPayloadBuffer.subarray(0, size));
            Atomics.store(stateInt32, 1, 0);
        } else if (msg.type === 'HEARTBEAT_INTERVAL') {
            gwWorker.postMessage({ type: 'HEARTBEAT_INTERVAL', interval: msg.interval });
        }
    });

    setInterval(rebuildActiveSocks, 5000);

    function scheduleMinuteCheck() {
        const now = new Date();
        const next = new Date(now);
        next.setMinutes(28, 0, 0);
        if (next <= now) next.setHours(next.getHours() + 1);
        const delay = Math.max(next - now, 1000);
        setTimeout(() => {
            for (let i = 0; i < REQ; i++) baglan(i);
            scheduleMinuteCheck();
        }, delay);
    }
    scheduleMinuteCheck();

} else {
    const { TOKEN, USER_AGENT, DISCORD_IPS, sabGlobal, sabState, IDENTIFY_BUF } = workerData;
    const workerStateInt32 = new Int32Array(sabState);
    const workerPayloadBuffer = Buffer.from(sabGlobal);

    let gatewaySessionCache = null;
    let gatewaySessionTime = 0;
    const SESSION_TTL = 7200000;
    let activeTlsSocket = null;
    let hbInterval = null;
    let prewarmInterval = null;

    const PING_BUF = Buffer.from('{"op":1,"d":null}');

    const sharedGwCtx = tls.createSecureContext({
        minVersion: 'TLSv1.3',
        maxVersion: 'TLSv1.3'
    });

    const handshakeBuf = Buffer.allocUnsafe(4096);

    function sendWsFrame(socket, rawBuffer, opcodeNumber) {
        const op = opcodeNumber & 0x0F;
        const len = rawBuffer.length;
        const maskKey = Buffer.allocUnsafe(4);
        crypto.randomFillSync(maskKey);

        let headerOffset, frameSize;
        if (len < 126) { headerOffset = 2; frameSize = len + 6; }
        else if (len < 65536) { headerOffset = 4; frameSize = len + 8; }
        else { headerOffset = 10; frameSize = len + 14; }

        const frameBuffer = Buffer.allocUnsafe(frameSize);
        frameBuffer[0] = 0x80 | op;

        if (len < 126) {
            frameBuffer[1] = 0x80 | len;
        } else if (len < 65536) {
            frameBuffer[1] = 0x80 | 126;
            frameBuffer.writeUInt16BE(len, 2);
        } else {
            frameBuffer[1] = 0x80 | 127;
            frameBuffer.writeBigUInt64BE(BigInt(len), 2);
        }

        frameBuffer[headerOffset] = maskKey[0];
        frameBuffer[headerOffset + 1] = maskKey[1];
        frameBuffer[headerOffset + 2] = maskKey[2];
        frameBuffer[headerOffset + 3] = maskKey[3];

        const payloadStart = headerOffset + 4;
        for (let i = 0; i < len; i++) {
            frameBuffer[payloadStart + i] = rawBuffer[i] ^ maskKey[i & 3];
        }
        socket.write(frameBuffer);
    }

    function startPrewarm() {
        if (prewarmInterval) clearInterval(prewarmInterval);
        prewarmInterval = setInterval(() => {
            if (activeTlsSocket && activeTlsSocket.writable) {
                try { sendWsFrame(activeTlsSocket, PING_BUF, 1); } catch (e) {}
            }
        }, PREWARM_INTERVAL);
    }

    function nativeWsStreamParser(socket) {
        const state = new ParserState();
        let chunkLen = 0, chunkOffset = 0, needed = 0, available = 0, toRead = 0;
        let b = 0, basicLen = 0, isFin = false;

        let fragmentPool = Buffer.allocUnsafe(FRAGMENT_POOL_INIT);
        let fragmentPoolSize = FRAGMENT_POOL_INIT;
        let fragmentedTotal = 0;
        let fragmentedOpcode = 0;
        let fragmentedIsText = false;
        let fragmentedMaskKey = null;
        let fragmentedIsMasked = 0;
        let isFragmented = false;

        const ensureFragmentCapacity = (required) => {
            if (required <= fragmentPoolSize) return;
            let newSize = fragmentPoolSize;
            while (newSize < required) newSize *= 2;
            if (newSize > SAB_SIZE) newSize = SAB_SIZE;
            const grown = Buffer.allocUnsafe(newSize);
            fragmentPool.copy(grown, 0, 0, fragmentedTotal);
            fragmentPool = grown;
            fragmentPoolSize = newSize;
        };

        const local_maskKey = state.maskKey;
        const local_extendedLenBuf = state.extendedLenBuf;

        socket.on('data', (chunk) => {
            chunkLen = chunk.length;
            chunkOffset = 0;
            let s_stage = state.stage;
            let s_opcode = state.opcode;
            let s_isMasked = state.isMasked;
            let s_maskOffset = state.maskOffset;
            let s_payloadLen = state.payloadLen;
            let s_extendedLenBytes = state.extendedLenBytes;
            let s_extendedLenRead = state.extendedLenRead;
            let s_payloadOffset = state.payloadOffset;
            let s_fragmentedOpcode = state.fragmentedOpcode;

            while (chunkOffset < chunkLen) {
                if (s_stage === 0) {
                    b = chunk[chunkOffset];
                    isFin = (b & 0x80) === 0x80;
                    s_opcode = b & 0x0F;
                    s_opcode = (s_opcode === 0 && s_fragmentedOpcode !== 0) ? s_fragmentedOpcode : s_opcode;
                    s_fragmentedOpcode = (!isFin && s_opcode > 0 && s_opcode < 8) ? s_opcode : s_fragmentedOpcode;
                    chunkOffset++;
                    s_stage = 1;
                    if (chunkOffset >= chunkLen) break;
                }
                if (s_stage === 1) {
                    b = chunk[chunkOffset];
                    chunkOffset++;
                    s_isMasked = ((b & 0x80) === 0x80) ? 1 : 0;
                    basicLen = b & 0x7F;
                    if (basicLen === 126) {
                        s_stage = 2; s_extendedLenBytes = 2; s_extendedLenRead = 0;
                    } else if (basicLen === 127) {
                        s_stage = 2; s_extendedLenBytes = 8; s_extendedLenRead = 0;
                    } else {
                        s_payloadLen = basicLen;
                        s_stage = (s_isMasked === 1) ? 3 : 4;
                        s_maskOffset = 0; s_payloadOffset = 0;
                    }
                    if (chunkOffset >= chunkLen) break;
                }
                if (s_stage === 2) {
                    needed = s_extendedLenBytes - s_extendedLenRead;
                    available = chunkLen - chunkOffset;
                    toRead = available < needed ? available : needed;
                    chunk.copy(local_extendedLenBuf, s_extendedLenRead, chunkOffset, chunkOffset + toRead);
                    s_extendedLenRead += toRead;
                    chunkOffset += toRead;
                    if (s_extendedLenRead === s_extendedLenBytes) {
                        s_payloadLen = (s_extendedLenBytes === 2)
                            ? local_extendedLenBuf.readUInt16BE(0)
                            : Number(local_extendedLenBuf.readBigUInt64BE(0));
                        s_stage = (s_isMasked === 1) ? 3 : 4;
                        s_maskOffset = 0; s_payloadOffset = 0;
                    }
                    if (chunkOffset >= chunkLen) break;
                }
                if (s_stage === 3) {
                    needed = 4 - s_maskOffset;
                    available = chunkLen - chunkOffset;
                    toRead = available < needed ? available : needed;
                    chunk.copy(local_maskKey, s_maskOffset, chunkOffset, chunkOffset + toRead);
                    s_maskOffset += toRead;
                    chunkOffset += toRead;
                    if (s_maskOffset === 4) s_stage = 4;
                    if (chunkOffset >= chunkLen) break;
                }
                if (s_stage === 4) {
                    needed = s_payloadLen - s_payloadOffset;
                    available = chunkLen - chunkOffset;
                    toRead = available < needed ? available : needed;

                    const isFirstFragment = (!isFragmented && !isFin && s_opcode !== 0);
                    const isContinuingFragment = isFragmented;

                    if (isFirstFragment) {
                        fragmentedOpcode = s_opcode;
                        fragmentedIsText = (fragmentedOpcode === 1);
                        fragmentedTotal = 0;
                        isFragmented = true;
                        fragmentedIsMasked = s_isMasked;
                        if (s_isMasked === 1) {
                            fragmentedMaskKey = Buffer.allocUnsafe(4);
                            local_maskKey.copy(fragmentedMaskKey, 0, 0, 4);
                        }
                    }

                    if (isFirstFragment || isContinuingFragment) {
                        ensureFragmentCapacity(fragmentedTotal + toRead);
                        chunk.copy(fragmentPool, fragmentedTotal, chunkOffset, chunkOffset + toRead);
                        fragmentedTotal += toRead;
                    } else {
                        chunk.copy(workerPayloadBuffer, s_payloadOffset, chunkOffset, chunkOffset + toRead);
                    }

                    s_payloadOffset += toRead;
                    chunkOffset += toRead;

                    if (s_payloadOffset === s_payloadLen) {
                        let finalPayload = null;
                        let finalLen = 0;
                        let wasFragmented = false;

                        if (isFin && isFragmented) {
                            wasFragmented = true;
                            finalPayload = fragmentPool;
                            finalLen = fragmentedTotal;
                            isFragmented = false;
                            fragmentedTotal = 0;
                        } else if (isFin && !isFragmented) {
                            finalPayload = workerPayloadBuffer;
                            finalLen = s_payloadLen;
                        }

                        if (finalPayload !== null && finalLen > 0) {
                            const shouldUnmask = wasFragmented ? (fragmentedIsMasked === 1) : (s_isMasked === 1);
                            if (shouldUnmask) {
                                const maskSrc = wasFragmented ? fragmentedMaskKey : local_maskKey;
                                for (let i = 0; i < finalLen; i++) {
                                    finalPayload[i] ^= maskSrc[i & 3];
                                }
                            }
                            if (wasFragmented && finalPayload !== workerPayloadBuffer) {
                                finalPayload.copy(workerPayloadBuffer, 0, 0, finalLen);
                            }
                        }

                        if (s_opcode === 8) {
                            parentPort.postMessage({ type: 'TERMINATE' });
                        }

                        if (s_opcode === 1 || s_opcode === 2 || (wasFragmented && fragmentedIsText)) {
                            if (isFin && !isFragmented && Atomics.load(workerStateInt32, 1) === 0) {
                                const msgLen = wasFragmented ? finalLen : s_payloadLen;
                                Atomics.store(workerStateInt32, 0, msgLen);
                                Atomics.store(workerStateInt32, 1, 1);
                                const view = workerPayloadBuffer.subarray(0, msgLen);
                                if (view.indexOf(GUILD_UPDATE) !== -1) {
                                    parentPort.postMessage(2);
                                } else {
                                    parentPort.postMessage(1);
                                }
                            }
                        }

                        if (wasFragmented) fragmentedMaskKey = null;
                        s_stage = 0;
                    }
                }
            }

            state.stage = s_stage;
            state.opcode = s_opcode;
            state.isMasked = s_isMasked;
            state.maskOffset = s_maskOffset;
            state.payloadLen = s_payloadLen;
            state.extendedLenBytes = s_extendedLenBytes;
            state.extendedLenRead = s_extendedLenRead;
            state.payloadOffset = s_payloadOffset;
            state.fragmentedOpcode = s_fragmentedOpcode;
        });
    }

    function connectGateway() {
        if (activeTlsSocket) {
            try { activeTlsSocket.destroy(); } catch (e) {}
            activeTlsSocket = null;
        }
        if (hbInterval) { clearInterval(hbInterval); hbInterval = null; }
        if (prewarmInterval) { clearInterval(prewarmInterval); prewarmInterval = null; }

        const tcp = net.connect({
            host: 'gateway.discord.gg',
            port: 443,
            keepAlive: true,
            noDelay: true
        });
        tcp.setNoDelay(true);

        const tlsSock = tls.connect({
            socket: tcp,
            servername: 'gateway.discord.gg',
            rejectUnauthorized: false,
            secureContext: sharedGwCtx,
            session: (gatewaySessionCache && (Date.now() - gatewaySessionTime) < SESSION_TTL) ? gatewaySessionCache : null,
            noDelay: true,
            checkServerIdentity: () => {}
        });
        tlsSock.setNoDelay(true);

        tlsSock.on('secureConnect', () => {
            activeTlsSocket = tlsSock;
            tlsSock.resume();

            const nonce = crypto.randomBytes(16).toString('base64');
            const upgradeReq =
                `GET /?v=9&encoding=json HTTP/1.1\r\n` +
                `Host: gateway.discord.gg\r\n` +
                `Upgrade: websocket\r\n` +
                `Connection: Upgrade\r\n` +
                `Sec-WebSocket-Key: ${nonce}\r\n` +
                `Sec-WebSocket-Version: 13\r\n` +
                `User-Agent: ${USER_AGENT}\r\n\r\n`;
            tlsSock.write(upgradeReq);

            let handshakeLen = 0;
            const onHandshakeData = (chunk) => {
                const copyLen = Math.min(chunk.length, handshakeBuf.length - handshakeLen);
                chunk.copy(handshakeBuf, handshakeLen, 0, copyLen);
                handshakeLen += copyLen;

                const headerEnd = handshakeBuf.indexOf('\r\n\r\n', 0);
                if (headerEnd !== -1 && headerEnd < handshakeLen) {
                    const remainingChunk = handshakeBuf.subarray(headerEnd + 4, handshakeLen);
                    if (handshakeBuf.indexOf('HTTP/1.1 101') !== -1) {
                        tlsSock.removeListener('data', onHandshakeData);
                        nativeWsStreamParser(tlsSock);
                        tlsSock.cork();
                        sendWsFrame(tlsSock, IDENTIFY_BUF, 1);
                        tlsSock.uncork();
                        startPrewarm();
                        if (remainingChunk.length > 0) {
                            tlsSock.emit('data', Buffer.from(remainingChunk));
                        }
                    } else if (handshakeLen > 2048) {
                        tlsSock.destroy();
                    }
                }
            };
            tlsSock.on('data', onHandshakeData);
        });

        tlsSock.on('session', (ticket) => {
            if (ticket && ticket.length > 0) {
                gatewaySessionCache = ticket;
                gatewaySessionTime = Date.now();
            }
        });

        const cleanup = () => {
            if (hbInterval) { clearInterval(hbInterval); hbInterval = null; }
            if (prewarmInterval) { clearInterval(prewarmInterval); prewarmInterval = null; }
            setTimeout(connectGateway, 250);
        };
        tlsSock.on('close', cleanup);
        tlsSock.on('error', cleanup);
        tcp.on('error', cleanup);
    }

    parentPort.on('message', (msg) => {
        if (msg.type === 'HEARTBEAT_INTERVAL') {
            const interval = msg.interval;
            if (hbInterval) clearInterval(hbInterval);
            hbInterval = setInterval(() => {
                if (activeTlsSocket && activeTlsSocket.writable) {
                    sendWsFrame(activeTlsSocket, PING_BUF, 1);
                }
            }, interval);
        } else if (msg.type === 'TERMINATE') {
            if (hbInterval) clearInterval(hbInterval);
            if (prewarmInterval) clearInterval(prewarmInterval);
            try { if (activeTlsSocket) activeTlsSocket.destroy(); } catch (e) {}
            process.exit(0);
        }
    });

    connectGateway();
}