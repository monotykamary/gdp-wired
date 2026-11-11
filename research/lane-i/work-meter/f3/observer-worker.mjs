import {parentPort, workerData} from 'node:worker_threads'
import {Session} from 'node:inspector'
import {writeSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {selectProfileWindow} from './profile-window.mjs'
const shared = new Int32Array(workerData), session = new Session()
const traceNow = () => performance.now()
const emit = (value, tag = 'F3_RAW_SILENCE') => writeSync(1, tag + ' ' + JSON.stringify(value) + '\n')
const post = (method, params = {}) => new Promise((resolve, reject) => session.post(method, params, (error, result) => error ? reject(error) : resolve(result)))
let last = Atomics.load(shared, 1), since = traceNow(), reports = 0, busy = false, stopping = false, savedProfiles = 0
const keepalive = setInterval(() => {}, 1000)
try {
  session.connectToMainThread()
  await post('Profiler.enable'); await post('Profiler.setSamplingInterval', {interval: 10000}); await post('Profiler.start')
  const stop = async () => {
    if (stopping || busy) return
    stopping = true; clearInterval(timer)
    try { await post('Profiler.stop') }
    finally { clearInterval(keepalive); session.disconnect(); parentPort.close() }
  }
  parentPort.on('message', message => { if (message === 'stop') void stop() })
  const timer = setInterval(async () => {
    if (busy || stopping) return
    if (Atomics.load(shared, 0) !== 1) { if (Atomics.load(shared, 0) === 2) void stop(); return }
    const next = Atomics.load(shared, 1), now = traceNow()
    if (next !== last) { last = next; since = now; return }
    if (now - since <= 250 || reports >= 16) return
    busy = true
    try {
      const {profile} = await post('Profiler.stop')
      const {stack, timing} = selectProfileWindow(profile, now - since)
      const heartbeatAfter = Atomics.load(shared, 1), whileRunning = Atomics.load(shared, 0) === 1
      // Retain bounded raw evidence; never repair or accept invalid timestamps.
      if (!timing.valid && savedProfiles < 2) {
        savedProfiles++
        const raw = JSON.stringify(profile), bytes = Buffer.byteLength(raw), sha256 = createHash('sha256').update(raw).digest('hex')
        emit({report: reports + 1, bytes, sha256, encoding: 'gzip-base64', retained: bytes <= 8 * 1024 * 1024,
          data: bytes <= 8 * 1024 * 1024 ? gzipSync(raw).toString('base64') : undefined}, 'F3_INVALID_PROFILE')
      }
      const stable = heartbeatAfter === next && whileRunning
      emit({rawSilentMs: now - since, whileRunning, heartbeatBefore: next, heartbeatAfter, stable, reports: ++reports, stack, profileWindow: timing, scope: 'raw-progress diagnostic; not weighted F3'}, stable ? 'F3_RAW_SILENCE' : 'F3_RAW_WINDOW_CHANGED')
      await post('Profiler.start'); since = traceNow()
    } catch (error) { emit({error: String(error)}); process.exitCode = 1 }
    finally { busy = false; if (Atomics.load(shared, 0) === 2) void stop() }
  }, 100)
  parentPort.postMessage({ready: true})
} catch (error) { clearInterval(keepalive); parentPort.postMessage({error: String(error)}); session.disconnect(); parentPort.close() }
