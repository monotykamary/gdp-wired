import {parentPort, workerData} from 'node:worker_threads'
import {Session} from 'node:inspector'
import {writeSync} from 'node:fs'
const shared = new Int32Array(workerData), session = new Session()
const traceNow = () => performance.now()
const emit = value => writeSync(1, 'F3_RAW_SILENCE ' + JSON.stringify(value) + '\n')
const post = (method, params = {}) => new Promise((resolve, reject) => session.post(method, params, (error, result) => error ? reject(error) : resolve(result)))
let last = Atomics.load(shared, 1), since = traceNow(), reports = 0, busy = false, stopping = false
const keepalive = setInterval(() => {}, 1000)
try {
  session.connectToMainThread()
  await post('Profiler.enable'); await post('Profiler.setSamplingInterval', {interval: 10000}); await post('Profiler.start')
  const stop = async () => { if (stopping || busy) return; stopping = true; clearInterval(timer); clearInterval(keepalive); await post('Profiler.stop'); session.disconnect(); parentPort.close() }
  parentPort.on('message', message => { if (message === 'stop') void stop() })
  const timer = setInterval(async () => {
    if (busy || stopping) return
    if (Atomics.load(shared, 0) !== 1) { if (Atomics.load(shared, 0) === 2) void stop(); return }
    const next = Atomics.load(shared, 1), now = traceNow()
    if (next !== last) { last = next; since = now; return }
    if (now - since <= 250 || reports >= 16) return
    busy = true
    try {
      const {profile} = await post('Profiler.stop'), nodes = new Map(profile.nodes.map(node => [node.id, node]))
      const parents = new Map(profile.nodes.flatMap(node => (node.children ?? []).map(id => [id, node.id])))
      const frequencies = new Map()
      for (const id of (profile.samples ?? []).slice(-25)) frequencies.set(id, (frequencies.get(id) ?? 0) + 1)
      let id = [...frequencies].sort((a, b) => b[1] - a[1])[0]?.[0]
      const stack = []
      while (id !== undefined) { const node = nodes.get(id); if (node) stack.push(node.callFrame); id = parents.get(id) }
      emit({rawSilentMs: now - since, whileRunning: Atomics.load(shared, 0) === 1, reports: ++reports, stack, scope: 'raw-progress diagnostic; not weighted F3'})
      await post('Profiler.start'); since = traceNow()
    } catch (error) { emit({error: String(error)}); process.exitCode = 1 }
    finally { busy = false; if (Atomics.load(shared, 0) === 2) void stop() }
  }, 100)
  parentPort.postMessage({ready: true})
} catch (error) { clearInterval(keepalive); parentPort.postMessage({error: String(error)}); session.disconnect(); parentPort.close() }
