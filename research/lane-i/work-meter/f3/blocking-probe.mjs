import {Worker, isMainThread, workerData, parentPort} from 'node:worker_threads'
import {writeSync} from 'node:fs'
import {strict as assert} from 'node:assert'

const emit = value => writeSync(1, 'F3_CAPABILITY ' + JSON.stringify(value) + '\n')
if (isMainThread) {
  const shared = new Int32Array(new SharedArrayBuffer(16))
  const worker = new Worker(new URL(import.meta.url), {workerData: shared.buffer})
  const startup = await new Promise((resolve, reject) => {
    worker.once('message', resolve); worker.once('error', reject)
  })
  if (startup.unsupported) { emit({runtime: process.release?.name, version: process.version, supported: false, detail: startup.unsupported}); await worker.terminate() }
  else {
    // Deliberately silent synchronous main-thread work. An ordinary timer on
    // this thread cannot detect it while it is running.
    Atomics.store(shared, 0, 1)
    function mainThreadSilentLoop() {
      const until = performance.now() + 1200
      let n = 0
      while (performance.now() < until) n++
      return n
    }
    const n = mainThreadSilentLoop()
    const detectedBeforeRelease = Atomics.load(shared, 2) === 1
    Atomics.store(shared, 0, 2)
    await new Promise((resolve, reject) => { worker.once('exit', resolve); worker.once('error', reject) })
    emit({runtime: process.release?.name, version: process.version, supported: true, detectedBeforeRelease, iterations: n})
    assert(detectedBeforeRelease, 'profile and stack must be observed before the blocking loop releases')
  }
} else {
  const shared = new Int32Array(workerData)
  let session
  const keepalive = setInterval(() => {}, 1000)
  try {
    const inspector = await import('node:inspector')
    session = new inspector.Session()
    session.connectToMainThread()
    const post = (method, params = {}) => new Promise((resolve, reject) => session.post(method, params, (error, result) => error ? reject(error) : resolve(result)))
    await post('Profiler.enable')
    await post('Profiler.setSamplingInterval', {interval: 10000})
    await post('Profiler.start')
    parentPort.postMessage({ready: true})
    let started, observed = Atomics.load(shared, 1)
    const timer = setInterval(async () => {
      if (Atomics.load(shared, 0) !== 1) return
      const current = Atomics.load(shared, 1), now = performance.now()
      if (started === undefined || current !== observed) { started = now; observed = current; return }
      if (now - started < 300) return
      clearInterval(timer)
      try {
        const {profile} = await post('Profiler.stop')
        const nodes = new Map(profile.nodes.map(node => [node.id, node]))
        const parents = new Map(profile.nodes.flatMap(node => (node.children ?? []).map(id => [id, node.id])))
        const recent = (profile.samples ?? []).slice(-25), counts = new Map()
        for (const id of recent) counts.set(id, (counts.get(id) ?? 0) + 1)
        const leaf = [...counts].sort((a, b) => b[1] - a[1])[0]?.[0]
        const stack = []
        for (let id = leaf; id !== undefined; id = parents.get(id)) {
          const node = nodes.get(id); if (node) stack.push(node.callFrame)
        }
        const whileBlocked = Atomics.load(shared, 0) === 1
        emit({runtime: process.release?.name, kind: 'silent-loop-profile', whileBlocked, samples: recent.length, stack})
        if (whileBlocked && stack.some(frame => frame.functionName === 'mainThreadSilentLoop')) Atomics.store(shared, 2, 1)
        clearInterval(keepalive); session.disconnect(); parentPort.close()
      } catch (error) { emit({kind: 'profile-error', error: String(error)}); process.exitCode = 1; clearInterval(keepalive); session.disconnect(); parentPort.close() }
    }, 100)
  } catch (error) { parentPort.postMessage({unsupported: String(error)}); clearInterval(keepalive); session?.disconnect(); parentPort.close() }
}
