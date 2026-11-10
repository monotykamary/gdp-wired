import {Worker} from 'node:worker_threads'
import {writeSync} from 'node:fs'
import {counters, run} from './facade.mjs'
const on = process.argv[2] === 'on', shared = new Int32Array(new SharedArrayBuffer(16))
const saved = [], emit = (tag, value) => writeSync(1, tag + ' ' + JSON.stringify(value) + '\n')
let worker, exited
try {
  if (on) {
    // Research-only observation: store the identical numeric value, never
    // alter acceptance or select a provisional complete-work weight vector.
    for (const object of counters) for (const key of Object.keys(object)) {
      const descriptor = Object.getOwnPropertyDescriptor(object, key)
      if (!descriptor || typeof descriptor.value !== 'number' || !descriptor.configurable) continue
      let value = descriptor.value
      saved.push(() => Object.defineProperty(object, key, {...descriptor, value}))
      Object.defineProperty(object, key, {configurable: descriptor.configurable, enumerable: descriptor.enumerable,
        get: () => value, set: next => { if (next > value) Atomics.add(shared, 1, 1); value = next }})
    }
    worker = new Worker(new URL('./observer-worker.mjs', import.meta.url), {workerData: shared.buffer})
    exited = new Promise((resolve, reject) => { worker.once('exit', code => code ? reject(Error('observer exit ' + code)) : resolve()); worker.once('error', reject) })
    await new Promise((resolve, reject) => { worker.once('message', message => message.ready ? resolve() : reject(Error(message.error))); worker.once('error', reject) })
  }
  Atomics.store(shared, 0, 1)
  const result = run('mldr', 15000000)
  Atomics.store(shared, 0, 2)
  if (worker) { worker.postMessage('stop'); await exited }
  emit('F3_SOLVER_RESULT', {monitor: on, runtime: process.version, scope: 'Node diagnostic; legacy work weights, not calibrated W or a Bun F3 claim', ...result})
} finally {
  Atomics.store(shared, 0, 2)
  if (worker) await worker.terminate()
  for (const restore of saved) restore()
}
