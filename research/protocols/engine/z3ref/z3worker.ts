// The Z3 worker behind core/z3.ts (exp/z3 only): Z3's wasm build (the z3-solver package) is asynchronous, the engine
// is not, so this thread holds the Z3 contexts and answers each SMT-LIB text through a shared buffer the engine's thread
// waits on (Atomics.wait). One context a name, made on first use; (reset) inside a text clears it.
import {parentPort, workerData} from 'node:worker_threads'
// (the package is the referee's alone, added in its job (bun add z3-solver), not one of the repo's dependencies)
const {init} = await import(['z3', 'solver'].join('-')) as {init: () => Promise<any>}

const sab = workerData.sab as SharedArrayBuffer
const head = new Int32Array(sab, 0, 2), body = new Uint8Array(sab, 8)
const enc = new TextEncoder()
const reply = (s: string) => {
  const b = enc.encode(s), n = Math.min(b.length, body.length)
  body.set(b.subarray(0, n)); head[1] = n
  Atomics.store(head, 0, 1); Atomics.notify(head, 0)
}
const {Z3} = await init()
const contexts = new Map<string, unknown>()
const ctxOf = (name: string) => {
  let c = contexts.get(name)
  if (!c) { const cfg = Z3.mk_config(); Z3.set_param_value(cfg, 'model', 'true'); c = Z3.mk_context(cfg); Z3.del_config(cfg); contexts.set(name, c) }
  return c as Parameters<typeof Z3.eval_smtlib2_string>[0]
}
reply('ready')
parentPort!.on('message', async (msg: {ctx: string, text: string}) => {
  try { reply(await Z3.eval_smtlib2_string(ctxOf(msg.ctx), msg.text)) } catch (e) { reply(`(error "${String(e).replace(/"/g, "'")}")`) }
})
