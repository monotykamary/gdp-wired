// gen/wo: a protocol's search run as run.ts runs it, with every decideLaw goal the engine asks written out (each machine
// and law set once, then each goal with the engine's verdict and ms), for wodl.ts's replay.
//   bun research/protocols/engine/wodump.ts <id> <ms> <dump.jsonl> [max goals]
import {appendFileSync, writeFileSync} from 'node:fs'
import {proveRule} from '../../../core/dsl.ts'
import {decideLawHook} from '../../../kernel/prove.ts'
import {protocols} from '../models.ts'

// (every stderr line stamped with the seconds since start)
const T0 = performance.now(), w0 = process.stderr.write.bind(process.stderr)
process.stderr.write = ((s: string | Uint8Array, ...rest: unknown[]) => w0(typeof s === 'string' ? s.replace(/^(?=.)/gm, () => `${((performance.now() - T0) / 1000).toFixed(1)} `) : s, ...(rest as []))) as typeof process.stderr.write
const [id = 'consensus_wo_decide', ms0, file = '/tmp/wo.jsonl', max0] = process.argv.slice(2), ms = Number(ms0 ?? 60_000), max = Number(max0 ?? 4000)
writeFileSync(file, '')
const ids = new WeakMap<object, string>(), byText = new Map<string, string>()
let n = 0, goals = 0
const idOf = (o: object, kind: 'machine' | 'set') => {
  let x = ids.get(o)
  if (x) return x
  const t = JSON.stringify(o)
  x = byText.get(t)
  if (!x) { x = `${kind[0]}${n++}`; byText.set(t, x); appendFileSync(file, `${JSON.stringify({id: x, [kind]: o})}\n`) }
  ids.set(o, x)
  return x
}
decideLawHook.on = (m, laws, i, out, t) => {
  if (process.env.WO_DL_LOG) process.stderr.write(`DL ${laws[i]!.name.slice(0, 80)} [${laws.length}] ${!out ? 'undecided' : out.proven ? 'proven' : 'model ' + out.goal.replace(/.* @/, '@')} ${Math.round(t)} ms\n`)
  if (goals++ >= max) return
  appendFileSync(file, `${JSON.stringify({m: idOf(m, 'machine'), s: idOf(laws, 'set'), i, law: laws[i]!.name.slice(0, 120), out: !out ? 'undecided' : out.proven ? 'proven' : `model ${out.goal.replace(/.* @/, '@')}`, ms: Math.round(t)})}\n`)
}
const p = protocols.find(q => q.id === id)!, r = p.make(), t0 = performance.now(), v: any = proveRule(r, p.laws(r), {search: {ms}})
if (process.env.WO_DUMP_OUT) { const {gzipSync} = await import('node:zlib'); const {readFileSync} = await import('node:fs'); console.log('DUMP'); console.log(gzipSync(readFileSync(file)).toString('base64')) }
console.log(JSON.stringify({id, verdict: v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown', ms: Math.round(performance.now() - t0), goals}))
process.exit(0)
