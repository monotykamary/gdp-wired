// The engine's final whole-set proof and its drop loop (core/infer.ts: a cube the set's proof fails at dropped and the
// proof asked again): a dumped set {m, laws} proven by the usual route (proveLaws) or the fast one, the failing law
// dropped each time, while it is not one of the first `keep` laws (the kinds and the caller's).
//   bun research/protocols/epr/setprobe.ts <set.json> [usual|fast] [keep=4] [max drops=24]
import {readFileSync} from 'node:fs'
import {decideLaw, proveLaws, proveSetFast, withWall} from '../../../kernel/prove.ts'

const [file, mode = 'usual', keepS = '4', maxS = '24'] = process.argv.slice(2)
let {m, laws} = JSON.parse(readFileSync(file!, 'utf8'))
const keep = Number(keepS), max = Number(maxS)
// (warm: each law's goals asked first by decideLaw, as the enumeration's rounds ask them before the set's proof)
if (mode === 'warm') {
  const tw = performance.now(), slow: unknown[] = []
  let proven = 0, sat = 0, none = 0
  for (let i = 0; i < laws.length; i++) {
    const t = performance.now(), r = withWall(tw + Number(process.env.WALL ?? 28_000), () => decideLaw(m, laws, i)), ms = performance.now() - t
    if (r?.proven) proven++; else if (r) sat++; else none++
    if (ms > 300) slow.push({i, ms: Math.round(ms), out: r ? (r.proven ? 'proven' : r.stuck) : 'undefined'})
  }
  console.log(JSON.stringify({warm: Math.round(performance.now() - tw), proven, sat, none, slow}))
}
const t0 = performance.now()
for (let k = 0; k <= max; k++) {
  const t = performance.now()
  const r = withWall(t0 + Number(process.env.WALL ?? 28_000), () => (mode === 'usual' ? proveLaws : proveSetFast)(m, laws))
  const at = r.failed?.goal ?? '', i = (laws as {name: string}[]).findIndex(l => at.startsWith(`${l.name} @`))
  console.log(JSON.stringify({k, laws: laws.length, ms: Math.round(performance.now() - t), proven: r.proven && r.checked, i, stuck: r.failed?.stuck, at: at.slice(0, 100)}))
  if (r.proven || i < keep) break
  laws = laws.filter((_: unknown, j: number) => j !== i)
}
