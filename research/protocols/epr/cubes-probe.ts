// The enumeration's unsure cube goals (callers/<p>-cubes.json, gen/enum4's round 1): each by decideLaw, then proveLaw.
//   bun research/protocols/epr/cubes-probe.ts ring|dist
import {readFileSync} from 'node:fs'
import {decideLaw, proveLaw, withWall} from '../../../kernel/prove.ts'
const p = process.argv[2]!, {m, laws, unsure} = JSON.parse(readFileSync(`${import.meta.dir}/callers/${p}-cubes.json`, 'utf8'))
for (const i of unsure as number[]) {
  let t = performance.now(); const d: any = withWall(performance.now() + 2_000, () => decideLaw(m, laws, i)); const td = performance.now() - t
  t = performance.now(); const r: any = process.argv.includes('--prove') ? withWall(performance.now() + 4_000, () => proveLaw(m, laws, i)) : undefined; const tp = performance.now() - t
  console.log(JSON.stringify({p, i, decideMs: Math.round(td), decide: d === undefined ? 'unknown' : d.proven ? 'proven' : d.stuck, elements: d?.diagram?.elements, ...(r ? {proveMs: Math.round(tp), prove: r.proven ? 'proven' : r.stuck} : {})}))
}
