// A diagnostic beside the score (not part of it): every liveness law again with a rank stated, the constant 0 (each
// helpful request reaches `to` in one step), still with no invariant given. A law proven so is one whose rank the
// search didn't find although none was needed; one still unproven needs an invariant (or a real rank) as well.
//   bun research/realworld/rank0.ts
import {proveLeadsTo} from '../../core/dsl.ts'
import {corpus} from './corpus.ts'

let n = 0, ok = 0
for (const it of corpus) for (const law of it.laws) {
  if (!law.live) continue
  const {r, l} = law.live, t = performance.now()
  const v = proveLeadsTo(r, [], {...l, rank: {op: 'const', value: 0}})
  n++; if (v.proven && v.checked) ok++
  console.log(`${v.proven && v.checked ? 'proven ' : 'not    '} ${String(Math.round(performance.now() - t)).padStart(6)} ms  ${it.id}: ${law.name}${v.proven ? '' : `  (${[v.goal, v.stuck, v.why].filter(Boolean).join('; ').slice(0, 160)})`}`)
}
console.log(`\nwith rank 0 stated: ${ok} / ${n} proven`)
