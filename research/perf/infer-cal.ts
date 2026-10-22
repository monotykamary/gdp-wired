// What core/infer.ts's search does a millisecond, for its counted budgets: `GDP_INFER_TRACE=1 bun research/perf/infer-cal.ts
// [tracks]` runs the frontier corpus's items of those tracks (invariant, exists, cycle by default) in one process, and the
// trace says, per search and phase, its wall time beside what it did (trials, rows, evaluations, the kernel's work).
import {corpus} from '../frontier/corpus.ts'

const tracks = (process.argv[2] ?? 'invariant,exists,cycle').split(',')
for (const i of corpus.filter(c => tracks.includes(c.track) && c.frontier)) {
  console.error(`[item] ${i.id}`)
  const t = performance.now(), v = i.frontier!() as {proven: boolean, checked: boolean}
  console.error(`[item] ${i.id}: ${v.proven && v.checked ? 'proven' : 'not proven'} in ${Math.round(performance.now() - t)} ms`)
}
