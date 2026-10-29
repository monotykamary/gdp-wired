// The work proveRule does before the invariant search (a search of 0 ms), per protocol.
//   bun research/protocols/engine/preprobe.ts id...
import {proveRule} from '../../../core/dsl.ts'
import {protocols} from '../models.ts'
for (const id of process.argv.slice(2)) {
  const p = protocols.find(q => q.id === id)!, r: any = p.make(), t = performance.now()
  const v: any = proveRule(r, p.laws(r), {search: {ms: 0}})
  console.log(id, 'before the search', Math.round(performance.now() - t), 'ms', v.proven ? 'proven' : v.stuck)
}
