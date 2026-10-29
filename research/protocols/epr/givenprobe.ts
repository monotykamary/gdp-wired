// The written invariants (models.ts's `human`) proven as a set both ways: proveLaws (the usual route) and proveSetFast
// (each law settled, the proof made and checked once), with each one's time and verdict.
//   bun research/protocols/epr/givenprobe.ts [id,id]
import {proveRule} from '../../../core/dsl.ts'
import {protocols} from '../models.ts'

const only = process.argv[2]?.split(',')
for (const p of protocols.filter(q => !only || only.includes(q.id))) {
  const out: Record<string, unknown> = {id: p.id}
  for (const fast of [false, true]) {
    const r = p.make(), laws = [...p.human(r), ...p.laws(r)], t = performance.now(), v = proveRule(r, laws, {search: false, fast})
    out[fast ? 'fast' : 'usual'] = {ms: Math.round(performance.now() - t), verdict: v.proven && v.checked ? 'proven' : v.proven ? 'unchecked' : `${v.stuck} at ${v.goal?.slice(0, 80)}`}
  }
  console.log(JSON.stringify(out))
}
