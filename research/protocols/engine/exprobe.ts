// wo: does the kernel prove the caller's law from the written ∀ laws and an ∃ law, its witness given or not?
//   bun research/protocols/engine/exprobe.ts [case]
import {proveRule, exists} from '../../../core/dsl.ts'
import {protocols, N} from '../models.ts'
const p = protocols.find(q => q.id === 'consensus_wo_decide')!, r: any = p.make(), laws = p.laws(r)
const human = p.human(r), forall5 = human.slice(0, 5)
const bare = r.law('after init some voting quorum member', ({started, VotingQuorum}: any) => started.eq(1).implies(exists((x: any) => x.lt(N).and(VotingQuorum.has(x)))))
const cases: Record<string, any[]> = {all: [...human, ...laws], bare: [...forall5, bare, ...laws]}
for (const name of process.argv[2] ? [process.argv[2]] : Object.keys(cases)) {
  const t = performance.now(), v: any = proveRule(r, cases[name]!, {search: false})
  console.log(name, v.proven ? 'proven' : `${v.stuck ?? ''} ${String(v.why ?? '').slice(0, 200)}`, Math.round(performance.now() - t), 'ms', v.witnesses ? JSON.stringify(v.witnesses).slice(0, 300) : '')
}
