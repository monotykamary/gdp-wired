// Feasibility probe (research only): paxos_epr's safety with the inductive invariant written by hand (mypyvy's, in the
// port's encoding, its quorum laws as counts over two parameters, and the propose phase's own), proven through the
// counted search's goals (core/counts.ts) and the kernel's check of the set.
//   bun research/protocols/quorum/paxos-hand.ts [ms] [only,law,names]
import {MapRef, forall} from '../../../core/dsl.ts'
import {searchCounted} from '../../../core/counts.ts'
import {N, pk, pk3} from '../ic3syn/common.ts'
import {protocols} from '../ic3syn/models.ts'

const p = protocols.find(q => q.id === 'paxos_epr')!
const r0: any = p.make()
const r: any = r0.counts({
  votes: ({Vote, size}: any) => ({below: size, base: N, body: (a: any, k: any, b: any) => Vote.at(pk3(k, a, b))}),
  free: ({Left, Vote, size}: any) => ({below: size, base: N, body: (a: any, k: any, b: any) => Left.at(pk(k, a)).not().or(Vote.at(pk3(k, a, b)))}),
  qs: ({Qs, size}: any) => ({below: size, body: (_x: any, k: any) => Qs.at(k)}),
})
// (a law reads a count of the state as a map: the rule's env gives laws no count)
const votes = new MapRef('votes', 0), free = new MapRef('free', 0), qs = new MapRef('qs', 0)
const lt = (...ts: any[]) => ts.map(t => t.lt(N)).reduce((a, b) => a.and(b))
const laws = [
  ...p.laws(r),
  r.law('proposals unique', ({Proposal}: any) => forall((a, b, c) => lt(a, b, c).and(Proposal.at(pk(a, b)), Proposal.at(pk(a, c))).implies(b.eq(c)))),
  r.law('vote proposed', ({Vote, Proposal}: any) => forall((n, a, b) => lt(n, a, b).and(Vote.at(pk3(n, a, b))).implies(Proposal.at(pk(a, b))))),
  r.law('decision proposed', ({Decision, Proposal}: any) => forall((a, b) => lt(a, b).and(Decision.at(pk(a, b))).implies(Proposal.at(pk(a, b))))),
  r.law('decision has votes', ({Decision, size}: any) => forall((a, b) => lt(a, b).and(Decision.at(pk(a, b))).implies(size.lt(votes.at(pk(a, b)).times(2))))),
  r.law('one_b left', ({OneB, Left}: any) => forall((n, a, b) => lt(n, a, b).and(OneB.at(pk(b, n)), a.lt(b)).implies(Left.at(pk(n, a))))),
  r.law('choosable', ({Proposal, size}: any) => forall((a, b, c, d) => lt(a, b, c, d).and(a.lt(c), b.eq(d).not(), Proposal.at(pk(c, d))).implies(free.at(pk(a, b)).times(2).atMost(size)))),
  r.law('no proposal at none', ({Proposal, none}: any) => forall(b => b.lt(N).implies(Proposal.at(pk(none, b)).not()))),
  r.law('busy joined', ({busy, Qs, OneB, pr}: any) => forall(k => k.lt(N).and(busy.eq(1), Qs.at(k)).implies(OneB.at(pk(pr, k))))),
  r.law('busy no proposal', ({busy, Proposal, pr}: any) => forall(b => b.lt(N).and(busy.eq(1)).implies(Proposal.at(pk(pr, b)).not()))),
  r.law('busy round', ({busy, pr, pv, pmaxr, cnt, none, size}: any) => forall(_k => busy.eq(1).implies(pr.eq(none).not().and(pr.lt(N), pv.lt(N), pmaxr.lt(N), cnt.lt(size))))),
  r.law('busy quorum', ({busy, size}: any) => forall(_k => busy.eq(1).implies(size.lt(qs.at(0).times(2))))),
  r.law('Qs in size', ({Qs, size}: any) => forall(k => Qs.at(k).implies(k.lt(size)))),
  r.law('busy maxr', ({busy, pr, pv, pmaxr, none, Proposal}: any) => forall(_k => busy.eq(1).and(pmaxr.eq(none).not()).implies(pmaxr.lt(pr).and(Proposal.at(pk(pmaxr, pv)))))),
  r.law('busy rows', ({busy, pr, pmaxr, none, cnt, Qs, Vote}: any) => forall((c, a, b) => lt(c, a, b).and(busy.eq(1), c.lt(cnt), Qs.at(c), Vote.at(pk3(c, a, b)), a.lt(pr)).implies(pmaxr.eq(none).not().and(a.atMost(pmaxr))))),
]
const only = process.argv[3]?.split(',')
const use = only ? laws.filter((l: any) => only.includes(l.name) || l.name === 'one value decided') : laws
const t0 = performance.now(), c = searchCounted(r.machine, use, Number(process.argv[2] ?? 120_000))
console.log(JSON.stringify({proven: c.proven, why: c.why, laws: c.laws.map(l => l.name), ms: Math.round(performance.now() - t0)}))
