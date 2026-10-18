// Liveness under fairness: for the suite (`bun examples/liveness.ts`), core/liveness.test.ts and lean-kernel's export.
//
// A ticket queue: `take` issues the next ticket (while fewer than `cap` wait), `work` serves the oldest. Every ticket
// issued is served later, in every run that sends `work` infinitely often: the tickets ahead of ticket t only shrink,
// and `work` serves one. The broken variant stalls `work` while two or more wait, so a run that keeps sending `work`
// can still wait forever.
//
// Batches: two requests each helpful in its own region, and a rank of two naturals compared in order. A recounted queue:
// a history whose query the helpful request leaves free. A review queue: a machine with sets, the set the helpful
// request carries left free.
import {type Law} from '../core/machine.ts'
import {type Liveness, count, everyKey, nat, oneOf, relation, rule, when, yes} from '../core/dsl.ts'
import {proveLiveness} from '../kernel/prove.ts'

export const tickets = (bug?: 'stalls with two waiting') => rule('ticket queue').params({cap: nat, t: nat}).inputs({op: oneOf('take', 'work')}).state({next: 0, served: 0})
  .flags(({op, next, served, cap}) => ({
    taking: op.is('take').and(next.minus(served).lt(cap)),
    working: op.is('work').and(served.lt(next), bug ? next.minus(served).lt(2) : served.lt(next)),
  }))
  .step(({next, served, taking, working}) => ({next: when(taking, next.plus(1), next), served: when(working, served.plus(1), served)}))
const ok = tickets()
export const ticketLaws = (r = ok): Law[] => [r.law('nothing served before it is issued', ({served, next}) => served.atMost(next))]
export const everyTicket = (r = ok): Liveness => r.leadsTo('every ticket issued is served', {
  from: ({t, next, served}) => t.lt(next).and(served.atMost(t)),
  to: ({t, served}) => served.gt(t),
  rank: ({t, served}) => t.plus(1).minus(served),
  helpful: () => ({op: 1}),
})

// The same queue keeping a log: `served` is the number of work requests the log keeps (a sum over it), each kept only
// while a ticket waits. Its liveness goes through its plain machine (the sum as state).
export const loggedTickets = (bug?: 'stalls with two waiting') => rule('logged ticket queue').params({cap: nat, t: nat}).inputs({op: oneOf('take', 'work')}).state({next: 0})
  .log('op')
  .sums({served: r => count(r.op.is('work'))})
  .flags(({op, next, served, cap}) => ({
    taking: op.is('take').and(next.minus(served).lt(cap)),
    working: op.is('work').and(served.lt(next), bug ? next.minus(served).lt(2) : served.lt(next)),
  }))
  .keep(({working}) => working)
  .step(({next, taking}) => ({next: when(taking, next.plus(1), next)}))
const logged = loggedTickets()
export const loggedLaws = (r = logged): Law[] => [r.law('nothing served before it is issued', ({served, next}) => served.atMost(next))]
export const everyLoggedTicket = (r = logged): Liveness => r.leadsTo('every ticket issued is served', {
  from: ({t, next, served}) => t.lt(next).and(served.atMost(t)),
  to: ({t, served}) => served.gt(t),
  rank: ({t, served}) => t.plus(1).minus(served),
  helpful: () => ({op: 1}),
})

// Batches: `load` opens the next waiting batch (of `size` items) once the open one is done, `work` does one item of it.
// Every batch gets done in every run that sends both infinitely often, by the rank (batches waiting, items left)
// compared in order: a load trades a batch for `size` items. `work` helps while items are left, `load` once none are;
// neither helps everywhere. The broken variant stalls `work` on the last item.
export const batches = (bug?: 'stalls on the last item') => rule('batches').params({size: nat}).inputs({op: oneOf('load', 'work')}).state({waiting: 5, items: 0})
  .flags(({op, waiting, items}) => ({loading: op.is('load').and(items.eq(0), waiting.gt(0)), working: op.is('work').and(bug ? items.gt(1) : items.gt(0))}))
  .step(({size, waiting, items, loading, working}) => ({waiting: when(loading, waiting.minus(1), waiting), items: when(loading, size, when(working, items.minus(1), items))}))
export const batchLaws = (r = batches()): Law[] => [r.law('at most five batches wait', ({waiting}) => waiting.atMost(5))]
export const allDone = (r = batches()): Liveness => r.leadsTo('every batch gets done', {
  from: () => yes,
  to: ({waiting, items}) => waiting.eq(0).and(items.eq(0)),
  rank: ({waiting, items}) => [waiting, items],
  helpful: [{when: ({items}) => items.gt(0), request: () => ({op: 1})}, {when: ({items}) => items.eq(0), request: () => ({op: 0})}],
})

// The logged queue checking its count against a recount of the log: a query, at least the count by a relation proven
// record by record. The helpful request names `op` and leaves the recount free, any value the relation allows. The
// broken variant reads the recount the wrong way round.
export const recounted = (bug?: 'reads the recount backwards') => rule('recounted ticket queue').params({cap: nat, t: nat}).inputs({op: oneOf('take', 'work')}).state({next: 0})
  .log('op')
  .sums({served: r => count(r.op.is('work'))})
  .queries({recount: r => count(r.op.is('work'))})
  .relations(({served, recount}) => [relation(served.atMost(recount))])
  .flags(({op, next, served, recount, cap}) => ({
    taking: op.is('take').and(next.minus(served).lt(cap)),
    working: op.is('work').and(served.lt(next), bug ? recount.lt(served) : served.atMost(recount)),
  }))
  .keep(({working}) => working)
  .step(({next, taking}) => ({next: when(taking, next.plus(1), next)}))
const recountedOk = recounted()
export const recountedLaws = (r = recountedOk): Law[] => [r.law('nothing served before it is issued', ({served, next}) => served.atMost(next))]
export const everyRecountedTicket = (r = recountedOk): Liveness => r.leadsTo('every ticket issued is served', {
  from: ({t, next, served}) => t.lt(next).and(served.atMost(t)),
  to: ({t, served}) => served.gt(t),
  rank: ({t, served}) => t.plus(1).minus(served),
  helpful: () => ({op: 1}),
})

// A review queue over a set: `submit` carries a set of documents and makes each pending, `approve` clears the one named.
// Document d, once pending, is approved in every run that sends `approve d` infinitely often, whatever set that request
// carries. The broken variant approves only a document the request's set names too.
export const reviews = (bug?: 'approves only what the set names') => rule('review queue').params({d: nat}).inputs({op: oneOf('submit', 'approve'), doc: nat}).maps({Pending: 0}).carries('Batch')
  .assume(({Batch}) => everyKey(k => Batch.at(k).atMost(1)))
  .step(({op, doc, Batch, Pending}) => ({Pending: Pending.each(k => when(op.is('submit'), when(Batch.at(k).eq(1), 1, Pending.at(k)),
    when(op.is('approve').and(k.eq(doc), bug ? Batch.at(k).eq(1) : yes), 0, Pending.at(k))))}))
const reviewsOk = reviews()
export const reviewLaws = (r = reviewsOk): Law[] => [r.law('pending is a set', ({Pending}) => ({forall: k => Pending.at(k).atMost(1)}))]
export const everyReview = (r = reviewsOk): Liveness => r.leadsTo('a pending document is approved', {
  from: ({d, Pending}) => Pending.at(d).eq(1),
  to: ({d, Pending}) => Pending.at(d).eq(0),
  rank: ({d, Pending}) => Pending.at(d),
  helpful: ({d}) => ({op: 1, doc: d}),
})

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'stalls with two waiting'] as const) {
    const r = tickets(bug), v = proveLiveness(r.machine, ticketLaws(r), everyTicket(r))
    results.push([`ticket queue${bug ? ` (${bug})` : ''}: every ticket is served`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'stalls with two waiting'] as const) {
    const r = loggedTickets(bug), v = proveLiveness(r.machine, loggedLaws(r), everyLoggedTicket(r))
    results.push([`logged ticket queue${bug ? ` (${bug})` : ''}: every ticket is served`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'stalls on the last item'] as const) {
    const r = batches(bug), v = proveLiveness(r.machine, batchLaws(r), allDone(r))
    results.push([`batches${bug ? ` (${bug})` : ''}: every batch gets done`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'reads the recount backwards'] as const) {
    const r = recounted(bug), v = proveLiveness(r.machine, recountedLaws(r), everyRecountedTicket(r))
    results.push([`recounted ticket queue${bug ? ` (${bug})` : ''}: every ticket is served`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'approves only what the set names'] as const) {
    const r = reviews(bug), v = proveLiveness(r.machine, reviewLaws(r), everyReview(r))
    results.push([`review queue${bug ? ` (${bug})` : ''}: a pending document is approved`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
