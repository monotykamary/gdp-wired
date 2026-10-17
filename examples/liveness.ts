// Liveness under fairness: for the suite (`bun examples/liveness.ts`), core/liveness.test.ts and lean-kernel's export.
//
// A ticket queue: `take` issues the next ticket (while fewer than `cap` wait), `work` serves the oldest. Every ticket
// issued is served later, in every run that sends `work` infinitely often: the tickets ahead of ticket t only shrink,
// and `work` serves one. The broken variant stalls `work` while two or more wait, so a run that keeps sending `work`
// can still wait forever.
import {type Law} from '../core/machine.ts'
import {type Liveness, nat, oneOf, rule, when} from '../core/dsl.ts'
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

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'stalls with two waiting'] as const) {
    const r = tickets(bug), v = proveLiveness(r.machine, ticketLaws(r), everyTicket(r))
    results.push([`ticket queue${bug ? ` (${bug})` : ''}: every ticket is served`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
