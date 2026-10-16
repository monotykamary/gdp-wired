// Two rules as step machines, a budget with capped costs and per-key caps on grants, plus requests in flight, and broken variants.
import {type Law, type Machine, all, any, atMost, bit, get, ite, less, min, minus, n, plus, same, x} from './machine.ts'

// The budget rule: step(s, b, c, m) = s + min(c, m) if s < b, else s.
export const loss = (capped = true): Machine => ({
  name: capped ? 'loss' : 'loss, max_tokens cap forgotten',
  params: ['b', 'm'], inputs: ['c'], state: {s: n(0)},
  step: {state: {s: ite(less(x('s'), x('b')), plus(x('s'), capped ? min(x('c'), x('m')) : x('c')), x('s'))}},
})
export const boundedLoss: Law = {name: 'bounded_loss: s <= b + m', holds: atMost(x('s'), plus(x('b'), x('m')))}

// The caps rule: a request is granted when ok and, for each key kind, the grants with its key are under that kind's cap.
const kinds = [['Acct', 'acct', n(1)], ['Day', 'day', x('d')], ['Hour', 'hour', x('hr')], ['Dom', 'dom', x('dm')]] as const
export const admit = (guarded: readonly string[] = ['Acct', 'Day', 'Hour', 'Dom']): Machine => {
  const granted = all(same(x('ok'), n(1)), ...kinds.filter(([kind]) => guarded.includes(kind)).map(([kind, field, cap]) => less(get(kind, x(field)), cap)))
  return {
    name: guarded.length === 4 ? 'admit' : `admit, guards only ${guarded.join(', ')}`,
    params: ['d', 'hr', 'dm'], inputs: ['acct', 'day', 'hour', 'dom', 'ok'], state: {},
    maps: {Acct: 0, Day: 0, Hour: 0, Dom: 0},
    step: {maps: Object.fromEntries(kinds.map(([kind, field]) => [kind, {key: x(field), value: ite(granted, plus(get(kind, x(field)), n(1)), get(kind, x(field)))}]))},
    assume: bit('ok'),
  }
}
export const capLaws: Law[] = kinds.map(([kind, , cap]) => ({name: `${kind === 'Acct' ? 'once_per_account' : `${kind.toLowerCase()}_cap`}: every ${kind} count <= its cap`, holds: atMost(get(kind, x('k')), cap), forall: 'k'}))

// The same rule with its grant decided once per step, as a grant decision is one call: what a prover can reuse.
export const admitFlagged = (): Machine => {
  const m = admit()
  const granted = all(same(x('ok'), n(1)), ...kinds.map(([kind, field, cap]) => less(get(kind, x(field)), cap)))
  return {...m, name: 'admit', step: {flags: {granted}, maps: Object.fromEntries(kinds.map(([kind, field]) => [kind, {key: x(field), value: ite({op: 'flag', name: 'granted'}, plus(get(kind, x(field)), n(1)), get(kind, x(field)))}]))}}
}

// With k requests in flight together, the bound becomes the budget plus k capped requests. Admission
// checks committed spend s, the cost lands when the request completes, at most 3 in flight, each capped at 50.
export const inflight: Machine = {
  name: 'in-flight requests',
  params: ['b'], inputs: ['t', 'done'], state: {s: n(0), p: n(0)},
  step: {state: {
    s: ite(all(same(x('done'), n(1)), less(n(0), x('p'))), plus(x('s'), min(x('t'), n(50))), x('s')),
    p: ite(same(x('done'), n(1)), ite(less(n(0), x('p')), minus(x('p'), n(1)), x('p')), ite(all(less(x('s'), x('b')), less(x('p'), n(3))), plus(x('p'), n(1)), x('p'))),
  }},
  assume: bit('done'),
}
export const inflightLoss: Law = {name: 'in-flight loss: s <= b + 3 × 50', holds: atMost(x('s'), plus(x('b'), n(150)))}

// A sliding-window limit with a history: a request is admitted when the requests logged within w before it (`seen`, a
// query over the log at the request's time t) leave room under c; an operator's forced request always goes through and
// is logged too. `ours` (a sum over the log) counts the admitted, unforced requests in the window ending at now, a param:
// the ceiling ours <= c holds at every now because it holds at an arbitrary one. It needs a relation the kernel proves
// one record at a time: at t <= now, every record ours counts is one seen counts. With `ordered`, requests come in time
// order and a record older than the window is dropped (the kernel proves it counts toward no later `seen`).
export const windowLimit = (ordered = false): Machine => ({
  name: 'window limit', params: ['w', 'c', 'now'], inputs: ['forced', 't', 'seen'], state: {},
  step: {flags: {admitted: all(same(x('forced'), n(0)), atMost(plus(x('seen'), n(1)), x('c')))}},
  history: {
    keep: any(same(x('forced'), n(1)), {op: 'flag', name: 'admitted'}),
    record: ['forced', 't'],
    sums: {ours: ite(all(same(x('r.forced'), n(0)), atMost(x('r.t'), x('now')), less(x('now'), plus(x('r.t'), x('w')))), n(1), n(0))},
    queries: {seen: ite(less(x('t'), plus(x('r.t'), x('w'))), n(1), n(0))},
    relations: [{when: atMost(x('t'), x('now')), holds: atMost(x('ours'), x('seen'))}],
    ...(ordered ? {prune: {order: 't', after: x('w')}} : {}),
  },
  assume: bit('forced'),
})
export const windowCeiling: Law = {name: 'window_ceiling: admitted in the window <= c', holds: atMost(x('ours'), x('c'))}
