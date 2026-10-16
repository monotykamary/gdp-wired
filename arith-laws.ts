// Sequence laws, proven inside the library: induction (start + one step) splits each law into cases, the
// solver refutes every case with a Farkas certificate, and certificate.ts checks every certificate on its own.
// Usage: bun arith-laws.ts
import {checkCertificate} from './certificate.ts'
import {type Constraint, add, counterexample, eq, k, le, lt, nat, refute, show, v} from './solver.ts'

type Case = {name: string, constraints: Constraint[]}
type Law = {name: string, model: string, start: Case[], step: Case[]}

const negate = (c: Constraint[]): Constraint[] => c.map(({lin, label}) => ({lin: add(k(1), Object.fromEntries(Object.entries(lin).map(([key, value]) => [key, -value]))), label: `not (${label})`}))

// the budget rule's step: s + min(c, m) if s < b, else s. min(c, m) is t, one case per side.
const lossStep = (capped: boolean): Case[] => [
  ...(capped
    ? [
      {name: 's < b, c <= m', constraints: [...lt(v('s'), v('b')), ...le(v('c'), v('m')), ...eq(v('t'), v('c')), ...eq(v("s'"), add(v('s'), v('t')))]},
      {name: 's < b, m < c', constraints: [...lt(v('s'), v('b')), ...lt(v('m'), v('c')), ...eq(v('t'), v('m')), ...eq(v("s'"), add(v('s'), v('t')))]},
    ]
    : [{name: 's < b, cost not capped', constraints: [...lt(v('s'), v('b')), ...eq(v("s'"), add(v('s'), v('c')))]}]),
  {name: 'b <= s, refused', constraints: [...le(v('b'), v('s')), ...eq(v("s'"), v('s'))]},
]
const lossLaw = (capped: boolean): Law => {
  const invariant = (s: string) => le(v(s), add(v('b'), v('m')), `${s} <= b + m`)
  return {
    name: capped ? 'bounded_loss' : 'bounded_loss, with the max_tokens cap forgotten', model: 'budget rule step/run',
    start: [{name: 's = 0', constraints: [...nat('b', 'm'), ...eq(v('s'), k(0)), ...negate(invariant('s'))]}],
    step: lossStep(capped).map(c => ({name: c.name, constraints: [...nat('s', 'b', 'c', 'm', 't', "s'"), ...invariant('s'), ...c.constraints, ...negate(invariant("s'"))]})),
  }
}

// caps rule, for one key kind and any key x of it: count is the grants with key x, and a request with key x is granted
// only while count < cap (its `under`); a grant with another key, or a refusal, leaves count as it is.
const capLaw = (guarded: boolean, cap: 'cap' | 'one'): Law => {
  const capOf = cap === 'one' ? k(1) : v('cap')
  const invariant = (n: string) => le(v(n), capOf, `${n} <= ${show(capOf)}`)
  const vars = cap === 'one' ? ['n', "n'"] : ['n', "n'", 'cap']
  return {
    name: `${cap === 'one' ? 'once_per_account' : 'caps_hold (day_cap, hour_cap, domain_cap)'}${guarded ? '' : ', with the under-cap guard forgotten'}`, model: 'caps rule step/run',
    start: [{name: 'n = 0', constraints: [...nat(...vars), ...eq(v('n'), k(0)), ...negate(invariant('n'))]}],
    step: [
      {name: 'granted, key x', constraints: [...(guarded ? lt(v('n'), capOf, 'under: n < cap') : []), ...eq(v("n'"), add(v('n'), k(1)))]},
      {name: 'granted, another key', constraints: eq(v("n'"), v('n'))},
      {name: 'refused', constraints: eq(v("n'"), v('n'))},
    ].map(c => ({name: c.name, constraints: [...nat(...vars), ...invariant('n'), ...c.constraints, ...negate(invariant("n'"))]})),
  }
}

for (const law of [lossLaw(true), capLaw(true, 'cap'), capLaw(true, 'one'), lossLaw(false), capLaw(false, 'cap')]) {
  const results = [...law.start.map(c => ({...c, phase: 'start'})), ...law.step.map(c => ({...c, phase: 'step'}))].map(c => {
    const verdict = refute(c.constraints)
    return {c, verdict, checked: verdict.kind === 'refuted' && checkCertificate(c.constraints, verdict.certificate)}
  })
  const proven = results.every(r => r.checked)
  console.log(`${proven ? 'PROVEN ' : 'REFUTED'}  ${law.name}  (${law.model}; ${results.length} cases)`)
  for (const {c, verdict} of results) {
    if (verdict.kind === 'refuted') {
      const used = verdict.certificate.flatMap((m, i) => (m > 0 ? [`${m}×[${c.constraints[i]!.label}]`] : []))
      if (c.phase === 'step') console.log(`    ${c.name}: ${used.join(' + ')}`)
    } else {
      console.log(`    ${c.name}: possible, e.g. ${JSON.stringify(counterexample(c.constraints))}`)
    }
  }
}
