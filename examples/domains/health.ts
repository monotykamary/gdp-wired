// Healthcare: daily dose caps, chart access with consent, ICU beds with an emergency reserve, refills within a window,
// medication orders, the blood bank, ward rounds.
import {type Bool, type Choice, type Maybe, count, forall, loop, max, maybe, nat, no, oneOf, relation, rule, bool, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Daily dose caps: a dose is given only if the patient's total for the day, the dose included, stays within the cap; a
// new day clears the patient's total.
const doses = (bug?: 'forgets the dose') => rule('daily dose caps')
  .params({cap: nat})
  .inputs({op: oneOf('give', 'newDay'), patient: nat, mg: nat})
  .maps({Given: 0})
  .flags(({op, patient, mg, cap, Given}) => ({gives: op.is('give').and(bug === 'forgets the dose' ? Given.at(patient).atMost(cap) : Given.at(patient).plus(mg).atMost(cap))}))
  .step(({op, patient, mg, gives, Given}) => ({Given: Given.set(patient, when(op.is('newDay'), 0, when(gives, Given.at(patient).plus(mg), Given.at(patient))))}))
const doseLaw = (r: ReturnType<typeof doses>) => r.law('every patient: today\'s doses <= cap', ({Given, cap}) => forall(p => Given.at(p).atMost(cap)))
const dosesForget = doses('forgets the dose')

// Chart access: clinicians read the chart of a patient they are known to treat, or anyone in an emergency (break the
// glass); billing reads it with the patient's consent on file; research needs consent on file and never breaks the
// glass. A missing fact fails closed.
const chart = rule('chart access').inputs({role: oneOf('clinician', 'billing', 'research'), treating: maybe(bool), consent: maybe(bool), emergency: bool})
type ChartEnv = {role: Choice<'clinician' | 'billing' | 'research'>, treating: Maybe<Bool>, consent: Maybe<Bool>, emergency: Bool}
const known = (b: Maybe<Bool>) => b.match({none: () => no, some: x => x})
const reads = (env: ChartEnv) => env.role.match({clinician: () => known(env.treating).or(env.emergency), billing: () => known(env.consent), research: () => known(env.consent)})
const readsConsentDefault = (env: ChartEnv) => env.role.match({clinician: () => known(env.treating).or(env.emergency), billing: () => known(env.consent), research: () => env.consent.match({none: () => env.emergency.not(), some: x => x})})
const chartDecisions = [
  chart.decide('no consent on file: no research access', env => [env.role.is('research'), env.consent.isNone], env => reads(env).not()),
  chart.decide('billing reads only with consent', env => [env.role.is('billing'), reads(env)], env => known(env.consent)),
  chart.decide('research never breaks the glass', env => [env.role.is('research'), env.emergency, reads(env)], env => known(env.consent)),
]
const chartConsentDefault = chart.decide('no consent on file: no research access', env => [env.role.is('research'), env.consent.isNone], env => readsConsentDefault(env).not())

// ICU beds: emergencies take any free bed; an elective admission must leave `reserve` beds free. The bound is a law;
// "an elective admission leaves the reserve" is a law about the step.
const icu = (bug?: 'electives skip the reserve') => rule('ICU beds with an emergency reserve')
  .params({beds: nat, reserve: nat})
  .inputs({op: oneOf('emergency', 'elective', 'discharge')})
  .state({occupied: 0})
  .flags(({op, occupied, beds, reserve}) => ({
    admits: op.is('emergency').and(occupied.lt(beds)).or(op.is('elective').and(bug ? occupied.lt(beds) : occupied.plus(reserve).lt(beds))),
  }))
  .step(({op, occupied, admits}) => ({occupied: when(admits, occupied.plus(1), when(op.is('discharge'), occupied.minus(1), occupied))}))
const icuLaws = (r: ReturnType<typeof icu>) => [r.law('occupied <= beds', ({occupied, beds}) => occupied.atMost(beds))]
const icuSteps = (r: ReturnType<typeof icu>) => [
  r.stepLaw('an elective admission leaves the reserve free', ({beds, reserve}, after) => after.occupied.plus(reserve).atMost(beds), ({op, admits}) => op.is('elective').and(admits)),
  r.stepLaw('a discharge never adds a patient', ({occupied}, after) => after.occupied.atMost(occupied), ({op}) => op.is('discharge')),
]
const icuSkip = icu('electives skip the reserve')

// Refills within a window: a refill goes through only if the refills logged within `window` days before it, plus this
// one, stay within `refills`. `recent` sums the refills in the window ending at now.
const refills = (opts: {pruned?: boolean, bug?: 'off by one'} = {}) => {
  const base = rule(opts.pruned ? 'prescription refills, pruned' : 'prescription refills')
    .params({window: nat, refills: nat, now: nat})
    .inputs({t: nat})
    .log('t')
    .sums({recent: (r, {now, window}) => count(r.t.atMost(now).and(now.lt(r.t.plus(window))))})
    .queries({filled: (r, {t, window}) => count(t.lt(r.t.plus(window)))})
    .flags(({filled, refills}) => ({fills: opts.bug ? filled.atMost(refills) : filled.plus(1).atMost(refills)}))
    .keep(({fills}) => fills)
    .relations(({t, now, recent, filled}) => [relation(recent.atMost(filled), t.atMost(now))])
  return opts.pruned ? base.prune('t', ({window}) => window) : base
}
const refillLaw = (r: ReturnType<typeof refills>) => r.law('refills in the window ending at now <= refills', ({recent, refills}) => recent.atMost(refills))
const refillsOff = refills({bug: 'off by one'})

// A medication order: drafted, activated, then discontinued; a discontinued order is never active again, and only a
// draft is activated. Status 0 draft, 1 active, 2 discontinued.
const order = (bug?: 'reactivates') => rule('medication order lifecycle')
  .inputs({op: oneOf('activate', 'discontinue')})
  .state({status: 0, activations: 0})
  .flags(({op, status}) => ({activates: op.is('activate').and(bug ? status.atLeast(1).not().or(status.eq(2)) : status.eq(0))}))
  .step(({op, status, activations, activates}) => ({
    status: when(activates, 1, when(op.is('discontinue').and(status.eq(1)), 2, status)),
    activations: when(activates, activations.plus(1), activations),
  }))
const orderLaws = (r: ReturnType<typeof order>) => [
  r.law('status is draft, active or discontinued', ({status}) => status.atMost(2)),
  r.law('an order is activated at most once', ({activations}) => activations.atMost(1)),
  r.law('an order has an activation exactly when it left draft', ({status, activations}) => status.eq(0).iff(activations.eq(0))),
]
const orderSteps = (r: ReturnType<typeof order>) => [
  r.stepLaw('a discontinued order stays discontinued', ({status}, after) => status.eq(2).implies(after.status.eq(2))),
  r.stepsLaw('two requests never bring a discontinued order back', 2, ({status}, after) => status.eq(2).implies(after.status.eq(2))),
]
const orderReactivates = order('reactivates')

// The blood bank: units are received and issued per blood type; an issue goes through only if what was issued of that
// type, this issue included, stays within what was received.
const bank = (bug?: 'checks the request alone') => rule('blood bank inventory')
  .inputs({op: oneOf('receive', 'issue'), type: nat, units: nat})
  .maps({Received: 0, Issued: 0})
  .flags(({op, type, units, Received, Issued}) => ({issues: op.is('issue').and(bug ? units.atMost(Received.at(type)) : Issued.at(type).plus(units).atMost(Received.at(type)))}))
  .step(({op, type, units, issues, Received, Issued}) => ({Received: Received.bump(type, op.is('receive'), units), Issued: Issued.bump(type, issues, units)}))
const bankLaw = (r: ReturnType<typeof bank>) => r.law('every type: issued <= received', ({Issued, Received}) => forall(k => Issued.at(k).atMost(Received.at(k))))
const bankAlone = bank('checks the request alone')

// Ward rounds: every patient of every ward is seen, at least one per turn; a finished ward moves the round to the next
// ward. The rank is the pair (wards left, patients left in this ward).
const rounds = (advances: boolean) => loop(advances ? 'ward rounds' : 'ward rounds, stuck on a ward')
  .params({wards: nat, patients: nat})
  .inputs({seen: nat})
  .state({w: ({wards}) => wards, k: ({patients}) => patients})
  .while(({w}) => w.gt(0))
  .body(({w, k, seen, patients}) => {
    const done = k.atMost(max(seen, 1))
    return advances
      ? {w: when(done, w.minus(1), w), k: when(done, patients, k.minus(max(seen, 1)))}
      : {w, k: when(done, patients, k.minus(max(seen, 1)))}
  })
  .rank(({w, k}) => [w, k])
const roundLaws = (r: ReturnType<typeof rounds>) => [r.law('patients left <= patients per ward', ({k, patients}) => k.atMost(patients)), r.law('wards left <= wards', ({w, wards}) => w.atMost(wards))]

export const domain: Domain = {
  domain: 'healthcare',
  about: 'dose caps, chart access with consent, ICU reserve, refills within a window, medication orders, blood bank, ward rounds',
  cases: [
    machineCase('daily dose caps', 'no patient is given more than the daily cap', doses(), [doseLaw(doses())], [
      {name: 'forgets the dose', why: 'the check reads the day so far without the dose being given', rule: dosesForget, laws: [doseLaw(dosesForget)]},
    ]),
    decisionCase('chart access', 'consent fails closed, and only clinicians break the glass', chartDecisions, [
      {name: 'missing consent read as yes', why: 'research with no consent on file is let through unless it is an emergency', decision: chartConsentDefault},
    ]),
    machineCase('ICU beds with an emergency reserve', 'beds never overflow, and electives always leave the reserve', icu(), icuLaws(icu()), [
      {name: 'electives skip the reserve', why: 'an elective admission is checked like an emergency, filling the reserved beds', rule: icuSkip, laws: icuLaws(icuSkip), steps: icuSteps(icuSkip)},
    ], {steps: icuSteps(icu())}),
    machineCase('prescription refills', 'at most `refills` refills in any window, read from the log', refills(), [refillLaw(refills())], [
      {name: 'off by one', why: 'the check admits a refill when the window already holds `refills` of them', rule: refillsOff, laws: [refillLaw(refillsOff)]},
    ]),
    machineCase('prescription refills, pruned', 'the same, the log dropping refills older than the window', refills({pruned: true}), [refillLaw(refills({pruned: true}))]),
    machineCase('medication order lifecycle', 'an order is activated once, and a discontinued order stays discontinued', order(), orderLaws(order()), [
      {name: 'reactivates a discontinued order', why: 'activation is allowed from discontinued, not only from draft', rule: orderReactivates, laws: orderLaws(orderReactivates), steps: orderSteps(orderReactivates)},
    ], {steps: orderSteps(order())}),
    machineCase('blood bank inventory', 'no blood type is issued beyond what was received', bank(), [bankLaw(bank())], [
      {name: 'checks the request alone', why: 'an issue is compared with the stock received, forgetting earlier issues', rule: bankAlone, laws: [bankLaw(bankAlone)]},
    ]),
    loopCase('ward rounds', 'every ward is finished, one patient or more a turn', rounds(true), roundLaws(rounds(true)), [
      {name: 'stuck on a ward', why: 'a finished ward starts over instead of moving to the next', loop: rounds(false), laws: roundLaws(rounds(false))},
    ]),
  ],
}

