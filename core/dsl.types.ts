// Type-level checks for the builders (dsl.ts): every line marked @ts-expect-error must fail to type-check, and
// `tsc -p .` fails if one of them doesn't (an unused @ts-expect-error is itself an error). Never run: type-checked only.
import {type DecisionEnv, bool, forall, maybe, nat, oneOf, record, recur, rule, variant, when, yes} from './dsl.ts'

const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})

export function typeChecks() {
  // A misspelled name.
  // @ts-expect-error bb is not a param, input or state variable
  budget.law('typo', ({s, bb}) => s.atMost(bb))
  // A law reads params and state, never a request.
  // @ts-expect-error c is an input
  budget.law('reads a request', ({s, c}) => s.atMost(c))
  // A step sets only declared state.
  // @ts-expect-error spent is not in the state
  budget.step(({s}) => ({spent: s.plus(1)}))
  // A step's update is a term, not a condition.
  // @ts-expect-error a condition where a term is due
  budget.step(({s, b}) => ({s: s.lt(b)}))
  // A precondition reads the params only.
  // @ts-expect-error s is state
  budget.pre(({s}) => s.atMost(1))

  const caps = rule('caps').params({d: nat}).inputs({day: nat, ok: bool}).maps({Day: 0})
  // A map is written through its own handle.
  // @ts-expect-error Days is not a map
  caps.step(({Day, day}) => ({Days: Day.bump(day)}))
  // A map law needs a key.
  caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
  // @ts-expect-error a boolean input is a condition, not a number to add
  caps.step(({Day, day, ok}) => ({Day: Day.set(day, ok)}))
  caps.step(({Day, day, ok}) => ({Day: Day.set(day, ok.n)}))

  const facts = rule('facts').inputs({plan: oneOf('free', 'pro'), spent: maybe(nat)})
  // Every case of a choice, by name.
  // @ts-expect-error the case team is not a value of plan
  facts.decide('x', () => [], ({plan}) => plan.is('team'))
  // @ts-expect-error pro is missing
  facts.decide('x', () => [], ({plan}) => plan.match({free: () => plan.is('free')}))
  // A missing value can't be read outside `some`.
  // @ts-expect-error spent is a Maybe, not a term
  facts.decide('x', () => [], ({spent}) => spent.atMost(3))
  facts.decide('x', () => [], ({spent}) => spent.match({none: () => spent.isNone, some: v => v.atMost(3)}))
  // A helper outside the chain, typed by the rule.
  const known = ({spent}: DecisionEnv<typeof facts>) => spent.isSome
  facts.decide('y', env => known(env), ({spent}) => spent.isSome)
  // @ts-expect-error a helper typed for facts doesn't take another rule's values
  known({plan: 1})

  // A history's record has only the logged inputs; a sum reads the record and the params, not the request.
  const h = rule('h').params({w: nat}).inputs({t: nat, amount: nat, who: nat}).log('t', 'amount')
  // @ts-expect-error who is not logged
  h.sums({total: r => r.who})
  // @ts-expect-error t (the request's) is not in a sum's reach
  h.sums({recent: (r, {t}) => when(r.t.lt(t), 1, 0)})
  h.sums({total: r => r.amount})
  // @ts-expect-error prune by a logged input only
  h.prune('who', ({w}) => w)

  // Records and variants: a case's fields only inside match, each case by name, writes by the case's own fields.
  const Pay = variant({card: {amount: nat, verified: bool}, cash: {amount: nat}})
  const pays = rule('pays').inputs({pay: Pay, who: record({limit: nat, blocked: bool})}).state({last: Pay.from({tag: 'cash', amount: 0})})
  pays.decide('x', () => [], ({pay, who}) => pay.match({card: c => c.amount.atMost(who.limit), cash: () => who.blocked.not()}))
  // @ts-expect-error cash is missing
  pays.decide('x', () => [], ({pay}) => pay.match({card: c => c.verified}))
  // @ts-expect-error a card's fields are read inside match
  pays.decide('x', () => [], ({pay}) => pay.amount.atMost(3))
  // @ts-expect-error cash has no field verified
  pays.decide('x', () => [], ({pay}) => pay.match({card: () => yes, cash: c => c.verified}))
  // @ts-expect-error cheque is not a case
  pays.decide('x', () => [], ({pay}) => pay.is('cheque'))
  // @ts-expect-error who has no field tier
  pays.decide('x', () => [], ({who}) => who.tier.is('gold'))
  pays.step(({pay}) => ({last: pay}))
  pays.step(() => ({last: Pay.make({tag: 'card', amount: 3, verified: true})}))
  // @ts-expect-error a card is written with its verified field
  pays.step(() => ({last: Pay.make({tag: 'card', amount: 3})}))
  // @ts-expect-error cash has no field verified
  pays.step(() => ({last: Pay.make({tag: 'cash', amount: 3, verified: true})}))

  // Maps and lists of a kind take whole values of it; a recurrence's further arguments and functions by name.
  const Acct = record({limit: nat, frozen: bool})
  const accts = rule('accts').inputs({who: nat, job: record({id: nat})}).maps({A: Acct.from({limit: 0, frozen: false})}).items({Q: record({id: nat})})
  accts.step(({who, A}) => ({A: A.set(who, {limit: 3, frozen: true})}))
  // @ts-expect-error frozen is left out
  accts.step(({who, A}) => ({A: A.set(who, {limit: 3})}))
  accts.step(({job, Q}) => Q.apply(Q.push(job)))
  // @ts-expect-error an item is a record of its fields, not a number
  accts.step(({Q}) => Q.apply(Q.push(3)))
  accts.law('limits', ({A}) => forall(k => A.at(k).limit.atLeast(0)))
  // @ts-expect-error a cell has no field spent
  accts.law('spent', ({A}) => forall(k => A.at(k).spent.atLeast(0)))
  recur('f', {args: ['cap'], zero: 0, next: (_, p, {cap}) => p.plus(cap)})
  // @ts-expect-error room is not an argument
  recur('f', {args: ['cap'], zero: 0, next: (_, p, {room}) => p.plus(room)})
}
