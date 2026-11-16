import {everyKey, exists, forall, nat, oneOf, rule, when, yes} from '../../core/dsl.ts'

// A generic row join with a forgotten input and two forwarding stages. No
// helper invariant or ghost is supplied to the public proof request.
export const pipeline = (broken = false) => rule('row pipeline')
  .sorts('Actor', 'Item', 'Label', 'Token')
  .relations({Allows: ['Item', 'Label'], Offers: ['Actor', 'Item'], Mail: ['Actor', 'Label'], Seen: ['Actor', 'Label'], Pending: ['Token', 'Item'], Answers: ['Token', 'Label'], Owners: ['Token', 'Actor']})
  .inputs({op: oneOf('allow', 'start', 'offer', 'receive', 'attach', 'answer', 'send'), a: nat, x: nat, y: nat, t: nat})
  .assume(({a, x, y, t}) => a.lt(64).and(x.lt(64), y.lt(64), t.lt(64)))
  .state({active: 0})
  .flags(({t, Owners}) => ({fresh: everyKey(a => a.lt(64).implies(Owners.has(t, a).not()))}))
  .flags(({op, a, x, y, t, active, fresh, Offers, Allows, Pending, Answers, Owners, Mail}) => ({
    allowing: op.is('allow').and(active.eq(0)), starting: op.is('start').and(active.eq(0)),
    offering: op.is('offer').and(active.eq(1)),
    attaching: op.is('attach').and(active.eq(1), Offers.has(a, x), fresh),
    answering: op.is('answer').and(active.eq(1), Pending.has(t, x), broken ? yes : Allows.has(x, y)),
    sending: op.is('send').and(active.eq(1), Answers.has(t, y), Owners.has(t, a)),
    receiving: op.is('receive').and(active.eq(1), Mail.has(a, y)),
  }))
  .step(({a, x, y, t, active, allowing, starting, offering, attaching, answering, sending, receiving, Allows, Offers, Pending, Answers, Owners, Mail, Seen}) => ({
    active: when(starting, 1, active), Allows: Allows.add([x, y], allowing), Offers: Offers.add([a, x], offering),
    Mail: Mail.add([a, y], sending), Seen: Seen.add([a, y], receiving), Pending: Pending.add([t, x], attaching),
    Answers: Answers.add([t, y], answering), Owners: Owners.add([t, a], attaching),
  }))
export const safety = (r: ReturnType<typeof pipeline>) => r.law('seen labels have an offered allowed item', ({Seen, Offers, Allows}) => forall((a, y) =>
  a.lt(64).and(y.lt(64), Seen.has(a, y)).implies(exists(x => x.lt(64).and(Offers.has(a, x), Allows.has(x, y))))))
