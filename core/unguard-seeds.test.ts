import {expect, test} from 'bun:test'
import {forall, nat, oneOf, proveRule, rule, sum, when} from './dsl.ts'
import {proofOutput, type PublicProofOutput} from './proof-output.ts'
import {proposeUnguardedSeeds} from './unguard-seeds.ts'

test('unguarded per-key seed proves scalar-latched multi-slot tally law and retains exact proof output', () => {
  const r = rule('bucket tally')
    .params({cap: nat})
    .inputs({b: nat, slot: nat, w: nat})
    .state({winner: 0})
    .maps({Total: 0, Slot: 0})
    .flags(({b, slot, w, cap, winner, Total, Slot}) => ({
      add: slot.lt(2).and(Slot.at(b.times(2).plus(slot)).eq(0), w.gt(0)),
      wins: slot.lt(2).and(Slot.at(b.times(2).plus(slot)).eq(0), w.gt(0), winner.eq(0), Total.at(b).plus(w).gt(cap)),
    }))
    .step(({b, slot, w, winner, Total, Slot, add, wins}) => ({
      winner: when(wins, b.plus(1), winner),
      Total: Total.set(b, when(add, Total.at(b).plus(w), Total.at(b))),
      Slot: Slot.set(b.times(2).plus(slot), when(add, w, Slot.at(b.times(2).plus(slot)))),
    }))
  const law = r.law('winner total matches its two slots and exceeds cap', ({winner, cap, Total, Slot}) =>
    forall(b => winner.eq(b.plus(1)).implies(
      Total.at(b).eq(sum(Slot.at(b.times(2)), Slot.at(b.times(2).plus(1)))).and(Total.at(b).gt(cap)))))

  let packet: PublicProofOutput | undefined
  proofOutput.on = ev => { packet = ev }
  try {
    const v = proveRule(r, [law], {search: {ms: 5000}})
    expect(v).toMatchObject({proven: true, checked: true})
    expect(v.found?.laws?.length).toBe(1)
    expect(packet?.result).toBe(v)
    expect(packet?.proof).toBeDefined()
  } finally {
    proofOutput.on = undefined
  }
  expect(proveRule(r, [law], {search: false}).proven).toBe(false)
  expect(proveRule(r, [law], {from: 'any', search: {ms: 1000}}).proven).toBe(false)
})

test('unguarded per-key seed handles single-conjunct scalar-latched and map-latched multi-conjunct laws', () => {
  const r1 = rule('sealed dual map')
    .inputs({op: oneOf('add', 'seal'), k: nat, v: nat})
    .state({sealed: 0})
    .maps({A: 0, B: 0, Total: 0})
    .step(({op, k, v, sealed, A, B, Total}) => ({
      sealed: when(op.is('seal'), 1, sealed),
      A: A.set(k, when(op.is('add'), A.at(k).plus(v), A.at(k))),
      B: B.set(k, when(op.is('add'), B.at(k).plus(v), B.at(k))),
      Total: Total.set(k, when(op.is('add'), Total.at(k).plus(v).plus(v), Total.at(k))),
    }))
  const law1 = r1.law('once sealed, total equals A + B', ({sealed, A, B, Total}) =>
    forall(k => sealed.eq(1).implies(Total.at(k).eq(A.at(k).plus(B.at(k))))))
  expect(proposeUnguardedSeeds(r1.machine, law1).length).toBe(1)
  expect(proveRule(r1, [law1], {search: {ms: 5000}})).toMatchObject({proven: true, checked: true})

  const r2 = rule('map-latched bucket')
    .params({cap: nat})
    .inputs({b: nat, slot: nat, w: nat})
    .maps({Ready: 0, Total: 0, Slot: 0})
    .flags(({b, slot, w, cap, Total, Slot}) => ({
      add: slot.lt(2).and(Slot.at(b.times(2).plus(slot)).eq(0), w.gt(0)),
      ready: slot.lt(2).and(Slot.at(b.times(2).plus(slot)).eq(0), w.gt(0), Total.at(b).plus(w).gt(cap)),
    }))
    .step(({b, slot, w, Ready, Total, Slot, add, ready}) => ({
      Ready: Ready.set(b, when(ready, 1, Ready.at(b))),
      Total: Total.set(b, when(add, Total.at(b).plus(w), Total.at(b))),
      Slot: Slot.set(b.times(2).plus(slot), when(add, w, Slot.at(b.times(2).plus(slot)))),
    }))
  const law2 = r2.law('ready bucket matches slots and exceeds cap', ({cap, Ready, Total, Slot}) =>
    forall(b => Ready.at(b).eq(1).implies(
      Total.at(b).eq(sum(Slot.at(b.times(2)), Slot.at(b.times(2).plus(1)))).and(Total.at(b).gt(cap)))))
  expect(proposeUnguardedSeeds(r2.machine, law2).length).toBe(1)
  expect(proveRule(r2, [law2], {search: {ms: 5000}})).toMatchObject({proven: true, checked: true})
})

test('unguarded per-key seed never proves false laws and preserves concrete refutations', () => {
  const broken = rule('broken bucket tally')
    .params({cap: nat})
    .inputs({b: nat, slot: nat, w: nat})
    .state({winner: 0})
    .maps({Total: 0, Slot: 0})
    .flags(({b, slot, w, cap, winner, Total, Slot}) => ({
      add: slot.lt(2).and(Slot.at(b.times(2).plus(slot)).eq(0), w.gt(0)),
      wins: slot.lt(2).and(Slot.at(b.times(2).plus(slot)).eq(0), w.gt(0), winner.eq(0), Total.at(b).plus(w).gt(cap)),
    }))
    .step(({b, slot, w, winner, Total, Slot, add, wins}) => ({
      winner: when(wins, b.plus(1), winner),
      Total: Total.set(b, when(add, Total.at(b).plus(w).plus(1), Total.at(b))),
      Slot: Slot.set(b.times(2).plus(slot), when(add, w, Slot.at(b.times(2).plus(slot)))),
    }))
  const blaw = broken.law('winner total matches its two slots and exceeds cap', ({winner, cap, Total, Slot}) =>
    forall(b => winner.eq(b.plus(1)).implies(
      Total.at(b).eq(sum(Slot.at(b.times(2)), Slot.at(b.times(2).plus(1)))).and(Total.at(b).gt(cap)))))
  const bv = proveRule(broken, [blaw], {search: {ms: 2000}})
  expect(bv.proven).toBe(false)
  expect(bv.run).toBeDefined()
})
