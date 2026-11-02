// Rounding to a tick in the kinds (core/dsl.ts: floorTo, ceilTo, roundTo by a mode, onTick on naturals, integers and
// decimals): each from divBy and modBy, so nothing new reaches the kernel. Run against a reference over exact integers,
// and the laws a quoter needs proven (on a tick, within a tick, within half a tick, the mode's own way with a half) or
// refuted (a mode said to break its halves another way).
import {expect, test} from 'bun:test'
import {type Rounding, decimal, fun, int, nat, proveDecision, when} from './dsl.ts'

// The reference: x/k rounded by the mode, over exact integers.
const ref = (x: number, k: number, mode: Rounding): number => {
  const q = Math.floor(x / k), r = x - q * k
  if (2 * r < k) return q * k + 0
  if (2 * r > k) return (q + 1) * k + 0
  const up = mode === 'halfUp' || (mode === 'halfAway' && x >= 0) || (mode === 'halfEven' && q % 2 !== 0)
  return (up ? q + 1 : q) * k + 0
}

test('floorTo, ceilTo, roundTo and onTick: against the reference, naturals, integers and decimals', () => {
  for (const k of [1, 2, 5, 10]) {
    const fi = fun('ticks').inputs({x: int}).returns(({x}) => ({f: x.floorTo(k), c: x.ceilTo(k), on: x.onTick(k), even: x.roundTo(k), up: x.roundTo(k, 'halfUp'), down: x.roundTo(k, 'halfDown'), away: x.roundTo(k, 'halfAway')}))
    const fn = fun('ticks').inputs({x: nat}).returns(({x}) => ({f: x.floorTo(k), c: x.ceilTo(k), on: x.onTick(k), even: x.roundTo(k), up: x.roundTo(k, 'halfUp'), down: x.roundTo(k, 'halfDown'), away: x.roundTo(k, 'halfAway')}))
    for (let x = -3 * k - 2; x <= 3 * k + 2; x++) {
      const want = {f: Math.floor(x / k) * k, c: Math.ceil(x / k) * k + 0, on: x % k === 0, even: ref(x, k, 'halfEven'), up: ref(x, k, 'halfUp'), down: ref(x, k, 'halfDown'), away: ref(x, k, 'halfAway')}
      expect([k, x, fi.run({x})]).toEqual([k, x, want])
      if (x >= 0) expect([k, x, fn.run({x})]).toEqual([k, x, want])
    }
  }
  const fd = fun('quote').inputs({p: decimal(2)}).returns(({p}) => ({f: p.floorTo(0.05), c: p.ceilTo(0.05), even: p.roundTo(0.05), away: p.roundTo(0.05, 'halfAway'), on: p.onTick(0.05)}))
  expect(fd.run({p: '1.03'})).toEqual({f: 1, c: 1.05, even: 1.05, away: 1.05, on: false})
  expect(fd.run({p: '-1.02'})).toEqual({f: -1.05, c: -1, even: -1, away: -1, on: false})
  expect(fd.run({p: '1.10'})).toEqual({f: 1.1, c: 1.1, even: 1.1, away: 1.1, on: true})
  expect(() => fd.run({p: '1.025'})).toThrow('needs more than 2 decimal places')
})

test('a quoter on a tick: the laws proven, a mode said to round its halves another way refuted', () => {
  const quote = fun('quote').inputs({p: int}).returns(({p}) => ({bid: p.floorTo(10), ask: p.ceilTo(10), even: p.roundTo(10), up: p.roundTo(10, 'halfUp'), away: p.roundTo(10, 'halfAway')}))
  const proven = (name: string, f: Parameters<typeof quote.law>[2]) => expect([name, proveDecision(quote.law(name, () => [], f))]).toMatchObject([name, {proven: true, checked: true}])
  proven('the bid is on a tick', o => o.bid.onTick(10))
  proven('the bid is at most the price, within a tick', (o, {p}) => o.bid.atMost(p).and(p.lt(o.bid.plus(10))))
  proven('the ask is at least the price, within a tick', (o, {p}) => p.atMost(o.ask).and(o.ask.lt(p.plus(10))))
  proven('the nearest is within half a tick', (o, {p}) => o.even.minus(p).times(2).abs.atMost(10))
  proven('a half rounds up, by halfUp', (o, {p}) => p.minus(o.bid).times(2).eq(10).implies(o.up.eq(o.ask)))
  proven('a half rounds away from 0, by halfAway', (o, {p}) => p.minus(o.bid).times(2).eq(10).implies(when(p.isNegative, o.away.eq(o.bid), o.away.eq(o.ask))))
  const broken = (name: string, f: Parameters<typeof quote.law>[2]) => expect([name, proveDecision(quote.law(name, () => [], f)).proven]).toEqual([name, false])
  broken('a half never rounds down, by halfEven', (o, {p}) => p.minus(o.bid).times(2).eq(10).implies(o.even.eq(o.ask)))
  broken('a half rounds up, by halfAway', (o, {p}) => p.minus(o.bid).times(2).eq(10).implies(o.away.eq(o.ask)))
}, 120_000)
