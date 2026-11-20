import {expect, test} from 'bun:test'
import {forall, nat, oneOf, proveRule, rule, when} from './dsl.ts'
import {coveringSeeds, coveringShapes} from './covering.ts'

// A member implies a positive count: the count moves with the membership, and the law needs the count tied to it.
const members = rule('members')
  .inputs({op: oneOf('join', 'leave'), id: nat})
  .state({size: 0})
  .maps({In: 0})
  .flags(({op, id, In}) => ({joins: op.is('join').and(In.at(id).eq(0)), leaves: op.is('leave').and(In.at(id).eq(1))}))
  .step(({id, size, In, joins, leaves}) => ({
    size: when(joins, size.plus(1), when(leaves, size.minus(1), size)),
    In: In.set(id, when(joins, 1, when(leaves, 0, In.at(id)))),
  }))
const backed = members.law('a member means a positive size', ({In, size}) => forall(k => In.at(k).eq(1).implies(size.atLeast(1))))

test('a count-bound law is read as a guard, a weight of one and its total', () => {
  const shapes = coveringShapes(members.machine, backed)
  expect(shapes).toHaveLength(1)
  expect(shapes[0]!.total).toEqual({op: 'var', name: 'size'})
  expect(shapes[0]!.term.op).toBe('if')
  const seeds = coveringSeeds(members.machine, backed, () => 'sum$probe')
  expect(seeds.map(s => s.holds.op)).toEqual(['=', '<='])
})

test('the covering helper proves the law, kernel-checked, and is reported as found', () => {
  const v = proveRule(members, [backed], {search: {ms: 20_000}})
  expect(v.proven && v.checked).toBe(true)
  expect(v.found?.laws?.some(l => l.text.startsWith('covering'))).toBe(true)
})

test('a false covering law is still refuted by its run, never proven', () => {
  // (leaving twice is allowed here: the size is taken from while nothing is a member, so a later member has size 0)
  const leaky = rule('leaky members')
    .inputs({op: oneOf('join', 'leave'), id: nat})
    .state({size: 0})
    .maps({In: 0})
    .step(({op, id, size, In}) => ({
      size: when(op.is('join').and(In.at(id).eq(0)), size.plus(2), when(op.is('leave'), size.minus(1), size)),
      In: In.set(id, when(op.is('join'), 1, In.at(id))),
    }))
  const law = leaky.law('a member means a positive size', ({In, size}) => forall(k => In.at(k).eq(1).implies(size.atLeast(1))))
  const v = proveRule(leaky, [law], {search: {ms: 5_000}})
  expect(v.proven).toBe(false)
  expect(v.run).toBeDefined()
})

test('a law with no total, or about two keys, has no covering shape', () => {
  expect(coveringShapes(members.machine, members.law('cells are flags', ({In}) => forall(k => In.at(k).atMost(1))))).toHaveLength(0)
  expect(coveringShapes(members.machine, members.law('a pair', ({In, size}) => forall((k, j) => In.at(k).plus(In.at(j)).atMost(size.plus(1)))))).toHaveLength(0)
})

test('covering skips uncovered broadcast clears and still proves covered each writes', () => {
  const withClear = rule('broadcast-covering-clear')
    .inputs({op: oneOf('put', 'clear'), id: nat, val: nat})
    .state({total: 0})
    .maps({M: 0})
    .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clear')}))
    .step(({id, val, total, M, puts, clears}) => ({
      total: when(clears, 0, when(puts, total.plus(val), total)),
      M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), val, M.at(k)))),
    }))
  const clearLaw = withClear.law('every cell fits in total', ({M, total}) => forall(k => M.at(k).atMost(total)))
  const vClear = proveRule(withClear, [clearLaw], {search: {ms: 2_000}})
  expect(vClear.proven).toBe(false)
  expect(vClear.checked).toBe(false)
  expect(vClear.run).toBeUndefined()

  const coveredEach = rule('broadcast-covering-covered')
    .inputs({op: oneOf('put', 'remove'), id: nat, val: nat})
    .state({total: 0})
    .maps({M: 0})
    .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), removes: op.is('remove').and(M.at(id).gt(0))}))
    .step(({id, val, total, M, puts, removes}) => ({
      total: when(puts, total.plus(val), when(removes, total.minus(M.at(id)), total)),
      M: M.each(k => when(puts.and(k.eq(id)), val, when(removes.and(k.eq(id)), 0, M.at(k)))),
    }))
  const coveredLaw = coveredEach.law('every cell fits in total', ({M, total}) => forall(k => M.at(k).atMost(total)))
  const vCovered = proveRule(coveredEach, [coveredLaw], {search: {ms: 10_000}})
  expect(vCovered.proven && vCovered.checked).toBe(true)
  expect(vCovered.found?.laws?.some(l => l.text.startsWith('covering'))).toBe(true)
})
