import {expect, test} from 'bun:test'
import {proveRule, proveSteps} from '../../core/dsl.ts'
import {captureFixed, divideFixed} from '../../core/fixed-division.ts'
import {fixedFailure, fixedInt} from '../../core/fixed-integers.ts'
import {orderedModel, safeArrayModel} from './first-fault.ts'

const bits = [false, true] as const

test('first fault precedes later refusal, frames data and output, and is absorbing', () => {
  const {r, order, absorb} = orderedModel()
  expect(proveSteps(r, [], [order, absorb], {from: 'any', search: false})).toMatchObject({proven: true, checked: true})
  const g = r.compiled(), p = r.encodeParams({}), initial = g.init(p)
  // Check totality separately: a proof about successors does not test that a
  // later refusal failed to excise the earlier fault transition.
  for (const event of bits) for (const branch of bits) for (const u of bits) for (const v of bits) for (const refused of bits) {
    const s = g.step(p, initial, r.encodeInput({event, branch, u, v, refused}))
    expect(s).toBeDefined()
    expect(r.decode(s)).toEqual({a: event && u, b: event && !u && branch && v, data: Number(event && !refused && !u && !(branch && v)), result: 0})
  }
})

test('guarded cursor has a reachable bounds invariant and can keep reading', () => {
  const {r, law} = safeArrayModel()
  expect(proveRule(r, [law], {search: false})).toMatchObject({proven: true, checked: true})
  const g = r.compiled(), p = r.encodeParams({}), start = g.init(p), req = r.encodeInput({read: true})
  const once = g.step(p, start, req)
  expect(r.decode(once)).toEqual({i: 1, alarm: false})
  expect(r.decode(g.step(p, once, req))).toEqual({i: 0, alarm: false})
})

test('fixed arithmetic traps at the operation width, not the destination width', () => {
  const i32 = fixedInt(32, true), i64 = fixedInt(64, true)
  expect(fixedFailure(i32.lift(255).plus(i32.lift(255), 'TRAP'))?.ok ?? false).toBe(false)
  expect(fixedFailure(i32.lift(2147483647).plus(i32.lift(1), 'TRAP'))?.ok).toBe(true)
  expect(fixedFailure(i64.lift('-9223372036854775808').minus(i64.lift(1n), 'TRAP'))?.ok).toBe(true)
  for (const remainder of bits) {
    const division = (a: number, b: number) => captureFixed(() => divideFixed(i32.lift(a), i32.lift(b), 'TRUNCATING', 'TRAP', remainder)).value
    expect(fixedFailure(division(7, 0))?.ok).toBe(true)
    expect(fixedFailure(division(-2147483648, -1))?.ok).toBe(true)
    expect(fixedFailure(division(-7, 2))?.ok ?? false).toBe(false)
  }
})
