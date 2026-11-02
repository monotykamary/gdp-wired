import {expect, test} from 'bun:test'
import {type C, n, x} from '../core/machine.ts'
import {work} from '../core/solver.ts'
import {decide, decideHook, eprMeter} from './epr.ts'
import {type Goal, check} from './kernel.ts'
import {clock, counted, eprScope, grow, late, withDeadline, withinDeadline} from './prove.ts'

for (const full of [false, true]) test(`EPR debits counted deadlines (${full ? 'full' : 'rows'}), including nested work`, () => counted(100, () => {
  const start = clock()
  withDeadline(start + 10, () => {
    eprMeter.n += 200
    expect(withinDeadline(Infinity)).toBeCloseTo(start + 8)
    withDeadline(start + 50, () => {
      eprMeter.n += 300
      expect(withinDeadline(Infinity)).toBeCloseTo(start + 5)
    })
    expect(withinDeadline(Infinity)).toBeCloseTo(start + 5)
    withDeadline(start + 1, () => { eprMeter.n += 100; expect(late(withinDeadline(Infinity))).toBe(false) })
    expect(withinDeadline(Infinity)).toBeCloseTo(start + 4)
    expect(() => withDeadline(start, () => { eprMeter.n += 100; throw Error('scope') })).toThrow('scope')
    expect(withinDeadline(Infinity)).toBeCloseTo(start + 3)
    // Work outside the inner query still counts toward the outer deadline, but not clock() a second time.
    expect(clock()).toBe(start)
    eprMeter.n += 301
    expect(late(withinDeadline(Infinity))).toBe(true)
  })
  expect(withinDeadline(Infinity)).toBe(Infinity)
}, full))

test('plain rows and EPR share the caller allowance; nested counted retains the outer rate', () => counted(100, () => {
  const start = clock()
  withDeadline(start + 5, () => counted(1, () => {
    work.n += 200; eprMeter.n += 200
    expect(withinDeadline(Infinity) - clock()).toBeCloseTo(1)
    work.n += 101
    expect(late(withinDeadline(Infinity))).toBe(true)
  }))
}))

test('wall-clock scopes do not turn EPR work into elapsed wall time', () => {
  const end = clock() + 100_000
  withDeadline(end, () => { eprMeter.n += 10_000_000; expect(withinDeadline(Infinity)).toBe(end) })
})

const key = (name: string, tupled: boolean) => tupled ? {op: 'tup' as const, a: x(name), b: x(name + '-second')} : x(name)
const c = (name: string, tupled = false): C => ({op: '=', a: {op: 'get', map: 'R', key: key(name, tupled)}, b: n(1)})
const goal = (name: string, tupled = false): Goal => ({name, hyps: Array.from({length: 12}, (_, i) => c(`k${i}`, tupled))})

for (const tupled of [false, true]) {
test(`${tupled ? 'tuple' : 'radix'} EPR stops at an inherited counted deadline, not just at a wall cap`, () => {
  const old = eprScope.patterns, hook = decideHook.on
  let decision: ReturnType<typeof decide> | undefined
  eprScope.patterns = {R: tupled ? [0, 0] : [1]}; decideHook.on = (_, d) => { decision = d }
  try {
    for (const full of [false, true]) counted(1, () => {
      const before = eprMeter.n
      const out = withDeadline(clock() + 1, () => grow(goal(`clock-stop-${tupled}-${full}`, tupled)))
      expect(decision).toEqual({unknown: 'past the deadline'})
      expect('tree' in out).toBe(false)
      expect(eprMeter.n - before).toBeGreaterThan(1)
      // Facts and encoding have separate 4096-unit checkpoints; native tuple encoding can enter both.
      expect(eprMeter.n - before).toBeLessThanOrEqual(8192)
    }, full)
  } finally { eprScope.patterns = old; decideHook.on = hook }
})

test(`${tupled ? 'tuple' : 'radix'} EPR queries that fit keep their decisions, and proof trees still replay`, () => {
  const old = eprScope.patterns
  eprScope.patterns = {R: tupled ? [0, 0] : [1]}
  try {
    const sat = goal(`clock-sat-${tupled}`, tupled), unsat: Goal = {name: `clock-unsat-${tupled}`, hyps: [c('one', tupled), {op: '=', a: {op: 'get', map: 'R', key: key('one', tupled)}, b: n(0)}]}
    for (const g of [sat, unsat]) {
      const baseline = decide(g, eprScope.patterns, {exact: true})
      expect('unknown' in baseline).toBe(false)
      for (const full of [false, true]) counted(100, () => withDeadline(clock() + 100_000, () => {
        const d = decide(g, eprScope.patterns!, {exact: true, late: () => late(withinDeadline(Infinity))})
        expect('unknown' in d).toBe(false)
        if ('sat' in baseline && 'sat' in d) expect(d.sat).toBe(baseline.sat)
        const out = grow(g)
        if ('tree' in out) expect(check(g, out.tree)).toBe(true)
        else expect(out.stuck).toBe('sat')
        expect('tree' in out).toBe(g === unsat)
      }), full)
    }
  } finally { eprScope.patterns = old }
})
}
