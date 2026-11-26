// Regression tests for map sums across broadcast (`each`) writes:
// - Runtimes (interpret, loadJs, fastStep) maintain sums exact directly from post-step maps (and throw RangeError
//   when a broadcast makes the sum infinite), never approximating with an uncovered finite-cover delta.
// - Every reported concrete refutation replays independently on the original rule (before withSumsOf).
// - Prover entry points (proveRule, proveSteps, proveLeadsTo, inferLaws, candidateSeeds) refuse uncovered broadcast
//   sums with stuck: 'unknown' and a clear reason rather than falsely refuting or falsely proving.
// - Controls without uncovered broadcasts (e.g. Spark MemoryStore without clear, covered each writes) still prove.
import {expect, test} from 'bun:test'
import {bool, choose, forall, nat, no, oneOf, proveLeadsTo, proveRule, proveSteps, record, replayRefutation, rule, when, yes} from './dsl.ts'
import {inferLaws} from './infer.ts'
import {fastStep, interpret, loadJs} from './machine.ts'

const putClear = () => rule('put-clear')
  .inputs({op: oneOf('put', 'clear'), id: nat, val: nat})
  .state({total: 0})
  .maps({M: 0})
  .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clear')}))
  .step(({id, val, total, M, puts, clears}) => ({
    total: when(clears, 0, when(puts, total.plus(val), total)),
    M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), val, M.at(k)))),
  }))

const Block = record({present: bool, size: nat})

const sparkMemoryStore = (mode: 'with-clear' | 'no-clear-each' | 'no-clear-set' = 'with-clear') => {
  const ops = mode === 'with-clear'
    ? oneOf('putBlock', 'removeBlock', 'reserveUnroll', 'releaseUnroll', 'clear')
    : oneOf('putBlock', 'removeBlock', 'reserveUnroll', 'releaseUnroll')
  return rule(`Spark MemoryStore (${mode})`)
    .params({poolSize: nat})
    .inputs({op: ops, id: nat, size: nat, maxAcquisition: nat})
    .state({memoryUsed: 0})
    .maps({Blocks: Block.from({present: false, size: 0}), Unroll: 0})
    .flags(({op, id, size, maxAcquisition, poolSize, memoryUsed, Blocks, Unroll}) => ({
      puts: op.is('putBlock').and(Blocks.at(id).present.not(), size.atMost(maxAcquisition), memoryUsed.plus(size).atMost(poolSize)),
      removes: op.is('removeBlock').and(Blocks.at(id).present),
      reservesUnroll: op.is('reserveUnroll').and(size.atMost(maxAcquisition), memoryUsed.plus(size).atMost(poolSize)),
      releasesUnroll: op.is('releaseUnroll').and(Unroll.at(id).gt(0)),
      clears: mode === 'with-clear' ? op.is('clear' as never) : no,
    }))
    .step(({id, size, memoryUsed, Blocks, Unroll, puts, removes, reservesUnroll, releasesUnroll, clears}) => {
      const b = Blocks.at(id), u = Unroll.at(id), relU = when(size.atMost(u), size, u)
      return {
        memoryUsed: when(clears, 0,
          when(puts.or(reservesUnroll), memoryUsed.plus(size),
            when(removes, memoryUsed.minus(b.size),
              when(releasesUnroll, memoryUsed.minus(relU), memoryUsed)))),
        Blocks: mode === 'no-clear-set'
          ? Blocks.set(id, {
              present: choose(puts, yes, choose(removes, no, b.present)),
              size: when(puts, size, when(removes, 0, b.size)),
            })
          : Blocks.each(k => ({
              present: mode === 'with-clear'
                ? choose(clears, no, choose(puts.and(k.eq(id)), yes, choose(removes.and(k.eq(id)), no, Blocks.at(k).present)))
                : choose(puts.and(k.eq(id)), yes, choose(removes.and(k.eq(id)), no, Blocks.at(k).present)),
              size: mode === 'with-clear'
                ? when(clears, 0, when(puts.and(k.eq(id)), size, when(removes.and(k.eq(id)), 0, Blocks.at(k).size)))
                : when(puts.and(k.eq(id)), size, when(removes.and(k.eq(id)), 0, Blocks.at(k).size)),
            })),
        Unroll: mode === 'no-clear-set'
          ? Unroll.set(id, when(reservesUnroll, u.plus(size), when(releasesUnroll, u.minus(relU), u)))
          : Unroll.each(k => mode === 'with-clear'
            ? when(clears, 0, when(reservesUnroll.and(k.eq(id)), Unroll.at(k).plus(size), when(releasesUnroll.and(k.eq(id)), Unroll.at(k).minus(relU), Unroll.at(k))))
            : when(reservesUnroll.and(k.eq(id)), Unroll.at(k).plus(size), when(releasesUnroll.and(k.eq(id)), Unroll.at(k).minus(relU), Unroll.at(k)))),
      }
    })
}

const lowerBoundDual = (rareClear: boolean) => rule(rareClear ? 'dual-rare-clear' : 'dual-reachable-clear')
  .inputs({op: oneOf('put', 'clear'), id: nat})
  .state({hasPut: 0})
  .maps({M: 0})
  .flags(({op, id, M}) => ({
    puts: op.is('put').and(M.at(id).eq(0)),
    // Guarded by M[id] == 0 so sumRuntime's finite cover at `id` leaves sum$M unchanged on clear.
    clears: op.is('clear').and(M.at(id).eq(0), rareClear ? id.eq(999999) : yes),
  }))
  .step(({id, hasPut, M, puts, clears}) => ({
    hasPut: when(puts, 1, hasPut),
    M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), 1, M.at(k)))),
  }))

test('two-request broadcast clear: exact runtimes and proven via reset guard', () => {
  const r = putClear()
  const eqLaw = r.law('M.sum() == total', ({M, total}) => M.sum().eq(total))
  const leLaw = r.law('M.sum() <= total', ({M, total}) => M.sum().atMost(total))
  const stepLaw = r.stepLaw('clear zeroes sum', (_b, a) => a.M.sum().eq(0), ({clears}) => clears)

  // Runtimes: put(id=1, val=2), clear(id=2) keeps M.sum() exact at 0.
  const m = r.withSumsOf(eqLaw).machine
  const it = interpret(m), js = loadJs(m), fs = fastStep(m)!
  let s1 = it.init({}), s2 = js.init({}), s3 = it.init({})
  for (const req of [{op: 0, id: 1, val: 2}, {op: 1, id: 2, val: 0}]) {
    s1 = it.step({}, s1, req); s2 = js.step({}, s2, req); s3 = fs({}, s3, req)
  }
  expect(s1.scalars['sum$M']).toBe(0)
  expect(s2.scalars['sum$M']).toBe(0)
  expect(s3.scalars['sum$M']).toBe(0)
  expect(s1.scalars.total).toBe(0)
  expect(r.crossCheck([eqLaw, leLaw], [stepLaw])).toEqual({checked: expect.any(Number)})
  expect(r.withMapSums()).toBeDefined()

  // Whole-map clear extracts a key-independent reset guard and proves cleanly across prover entry points.
  for (const v of [
    proveRule(r, [eqLaw], {search: false}),
    proveRule(r, [leLaw], {search: false}),
    proveSteps(r, [], [stepLaw], {search: false}),
    inferLaws(r, [eqLaw], [], {ms: 1500}),
  ]) {
    expect(v.proven && v.checked).toBe(true)
  }
})

test('Spark MemoryStore with clear: exact sums on putBlock+clear and proven via reset guard', () => {
  const r = sparkMemoryStore('with-clear')
  const sumLe = r.law('sum <= memoryUsed', ({Blocks, Unroll, memoryUsed}) =>
    Blocks.sum(b => when(b.present, b.size, 0)).plus(Unroll.sum()).atMost(memoryUsed))
  const sumEq = r.law('sum == memoryUsed', ({Blocks, Unroll, memoryUsed}) =>
    Blocks.sum(b => when(b.present, b.size, 0)).plus(Unroll.sum()).eq(memoryUsed))
  const blockLaw = r.law('every cached block size is covered by memoryUsed', ({Blocks, memoryUsed}) =>
    forall(b => Blocks.at(b).present.implies(Blocks.at(b).size.atMost(memoryUsed))))
  const unrollLaw = r.law('every task unroll allocation is covered by memoryUsed', ({Unroll, memoryUsed}) =>
    forall(t => Unroll.at(t).atMost(memoryUsed)))

  // Two-request reproducer from the frozen Spark model: putBlock(id=1, size=2), clear(id=2).
  const m = r.withSumsOf(sumLe).machine
  const it = interpret(m), js = loadJs(m), fs = fastStep(m)!
  const params = {poolSize: 10}
  const trace = [
    {op: 0, id: 1, size: 2, maxAcquisition: 10},
    {op: 4, id: 2, size: 0, maxAcquisition: 0},
  ]
  let a = it.init(params), b = js.init(params), c = it.init(params)
  for (const req of trace) {
    a = it.step(params, a, req); b = js.step(params, b, req); c = fs(params, c, req)
  }
  const sumNames = Object.keys(m.sums ?? {})
  expect(sumNames.length).toBe(2)
  for (const s of sumNames) {
    expect(a.scalars[s]).toBe(0)
    expect(b.scalars[s]).toBe(0)
    expect(c.scalars[s]).toBe(0)
  }
  expect(a.scalars.memoryUsed).toBe(0)
  expect(r.withMapSums()).toBeDefined()

  for (const v of [
    proveRule(r, [sumLe], {search: false}),
    proveRule(r, [sumEq], {search: false}),
    proveRule(r, [blockLaw], {search: {ms: 15_000}}),
    proveRule(r, [unrollLaw], {search: {ms: 15_000}}),
  ]) {
    expect(v.proven && v.checked).toBe(true)
  }
})

test('Spark MemoryStore control without clear: sum helper and cell laws still prove', () => {
  for (const mode of ['no-clear-set', 'no-clear-each'] as const) {
    const r = sparkMemoryStore(mode)
    const sumEq = r.law('sum == memoryUsed', ({Blocks, Unroll, memoryUsed}) =>
      Blocks.sum(b => when(b.present, b.size, 0)).plus(Unroll.sum()).eq(memoryUsed))
    const blockLaw = r.law('every cached block size is covered by memoryUsed', ({Blocks, memoryUsed}) =>
      forall(b => Blocks.at(b).present.implies(Blocks.at(b).size.atMost(memoryUsed))))
    const unrollLaw = r.law('every task unroll allocation is covered by memoryUsed', ({Unroll, memoryUsed}) =>
      forall(t => Unroll.at(t).atMost(memoryUsed)))
    const v = proveRule(r, [sumEq, blockLaw, unrollLaw], {search: false})
    expect(v.proven && v.checked).toBe(true)
  }
})

test('lower-bound dual: reachable violation gets true replayed refutation; rare violation is refused, never falsely proven', () => {
  // Reachable clear: genuinely false law gets a real refutation that replays on the original rule.
  const rReach = lowerBoundDual(false)
  const falseLower = rReach.law('hasPut <= M.sum()', ({hasPut, M}) => hasPut.atMost(M.sum()))
  const falseStep = rReach.stepLaw('clear preserves M.sum()', (b, a) => a.M.sum().eq(b.M.sum()), ({clears}) => clears)
  const vReach = proveRule(rReach, [falseLower], {search: false})
  expect(vReach.proven).toBe(false)
  expect(vReach.stuck).toBe('sat')
  expect(vReach.run).toBeDefined()
  expect(replayRefutation(rReach, [falseLower], [], vReach.run!.params, vReach.run!.trace as Record<string, number>[], 4, falseLower)).toBe(true)

  const vStepReach = proveSteps(rReach, [], [falseStep], {search: false})
  expect(vStepReach.proven).toBe(false)
  expect(vStepReach.run).toBeDefined()

  // Rare clear (outside random run bounds): NEVER falsely proven across any entry point; refused with unknown.
  const rRare = lowerBoundDual(true)
  const rareLower = rRare.law('hasPut <= M.sum()', ({hasPut, M}) => hasPut.atMost(M.sum()))
  const rareStep = rRare.stepLaw('clear preserves M.sum()', (b, a) => a.M.sum().eq(b.M.sum()), ({clears}) => clears)
  const rareLive = rRare.leadsTo('sum stays positive', {
    from: ({hasPut}) => hasPut.atLeast(1),
    to: ({M}) => M.sum().atLeast(1),
    rank: () => 0,
    helpful: () => ({op: 1, id: 999999}),
  })
  for (const v of [
    proveRule(rRare, [rareLower], {search: false}),
    proveRule(rRare, [rareLower], {search: {ms: 1500}}),
    proveRule(rRare, [rareLower], {search: false, fast: true}),
    proveRule(rRare, [rareLower], {search: false, from: 'any'}),
    proveSteps(rRare, [], [rareStep], {search: false}),
    proveLeadsTo(rRare, [rareLower], rareLive),
    inferLaws(rRare, [rareLower], [], {ms: 1500}),
  ]) {
    expect(v.proven).toBe(false)
    expect(v.checked).toBe(false)
    expect(v.stuck).toBe('unknown')
    expect(v.goal).toMatch(/@cover M/)
  }

  // Candidate seeds on uncovered broadcast sum are also refused cleanly.
  let seedStatus = ''
  const vSeed = proveRule(rRare, [rareLower], {
    search: {ms: 1500},
    candidateSeeds: {
      laws: [rareLower],
      report: audit => { seedStatus = audit.status },
    },
  })
  expect(vSeed.proven).toBe(false)
  expect(vSeed.stuck).toBe('unknown')
  expect(seedStatus).toBe('inconclusive')
})

test('step-reads-sum rule (law does not mention .sum()): exact runtimes and proven with reset guard', () => {
  const r = rule('step-reads-sum')
    .inputs({op: oneOf('put', 'clear', 'check'), id: nat})
    .state({cleared: 0, ok: 1})
    .maps({M: 0})
    .flags(({op, id, M}) => ({
      puts: op.is('put').and(M.at(id).eq(0)),
      clears: op.is('clear'),
      checks: op.is('check'),
    }))
    .step(({id, cleared, ok, M, puts, clears, checks}) => ({
      cleared: when(clears, 1, when(puts, 0, cleared)),
      ok: when(checks.and(cleared.eq(1)), when(M.sum().eq(0), 1, 0), ok),
      M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), 1, M.at(k)))),
    }))
  const okLaw = r.law('ok stays 1', ({ok}) => ok.eq(1))
  const clearedZero = r.law('cleared implies sum == 0', ({cleared, M}) => cleared.eq(1).implies(M.sum().eq(0)))

  const it = r.interpreter(), js = r.compiled()
  const trace = [{op: 0, id: 1}, {op: 1, id: 2}, {op: 2, id: 0}]
  let a = it.init({}), b = js.init({})
  for (const req of trace) {
    a = it.step({}, a, req); b = js.step({}, b, req)
  }
  expect(a.scalars.ok).toBe(1)
  expect(a.scalars['sum$M']).toBe(0)
  expect(b.scalars.ok).toBe(1)
  expect(b.scalars['sum$M']).toBe(0)

  const v = proveRule(r, [clearedZero, okLaw], {search: false})
  expect(v.proven && v.checked).toBe(true)
})

test('partial range broadcast and infinite broadcast (shift)', () => {
  // Partial broadcast: clears keys strictly below `limit`.
  const rPartial = rule('range-clear')
    .inputs({op: oneOf('put', 'clearBelow'), id: nat, val: nat, limit: nat})
    .maps({M: 0})
    .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clearBelow')}))
    .step(({id, val, limit, M, puts, clears}) => ({
      M: M.each(k => when(clears.and(k.lt(limit)), 0, when(puts.and(k.eq(id)), val, M.at(k)))),
    }))
  const nonNeg = rPartial.law('sum non-negative', ({M}) => M.sum().atLeast(0))
  const pm = rPartial.withSumsOf(nonNeg).machine
  const pit = interpret(pm), pjs = loadJs(pm), pfs = fastStep(pm)!
  let pa = pit.init({}), pb = pjs.init({}), pc = pit.init({})
  for (const req of [{op: 0, id: 1, val: 3, limit: 0}, {op: 0, id: 5, val: 7, limit: 0}, {op: 1, id: 0, val: 0, limit: 3}]) {
    pa = pit.step({}, pa, req); pb = pjs.step({}, pb, req); pc = pfs({}, pc, req)
  }
  expect(pa.scalars['sum$M']).toBe(7)
  expect(pb.scalars['sum$M']).toBe(7)
  expect(pc.scalars['sum$M']).toBe(7)
  const vp = proveRule(rPartial, [nonNeg], {search: false})
  expect(vp.proven).toBe(false)
  expect(vp.run).toBeUndefined()
  expect(vp.stuck).toBe('unknown')

  // Infinite broadcast: M[k] := M[k] + 1 makes the sum infinite after one step.
  const rShift = rule('shift-all')
    .maps({M: 0})
    .step(({M}) => ({M: M.each(k => M.at(k).plus(1))}))
  const shiftLaw = rShift.law('sum is 0', ({M}) => M.sum().eq(0))
  const sm = rShift.withSumsOf(shiftLaw).machine
  const sit = interpret(sm), sjs = loadJs(sm), sfs = fastStep(sm)!
  expect(() => sit.step({}, sit.init({}), {})).toThrow(/infinite/)
  expect(() => sjs.step({}, sjs.init({}), {})).toThrow(/infinite/)
  expect(() => sfs({}, sit.init({}), {})).toThrow(/infinite/)
  const vs = proveRule(rShift, [shiftLaw], {search: false})
  expect(vs.proven).toBe(false)
  expect(vs.run).toBeUndefined()
  expect(vs.stuck).toBe('unknown')
})

test('replayRefutation rejects bogus traces and accepts genuine original-rule violations', () => {
  const r = putClear()
  const eqLaw = r.law('M.sum() == total', ({M, total}) => M.sum().eq(total))
  // put(1, 2), clear(2) holds on the original rule (both M.sum() and total end at 0).
  expect(replayRefutation(r, [eqLaw], [], {}, [{op: 0, id: 1, val: 2}, {op: 1, id: 2, val: 0}], 4, eqLaw)).toBe(false)

  // On the lower-bound dual, put(1), clear(2) genuinely breaks hasPut <= M.sum().
  const d = lowerBoundDual(false)
  const falseLower = d.law('hasPut <= M.sum()', ({hasPut, M}) => hasPut.atMost(M.sum()))
  expect(replayRefutation(d, [falseLower], [], {}, [{op: 0, id: 1}, {op: 1, id: 2}], 4, falseLower)).toBe(true)

  // An input violating the rule's assumption is rejected by replayRefutation.
  const guarded = rule('guarded-put')
    .inputs({x: nat})
    .assume(({x}) => x.eq(0))
    .state({s: 0})
    .step(({x, s}) => ({s: s.plus(x)}))
  const zeroLaw = guarded.law('s == 0', ({s}) => s.eq(0))
  expect(replayRefutation(guarded, [zeroLaw], [], {}, [{x: 5}], 4, zeroLaw)).toBe(false)
})
