// Unit tests for untrusted map-sum reset-guard extraction (core/sum-reset.ts).
// Purely tests the untrusted extractor without depending on any trusted kernel change.
import {expect, test} from 'bun:test'
import {bool, choose, nat, no, oneOf, record, rule, when, yes} from './dsl.ts'
import {type C, type Machine, type Sum} from './machine.ts'
import {extractSumReset, isAdmissibleResetGuard, sumResets} from './sum-reset.ts'

const Block = record({present: bool, size: nat})

const sparkMemoryStore = () => rule('Spark MemoryStore')
  .params({poolSize: nat})
  .inputs({op: oneOf('putBlock', 'removeBlock', 'reserveUnroll', 'releaseUnroll', 'clear'), id: nat, size: nat, maxAcquisition: nat})
  .state({memoryUsed: 0})
  .maps({Blocks: Block.from({present: false, size: 0}), Unroll: 0})
  .flags(({op, id, size, maxAcquisition, poolSize, memoryUsed, Blocks, Unroll}) => ({
    puts: op.is('putBlock').and(Blocks.at(id).present.not(), size.atMost(maxAcquisition), memoryUsed.plus(size).atMost(poolSize)),
    removes: op.is('removeBlock').and(Blocks.at(id).present),
    reservesUnroll: op.is('reserveUnroll').and(size.atMost(maxAcquisition), memoryUsed.plus(size).atMost(poolSize)),
    releasesUnroll: op.is('releaseUnroll').and(Unroll.at(id).gt(0)),
    clears: op.is('clear'),
  }))
  .step(({id, size, memoryUsed, Blocks, Unroll, puts, removes, reservesUnroll, releasesUnroll, clears}) => {
    const b = Blocks.at(id), u = Unroll.at(id), relU = when(size.atMost(u), size, u)
    return {
      memoryUsed: when(clears, 0,
        when(puts.or(reservesUnroll), memoryUsed.plus(size),
          when(removes, memoryUsed.minus(b.size),
            when(releasesUnroll, memoryUsed.minus(relU), memoryUsed)))),
      Blocks: Blocks.each(k => ({
        present: choose(clears, no, choose(puts.and(k.eq(id)), yes, choose(removes.and(k.eq(id)), no, Blocks.at(k).present))),
        size: when(clears, 0, when(puts.and(k.eq(id)), size, when(removes.and(k.eq(id)), 0, Blocks.at(k).size))),
      })),
      Unroll: Unroll.each(k => when(clears, 0,
        when(reservesUnroll.and(k.eq(id)), Unroll.at(k).plus(size),
          when(releasesUnroll.and(k.eq(id)), Unroll.at(k).minus(relU), Unroll.at(k))))),
    }
  })

test('extracts reset guard from put-clear and Spark MemoryStore (both Blocks and Unroll sums)', () => {
  const putClear = rule('put-clear')
    .inputs({op: oneOf('put', 'clear'), id: nat, val: nat})
    .state({total: 0})
    .maps({M: 0})
    .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clear')}))
    .step(({id, val, total, M, puts, clears}) => ({
      total: when(clears, 0, when(puts, total.plus(val), total)),
      M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), val, M.at(k)))),
    }))
  const eqLaw = putClear.law('M.sum() == total', ({M, total}) => M.sum().eq(total))
  const pcResets = sumResets(putClear.withSumsOf(eqLaw).machine)
  expect(pcResets['sum$M']).toEqual({op: 'flag', name: 'clears'})

  const spark = sparkMemoryStore()
  const sumLaw = spark.law('sum == memoryUsed', ({Blocks, Unroll, memoryUsed}) =>
    Blocks.sum(b => when(b.present, b.size, 0)).plus(Unroll.sum()).eq(memoryUsed))
  const sm = spark.withSumsOf(sumLaw).machine
  const resets = sumResets(sm)
  const sumNames = Object.keys(sm.sums ?? {})
  expect(sumNames).toHaveLength(2)
  for (const name of sumNames) expect(resets[name]).toEqual({op: 'flag', name: 'clears'})
})

test('extracts reset from inverted branch, chained resets, filtered single-field clear, non-zero zeroing const, and multi-map conjunction', () => {
  // Inverted branch: when(!clears, ..., 0)
  const inv = rule('inverted-clear')
    .inputs({op: oneOf('put', 'clear'), id: nat, val: nat})
    .maps({M: 0})
    .flags(({op}) => ({puts: op.is('put'), clears: op.is('clear')}))
    .step(({id, val, M, puts, clears}) => ({
      M: M.each(k => when(clears.not(), when(puts.and(k.eq(id)), val, M.at(k)), 0)),
    }))
  const invLaw = inv.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(inv.withSumsOf(invLaw).machine)['sum$M']).toEqual({op: 'flag', name: 'clears'})

  // Chained resets: when(r1, 0, when(r2, 0, ...)) -> r1 ∨ r2
  const chained = rule('chained-clear')
    .inputs({op: oneOf('put', 'flush', 'reset'), id: nat, val: nat})
    .maps({M: 0})
    .flags(({op}) => ({puts: op.is('put'), flushes: op.is('flush'), resets: op.is('reset')}))
    .step(({id, val, M, puts, flushes, resets}) => ({
      M: M.each(k => when(flushes, 0, when(resets, 0, when(puts.and(k.eq(id)), val, M.at(k))))),
    }))
  const chLaw = chained.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(chained.withSumsOf(chLaw).machine)['sum$M']).toEqual({
    op: 'or',
    xs: [{op: 'flag', name: 'flushes'}, {op: 'flag', name: 'resets'}],
  })

  // Filtered record sum where only `present` clears to false (size stays via set)
  const presentOnly = rule('present-only-clear')
    .inputs({op: oneOf('put', 'clear'), id: nat, size: nat})
    .maps({Blocks: Block.from({present: false, size: 0})})
    .flags(({op}) => ({puts: op.is('put'), clears: op.is('clear')}))
    .step(({id, size, Blocks, puts, clears}) => ({
      Blocks: Blocks.each(k => ({
        present: choose(clears, no, choose(puts.and(k.eq(id)), yes, Blocks.at(k).present)),
        size: when(puts.and(k.eq(id)), size, Blocks.at(k).size),
      })),
    }))
  const poLaw = presentOnly.law('s', ({Blocks}) => Blocks.sum(b => when(b.present, b.size, 0)).atLeast(0))
  const poM = presentOnly.withSumsOf(poLaw).machine
  const poName = Object.keys(poM.sums!)[0]!
  expect(sumResets(poM)[poName]).toEqual({op: 'flag', name: 'clears'})

  // Bool map cleared with choose(clears, no, ...)
  const boolClear = rule('bool-clear')
    .inputs({op: oneOf('take', 'clear'), id: nat})
    .maps({Holds: bool.from(false)})
    .flags(({op}) => ({takes: op.is('take'), clears: op.is('clear')}))
    .step(({id, Holds, takes, clears}) => ({
      Holds: Holds.each(k => choose(clears, no, choose(takes.and(k.eq(id)), yes, Holds.at(k)))),
    }))
  const bcLaw = boolClear.law('s', ({Holds}) => Holds.sum(c => c.n).atLeast(0))
  const bcM = boolClear.withSumsOf(bcLaw).machine
  const bcName = Object.keys(bcM.sums!)[0]!
  expect(sumResets(bcM)[bcName]).toEqual({op: 'flag', name: 'clears'})

  // Non-zero constant reset: state map resets to 1 ('idle'), summand counts cells at 0 ('active')
  const nonZeroConst: Machine = {
    name: 'nonzero-const-reset',
    params: [],
    inputs: ['op', 'id'],
    state: {},
    maps: {St: 1, Val: 0},
    step: {
      maps: {
        St: {
          each: 'k$w',
          value: {
            op: 'if',
            c: {op: '=', a: {op: 'var', name: 'op'}, b: {op: 'const', value: 1}},
            then: {op: 'const', value: 1},
            else: {op: 'get', map: 'St', key: {op: 'var', name: 'k$w'}},
          },
        },
      },
    },
  }
  const activeSum: Sum = {
    key: 'k$S',
    term: {
      op: 'if',
      c: {op: '=', a: {op: 'get', map: 'St', key: {op: 'var', name: 'k$S'}}, b: {op: 'const', value: 0}},
      then: {op: 'get', map: 'Val', key: {op: 'var', name: 'k$S'}},
      else: {op: 'const', value: 0},
    },
  }
  expect(extractSumReset(nonZeroConst, activeSum, 'S')).toEqual({
    op: '=', a: {op: 'var', name: 'op'}, b: {op: 'const', value: 1},
  })

  // Multi-map additive sum M1[k] + M2[k] where M1 clears on r1 and M2 clears on r2 -> r1 ∧ r2
  const twoMaps: Machine = {
    name: 'two-map-reset',
    params: [],
    inputs: ['r1', 'r2'],
    state: {},
    maps: {M1: 0, M2: 0},
    step: {
      maps: {
        M1: {each: 'k1', value: {op: 'if', c: {op: '=', a: {op: 'var', name: 'r1'}, b: {op: 'const', value: 1}}, then: {op: 'const', value: 0}, else: {op: 'get', map: 'M1', key: {op: 'var', name: 'k1'}}}},
        M2: {each: 'k2', value: {op: 'if', c: {op: '=', a: {op: 'var', name: 'r2'}, b: {op: 'const', value: 1}}, then: {op: 'const', value: 0}, else: {op: 'get', map: 'M2', key: {op: 'var', name: 'k2'}}}},
      },
    },
  }
  const addSum: Sum = {
    key: 'k$S',
    term: {op: 'add', a: {op: 'get', map: 'M1', key: {op: 'var', name: 'k$S'}}, b: {op: 'get', map: 'M2', key: {op: 'var', name: 'k$S'}}},
  }
  expect(extractSumReset(twoMaps, addSum, 'S')).toEqual({
    op: 'and',
    xs: [
      {op: '=', a: {op: 'var', name: 'r1'}, b: {op: 'const', value: 1}},
      {op: '=', a: {op: 'var', name: 'r2'}, b: {op: 'const', value: 1}},
    ],
  })
})

test('refuses extraction for all 4 mutant classes: key-dependent guard, partial wipe, reset-that-writes, and guard reading summed cells', () => {
  // 1. Key-dependent guard (k < limit)
  const keyDep = rule('key-dependent')
    .inputs({id: nat, limit: nat})
    .maps({M: 0})
    .step(({limit, M}) => ({M: M.each(k => when(k.lt(limit), 0, M.at(k)))}))
  const kdLaw = keyDep.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(keyDep.withSumsOf(kdLaw).machine)['sum$M']).toBeUndefined()

  // 2. Partial wipe (clears && k < limit)
  const partial = rule('partial-wipe')
    .inputs({op: oneOf('put', 'clearBelow'), id: nat, val: nat, limit: nat})
    .maps({M: 0})
    .flags(({op}) => ({puts: op.is('put'), clears: op.is('clearBelow')}))
    .step(({id, val, limit, M, puts, clears}) => ({
      M: M.each(k => when(clears.and(k.lt(limit)), 0, when(puts.and(k.eq(id)), val, M.at(k)))),
    }))
  const partLaw = partial.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(partial.withSumsOf(partLaw).machine)['sum$M']).toBeUndefined()

  // 3a. Reset that also writes (single map: clears writes val at id, 0 elsewhere)
  const resetWrites1 = rule('reset-also-writes-single')
    .inputs({op: oneOf('put', 'clearAndWrite'), id: nat, val: nat})
    .maps({M: 0})
    .flags(({op}) => ({puts: op.is('put'), clears: op.is('clearAndWrite')}))
    .step(({id, val, M, puts, clears}) => ({
      M: M.each(k => when(clears, when(k.eq(id), val, 0), when(puts.and(k.eq(id)), val, M.at(k)))),
    }))
  const rw1Law = resetWrites1.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(resetWrites1.withSumsOf(rw1Law).machine)['sum$M']).toBeUndefined()

  // 3b. Reset that also writes (two-map sum M1[k] + M2[k]: M1 clears, M2 writes via set)
  const resetWrites2: Machine = {
    name: 'reset-also-writes-two-maps',
    params: [],
    inputs: ['op', 'id', 'val'],
    state: {},
    maps: {M1: 0, M2: 0},
    step: {
      maps: {
        M1: {each: 'k1', value: {op: 'if', c: {op: '=', a: {op: 'var', name: 'op'}, b: {op: 'const', value: 1}}, then: {op: 'const', value: 0}, else: {op: 'get', map: 'M1', key: {op: 'var', name: 'k1'}}}},
        M2: {key: {op: 'var', name: 'id'}, value: {op: 'var', name: 'val'}},
      },
    },
  }
  const addSum: Sum = {
    key: 'k$S',
    term: {op: 'add', a: {op: 'get', map: 'M1', key: {op: 'var', name: 'k$S'}}, b: {op: 'get', map: 'M2', key: {op: 'var', name: 'k$S'}}},
  }
  expect(extractSumReset(resetWrites2, addSum, 'S')).toBeUndefined()

  // 4a. Guard reading summed cell at bound key (M[k] == 1)
  const cellAtKey = rule('reads-cell-at-key')
    .inputs({op: oneOf('put', 'clearOnes'), id: nat, val: nat})
    .maps({M: 0})
    .flags(({op}) => ({puts: op.is('put'), clears: op.is('clearOnes')}))
    .step(({id, val, M, puts, clears}) => ({
      M: M.each(k => when(clears.and(M.at(k).eq(1)), 0, when(puts.and(k.eq(id)), val, M.at(k)))),
    }))
  const ckLaw = cellAtKey.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(cellAtKey.withSumsOf(ckLaw).machine)['sum$M']).toBeUndefined()

  // 4b. Guard reading summed cell at request key via flag (lowerBoundDual pattern: op == clear && M[id] == 0)
  const cellViaFlag = rule('reads-cell-via-flag')
    .inputs({op: oneOf('put', 'clear'), id: nat})
    .maps({M: 0})
    .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clear').and(M.at(id).eq(0))}))
    .step(({id, M, puts, clears}) => ({
      M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), 1, M.at(k)))),
    }))
  const cfLaw = cellViaFlag.law('s', ({M}) => M.sum().atLeast(0))
  const cfM = cellViaFlag.withSumsOf(cfLaw).machine
  expect(sumResets(cfM)['sum$M']).toBeUndefined()
  expect(isAdmissibleResetGuard(cfM, cfM.sums!['sum$M']!, {op: 'flag', name: 'clears'}, 'sum$M')).toBe(false)

  // 4c. Guard reading summed cell through chained flags (f1 = M[id] == 0, f2 = op == clear && f1)
  const chainedFlag = rule('reads-cell-via-chained-flag')
    .inputs({op: oneOf('put', 'clear'), id: nat})
    .maps({M: 0})
    .flags(({op, id, M}) => ({zeroAtId: M.at(id).eq(0), clears: op.is('clear')}))
    .step(({id, M, zeroAtId, clears}) => ({
      M: M.each(k => when(clears.and(zeroAtId), 0, when(k.eq(id), 1, M.at(k)))),
    }))
  const chfLaw = chainedFlag.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(chainedFlag.withSumsOf(chfLaw).machine)['sum$M']).toBeUndefined()

  // 4d. Direct admissibility check rejects key variables (sum.key, x$S, w.each), undeclared vars, and quantifiers
  const m = cfM
  const sum = m.sums!['sum$M']!
  const eachKey = (m.step.maps!.M! as {each: string}).each
  for (const bad of [
    {op: '=', a: {op: 'var', name: sum.key}, b: {op: 'const', value: 0}},
    {op: '=', a: {op: 'var', name: 'x$sum$M'}, b: {op: 'const', value: 0}},
    {op: '=', a: {op: 'var', name: eachKey}, b: {op: 'const', value: 0}},
    {op: '=', a: {op: 'var', name: 'undeclared'}, b: {op: 'const', value: 0}},
    {op: '=', a: {op: 'get', map: 'M', key: {op: 'var', name: 'id'}}, b: {op: 'const', value: 0}},
    {op: 'flag', name: 'cells$sum$M'},
    {op: 'all', key: 'q$0', c: {op: '=', a: {op: 'get', map: 'M', key: {op: 'var', name: 'q$0'}}, b: {op: 'const', value: 0}}},
  ] as C[]) {
    expect(isAdmissibleResetGuard(m, sum, bad, 'sum$M'), JSON.stringify(bad)).toBe(false)
  }
})

test('returns undefined when no summed map uses an each write', () => {
  const setOnly = rule('set-only')
    .inputs({id: nat, val: nat})
    .maps({M: 0})
    .step(({id, val, M}) => ({M: M.set(id, val)}))
  const law = setOnly.law('s', ({M}) => M.sum().atLeast(0))
  expect(sumResets(setOnly.withSumsOf(law).machine)['sum$M']).toBeUndefined()
})
