// Trusted kernel tests & mutant battery for SumDecl.reset (`kernel/kernel.ts` sumMachine + `lean-kernel/emit.ts`).
// Verifies:
//   - Positive whole-map reset proofs (put-clear, plain/chained flags)
//   - Rejection of all 4 mutant classes:
//       1. Key-dependent reset guard (sum.key, cover key x$S, write key w.each)
//       2. Partial wipe under reset (k < limit, k != 0)
//       3. Reset that also writes (single-map and two-map summand)
//       4. Reset guard reading summed cells (at key, at input id, via plain flag, via chained flag)
//   - Rejection of certificate & declaration tampers (dropped @reset tree, dropped reset decl, swapped guard)
//   - Lean export shape (some reset decl, paired (coverTrees, some resetTree) certs, tamper checks)
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine} from '../core/machine.ts'
import {check, checkLaws, sumMachine, trueC} from './kernel.ts'
import {proveLaws} from './prove.ts'
import {retainedSumMachineToLean, smachineToLean} from '../lean-kernel/emit.ts'

const v = (name: string): E => ({op: 'var', name})
const k = (value: number): E => ({op: 'const', value})
const eq = (a: E, b: E): C => ({op: '=', a, b})
const lt = (a: E, b: E): C => ({op: '<', a, b})
const and2 = (a: C, b: C): C => ({op: 'and', xs: [a, b]})
const ite = (c: C, then: E, otherwise: E): E => ({op: 'if', c, then, else: otherwise})
const get = (map: string, key: E): E => ({op: 'get', map, key})

const sumAnswer = (m: Machine, laws: Law[], proof: {instances: Record<string, Record<string, E[]>>, trees: Record<string, import('./kernel.ts').Tree>}): boolean => {
  try {
    const {machine, goals} = sumMachine(m, undefined, laws)
    return goals.every(g => proof.trees[g.name] !== undefined && check(g, proof.trees[g.name]!)) && checkLaws(machine, laws, proof)
  } catch {
    return false
  }
}

const baseM: Machine = {
  name: 'reset-mutant-base',
  params: [],
  inputs: ['op', 'id', 'val', 'limit'],
  state: {S: k(0), total: k(0)},
  maps: {M: 0},
  step: {
    flags: {
      puts: and2(eq(v('op'), k(0)), eq(get('M', v('id')), k(0))),
      clears: eq(v('op'), k(1)),
      clearsReadingM: and2(eq(v('op'), k(1)), eq(get('M', v('id')), k(0))),
      zeroAtId: eq(get('M', v('id')), k(0)),
      chainedReadingM: and2(eq(v('op'), k(1)), {op: 'flag', name: 'zeroAtId'}),
      chainedClears: and2({op: 'flag', name: 'clears'}, {op: '<=', a: v('op'), b: k(1)}),
    },
    state: {
      total: ite({op: 'flag', name: 'clears'}, k(0), ite({op: 'flag', name: 'puts'}, {op: 'add', a: v('total'), b: v('val')}, v('total'))),
    },
    maps: {
      M: {
        each: 'k$w',
        value: ite({op: 'flag', name: 'clears'}, k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w')))),
      },
    },
  },
  assume: {op: '<=', a: v('op'), b: k(1)},
  sums: {S: {key: 'k$S', term: get('M', v('k$S')), reset: {op: 'flag', name: 'clears'}}},
}

const baseLaws: Law[] = [
  {name: 'S == total', holds: eq(v('S'), v('total'))},
  {name: 'every cell <= total', forall: 'k$l', holds: {op: '<=', a: get('M', v('k$l')), b: v('total')}},
]

const withReset = (reset: C | undefined): Machine => ({
  ...baseM,
  sums: {S: {key: 'k$S', term: get('M', v('k$S')), ...(reset ? {reset} : {})}},
})

const withWrite = (value: E): Machine => ({
  ...baseM,
  step: {...baseM.step, maps: {M: {each: 'k$w', value}}},
})

test('whole-map reset proves @reset and @cover under ¬reset, and exports cleanly to Lean', () => {
  const res = proveLaws(baseM, baseLaws)
  expect(res.proven && res.checked && !!res.proof).toBe(true)
  expect(res.proof!.trees['S @reset']).toBeDefined()
  expect(res.proof!.trees['S @cover M']).toBeDefined()
  expect(sumAnswer(baseM, baseLaws, res.proof!)).toBe(true)

  // Chained plain-flag reset guard also proves and checks.
  const chainedM: Machine = {
    ...baseM,
    sums: {S: {key: 'k$S', term: get('M', v('k$S')), reset: {op: 'flag', name: 'chainedClears'}}},
  }
  const chainedRes = proveLaws(chainedM, baseLaws)
  expect(chainedRes.proven && chainedRes.checked).toBe(true)

  // Retained Lean export includes `some (...)` reset guard and paired `(coverTrees, some resetTree)` cert.
  const lean = retainedSumMachineToLean('putclear', baseM, baseLaws, res.proof!, {})
  expect(lean).toContain('def putclear_sums : SumMachine :=')
  expect(lean).toContain('some (')
  expect(lean).toContain('def putclear_covers : List (List (List VDef × Tree) × Option (List VDef × Tree)) :=')
  expect(lean).toContain('theorem putclear_scheck : checkSums putclear_sums putclear_proof putclear_covers = true')
})

test('mutant battery refuses all 4 unsound reset classes and certificate tampers', () => {
  const baseRes = proveLaws(baseM, baseLaws)
  expect(baseRes.proven && baseRes.checked && !!baseRes.proof).toBe(true)
  const validProof = baseRes.proof!

  // Class 1: key-dependent reset guards (must throw in sumMachine)
  for (const [label, guard] of [
    ['M1 sum.key (k$S < limit)', lt(v('k$S'), v('limit'))],
    ['M2 cover key (x$S < limit)', lt(v('x$S'), v('limit'))],
    ['M3 write key (k$w < limit)', lt(v('k$w'), v('limit'))],
  ] as const) {
    const m = withReset(guard)
    expect(() => sumMachine(m, undefined, baseLaws), label).toThrow(/reset guard reads a (key|write key)/)
    expect(sumAnswer(m, baseLaws, validProof), label).toBe(false)
  }

  const trivialLaw: Law[] = [{name: 'nonneg', holds: {op: '<=', a: k(0), b: v('S')}}]

  // Class 2: partial wipes (S @reset fails even on a trivial law; valid base proof rejected)
  for (const [label, value] of [
    ['M4 partial wipe (clears && k < limit)', ite(and2({op: 'flag', name: 'clears'}, lt(v('k$w'), v('limit'))), k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))],
    ['M5 partial wipe (clears && k != 0)', ite(and2({op: 'flag', name: 'clears'}, {op: 'not', x: eq(v('k$w'), k(0))}), k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))],
  ] as const) {
    const m = withWrite(value)
    expect(sumAnswer(m, baseLaws, validProof), label).toBe(false)
    expect(proveLaws(m, baseLaws).proven, label).toBe(false)
    const rt = proveLaws(m, trivialLaw)
    expect(rt.proven, label).toBe(false)
    expect(rt.failed?.goal, label).toBe('S @reset')
  }

  // Class 3: reset that also writes (single-map & two-map)
  const m6 = withWrite(ite({op: 'flag', name: 'clears'}, ite(eq(v('k$w'), v('id')), v('val'), k(0)), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w')))))
  expect(sumAnswer(m6, baseLaws, validProof)).toBe(false)
  expect(proveLaws(m6, baseLaws).proven).toBe(false)
  const r6 = proveLaws(m6, trivialLaw)
  expect(r6.proven).toBe(false)
  expect(r6.failed?.goal).toBe('S @reset')

  const m7: Machine = {
    name: 'M7-two-map-reset-also-writes',
    params: [],
    inputs: ['op', 'id', 'val'],
    state: {S: k(0)},
    maps: {M: 0, U: 0},
    step: {
      flags: {puts: eq(v('op'), k(0)), clears: eq(v('op'), k(1))},
      maps: {
        M: {each: 'k$w', value: ite({op: 'flag', name: 'clears'}, k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))},
        U: {key: v('id'), value: v('val')},
      },
    },
    assume: {op: '<=', a: v('op'), b: k(1)},
    sums: {S: {key: 'k$S', term: {op: 'add', a: get('M', v('k$S')), b: get('U', v('k$S'))}, reset: {op: 'flag', name: 'clears'}}},
  }
  const r7 = proveLaws(m7, [{name: 'nonneg', holds: {op: '<=', a: k(0), b: v('S')}}])
  expect(r7.proven).toBe(false)
  expect(r7.failed?.goal).toBe('S @reset')

  // Class 4: reset guard reading summed cells (at key, directly at id, via plain flag, via chained flag)
  for (const [label, guard, pattern] of [
    ['M8 M[k$S] = 1', eq(get('M', v('k$S')), k(1)), /key variable/],
    ['M9 op = 1 && M[id] = 0', and2(eq(v('op'), k(1)), eq(get('M', v('id')), k(0))), /summed map/],
    ['M10 plain flag clearsReadingM', {op: 'flag', name: 'clearsReadingM'} as C, /summed map/],
    ['M11 chained flag chainedReadingM', {op: 'flag', name: 'chainedReadingM'} as C, /summed map/],
  ] as const) {
    const m = withReset(guard)
    expect(() => sumMachine(m, undefined, baseLaws), label).toThrow(pattern)
    expect(sumAnswer(m, baseLaws, validProof), label).toBe(false)
  }

  // Class 5: certificate & declaration tampers
  const droppedTrees = {...validProof.trees}
  delete droppedTrees['S @reset']
  expect(checkLaws(baseM, baseLaws, {...validProof, trees: droppedTrees})).toBe(false)
  expect(sumAnswer(withReset(undefined), baseLaws, validProof)).toBe(false)
  expect(sumAnswer(withReset({op: 'flag', name: 'puts'}), baseLaws, validProof)).toBe(false)
  expect(sumAnswer(withReset(trueC), baseLaws, validProof)).toBe(false)
  expect(proveLaws(withReset(trueC), baseLaws).proven).toBe(false)

  // Lean tamper exporter emits false checks for tampers without throwing.
  const leanTampers = [
    {what: 'M1 key-dependent', m: withReset(lt(v('k$S'), v('limit'))), expect: false},
    {what: 'M4 partial wipe', m: withWrite(ite(and2({op: 'flag', name: 'clears'}, lt(v('k$w'), v('limit'))), k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))), expect: false},
    {what: 'M6 reset also writes', m: m6, expect: false},
    {what: 'M10 plain flag reading summed map', m: withReset({op: 'flag', name: 'clearsReadingM'}), expect: false},
    {what: 'M12b reset dropped', m: withReset(undefined), expect: false},
  ]
  const exported = smachineToLean('mutbase', baseM, baseLaws, {sumTampers: leanTampers, coverTrees: validProof.trees, noFacts: true})
  expect((exported.match(/= false := by decide \+kernel/g) ?? []).length).toBe(leanTampers.length)
})

test('undeclared flag or negative constant in reset guard is refused', () => {
  expect(() => sumMachine(withReset({op: 'flag', name: 'noSuchFlag'}), undefined, baseLaws)).toThrow(/undeclared flag/)
  expect(() => sumMachine(withReset({op: '<=', a: {op: 'const', value: -1}, b: k(0)}), undefined, baseLaws)).toThrow(/negative/)
})
