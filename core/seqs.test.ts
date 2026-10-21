// Sequences as positions and a length (carriesSeq, carriesSeqs): the comparisons proven without induction, the encoding
// and the runtimes against plain arrays, and examples/scopes.ts's patterns against pi-fabric's covers.
import {expect, test} from 'bun:test'
import {everyBelow, nat, proveDecision, rule, when} from './dsl.ts'
import {comparePatterns, patternLaws} from '../examples/scopes.ts'

const seqs = rule('seqs').inputs({n: nat, x: nat}).carriesSeq('A', 'B', 'C').carriesSeqs('T')
const proven = (d: ReturnType<typeof seqs.decide>) => { const v = proveDecision(d); return v.proven && v.checked }

test('prefixes and equality, proven with no lemma; a false law refused', () => {
  expect(proven(seqs.decide('a prefix of a prefix is a prefix', ({A, B, C}) => [A.prefixOf(B), B.prefixOf(C)], ({A, C}) => A.prefixOf(C)))).toBe(true)
  expect(proven(seqs.decide('prefixes both ways are equal', ({A, B}) => [A.prefixOf(B), B.prefixOf(A)], ({A, B}) => A.equals(B)))).toBe(true)
  expect(proven(seqs.decide('an extension starts with what it extends', ({A, B}) => B.extends(A, 2), ({A, B}) => B.startsWith(A).and(B.len.eq(A.len.plus(2)))))).toBe(true)
  expect(proven(seqs.decide('what a prefix has, the longer one has', ({A, B, x}) => [A.prefixOf(B), A.has(x)], ({B, x}) => B.has(x)))).toBe(true)
  expect(proven(seqs.decide('a row read at its number', ({A, B, T, n}) => [T.row(n).startsWith(A), A.startsWith(B)], ({B, T, n}) => T.row(n).startsWith(B)))).toBe(true)
  expect(proven(seqs.decide('a prefix is the whole (false)', ({A, B}) => A.prefixOf(B), ({A, B}) => A.equals(B)))).toBe(false)
  expect(proven(seqs.decide('bookkeeping below a length', ({A, B, n}) => [everyBelow(A.len, k => A.at(k).eq(B.at(k))), n.lt(A.len)], ({A, B, n}) => A.at(n).eq(B.at(n))))).toBe(true)
})

test('a condition about every row may not compare the rows\' sequences (two keys at once)', () => {
  const d = seqs.decide('every row starts with A', ({A, T}) => [everyBelow(T.rows, r => T.row(r).startsWith(A))], ({A, T}) => T.row(0).startsWith(A))
  expect(() => proveDecision(d)).toThrow(/two keys at once/)
})

test('the encoding and the compiled rule against plain arrays', () => {
  const r = seqs.state({z: 0}).step(({A, B, T, n}) => ({z: when(A.prefixOf(B), 1, 0).plus(when(A.equals(B), 2, 0)).plus(when(T.row(n).startsWith(A), 4, 0))}))
  const enc = r.encodeInput({n: 1, x: 0, A: [1, 0, 2], B: [1, 0, 2, 3], C: [], T: [[5], [1, 0, 2, 9], []]})
  expect([enc.A_len, enc.C_len, enc.T_rows]).toEqual([3, 0, 3])
  expect([...(enc.A as Map<number, number>)]).toEqual([[0, 1], [2, 2]])
  expect([...(enc.T_base as Map<number, number>)]).toEqual([[1, 1], [2, 5]])
  const gen = r.compiled(), ps = r.encodeParams({})
  let x = 3
  const draw = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
  const arr = () => Array.from({length: draw(4)}, () => draw(3))
  const starts = (a: number[], b: number[]) => a.length <= b.length && a.every((y, i) => b[i] === y)
  for (let t = 0; t < 3000; t++) {
    const A = arr(), B = draw(2) ? [...A, ...arr()] : arr(), T = Array.from({length: 1 + draw(3)}, () => (draw(2) ? [...A, ...arr()] : arr())), n = draw(T.length)
    const z = r.decode(gen.step(ps, gen.init(ps), r.encodeInput({n, x: 0, A, B, C: [], T}))).z
    expect(z).toBe(Number(starts(A, B)) + 2 * Number(starts(A, B) && A.length === B.length) + 4 * Number(starts(A, T[n]!)))
  }
})

test('pi-fabric\'s patterns: covers as src/scope.ts writes it, its laws proven, a broken variant refused', () => {
  expect(comparePatterns(3000).failure).toBeUndefined()
  for (const d of patternLaws()) expect(proven(d as never)).toBe(true)
  expect(proven(patternLaws('lets /* cover /**')[0] as never)).toBe(false)
})
