// Recursive datatypes as values (core/data.ts): the functions run as written, laws proven by cyclic proofs the search
// finds (checked again by the kernel), broken variants refused with a value that breaks them, a definition that isn't
// structural recursion refused, and a tampered proof refused by the kernel.
import {expect, test} from 'bun:test'
import {type Val, data, define, evalX, law, natural, proveData, refute, self, showValue} from './data.ts'
import {checkCyclic} from '../kernel/cyclic.ts'
import {List, Tree, app, broken, laws, len, mir, rev, sorted, ins} from '../examples/data.ts'

const list = (...xs: number[]): {c: number, f: unknown[]} => xs.reduceRight<{c: number, f: unknown[]}>((t, h) => ({c: 1, f: [h, t]}), {c: 0, f: []})
const run = (call: {x: unknown}, env: Record<string, unknown>) => evalX(call.x as never, new Map(Object.entries(env)) as never, {})

test('the functions compute what they say', () => {
  const xs = list(1, 2, 3), ys = list(4)
  expect(showValue(List, run(app(List.cons(1, List.cons(2, List.nil)), List.cons(3, List.nil)) as never, {}) as never)).toBe('cons(1, cons(2, cons(3, nil)))')
  expect(run({x: {op: 'call', fn: 'len', args: [{op: 'var', name: 'xs'}]}}, {xs})).toBe(3)
  expect(showValue(List, run({x: {op: 'call', fn: 'reverse', args: [{op: 'var', name: 'xs'}]}}, {xs}) as never)).toBe('cons(3, cons(2, cons(1, nil)))')
  expect(showValue(List, run({x: {op: 'call', fn: 'insert', args: [{op: 'nat', value: 2}, {op: 'var', name: 'xs'}]}}, {xs}) as never)).toBe('cons(1, cons(2, cons(2, cons(3, nil))))')
  expect(run({x: {op: 'call', fn: 'sorted', args: [{op: 'var', name: 'ys'}]}}, {ys})).toBe(1)
  void len; void rev; void sorted; void ins; void mir; void Tree
})

test('laws with no lemma: proven, and checked by the kernel', () => {
  for (const l of [laws.lengthAppend(), laws.lengthMap(), laws.sizeMirror(), laws.insertLength()]) {
    const v = proveData(l)
    expect(v.proven && v.checked).toBe(true)
    expect(v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true)
  }
})

test('broken variants are refused with a value that breaks them', () => {
  for (const mk of Object.values(broken)) {
    const v = proveData(mk())
    expect(v.proven).toBe(false)
    expect(v.counterexample).toBeDefined()
  }
  expect(refute(laws.lengthAppend())).toBeUndefined()
})

test('a tampered proof is refused: a use read at the node itself (no descent)', () => {
  const v = proveData(laws.lengthAppend())
  if (!v.proof?.proven) throw new Error('not proven')
  const p = v.proof.proof, i = p.nodes.findIndex(n => n.uses.some(u => Object.keys(u.subst).length))
  const tampered = {...p, nodes: p.nodes.map((n, j) => (j !== i ? n : {...n, uses: n.uses.map(u => ({...u, subst: Object.fromEntries(Object.keys(u.subst).map(x => [x, {op: 'var' as const, name: x}]))}))}))}
  expect(checkCyclic(tampered)).toBe(false)
})

test('a definition that is not structural recursion is refused', () => {
  const L = data('Lst', {none: {}, more: {item: natural, rest: self}})
  const bad = define('bad', {xs: L}, natural, ({xs}) => (xs as Val).match({none: () => 0, more: () => bad(xs)}))
  expect(() => proveData(law('bad', {xs: L}, ({xs}) => bad(xs).eq(0)))).toThrow(/structural/)
})
