// Recursive datatypes as values (core/data.ts): the functions run as written, laws proven by cyclic proofs the search
// finds (checked again by the kernel), broken variants refused with a value that breaks them, a definition that isn't
// structural recursion refused, and a tampered proof refused by the kernel.
import {expect, test} from 'bun:test'
import {type Nat, type Val, data, define, evalX, law, mutual, natural, programOf, proveData, refute, schemesOf, self, showValue, showY} from './data.ts'
import {checkCyclic} from '../kernel/cyclic.ts'
import {Bag, Forest, List, Rose, Tree, app, broken, laws, len, mir, rev, sorted, ins} from '../examples/data.ts'

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

test('a mutual pair, a field of a datatype declared before, and recursion on a natural: the functions compute', () => {
  const t = Rose.node(1, Forest.cons(Rose.node(2, Forest.nil), Forest.cons(Rose.node(3, Forest.nil), Forest.nil)))
  const call = (fn: string, ...args: unknown[]) => ({x: {op: 'call', fn, args: args.map(a => (a as {x: unknown}).x ?? {op: 'nat', value: a})}})
  expect(run(call('rsum', t), {})).toBe(6)
  expect(run(call('rsize', t), {})).toBe(3)
  expect(showValue(List, run(call('rflat', t), {}) as never)).toBe('cons(1, cons(2, cons(3, nil)))')
  expect(showValue(Rose, run(call('rmirror', t), {}) as never)).toBe('node(1, cons(node(3, nil), cons(node(2, nil), nil)))')
  expect(run(call('lens', Bag.more(List.cons(1, List.nil), Bag.more(List.cons(2, List.cons(3, List.nil)), Bag.none))), {})).toBe(3)
  expect(showValue(List, run(call('replicate', 3, 7), {}) as never)).toBe('cons(7, cons(7, cons(7, nil)))')
  expect(showValue(List, run(call('take', 2, List.cons(1, List.cons(2, List.cons(3, List.nil)))), {}) as never)).toBe('cons(1, cons(2, nil))')
  expect(showValue(List, run(call('drop', 2, List.cons(1, List.cons(2, List.cons(3, List.nil)))), {}) as never)).toBe('cons(3, nil)')
})

test('a group with no value, and a ring of datatypes the bijection with the naturals does not take, are refused', () => {
  expect(() => mutual({Aa: {a: {b: 'Bb'}}, Bb: {b: {a: 'Aa'}}})).toThrow(/no value/)
  expect(() => mutual({Cc: {c: {d: 'Dd'}, c2: {e: 'Ee'}}, Dd: {d: {c: 'Cc'}, d2: {e: 'Ee'}}, Ee: {none: {}}})).toThrow(/ring/)
})

test('mutual recursion is checked across its ring, and a law on a rose tree gets its forest companion', () => {
  const {Rt, Fr} = mutual({Rt: {nd: {v: natural, ks: 'Fr'}}, Fr: {no: {}, more: {h: 'Rt', t: 'Fr'}}})
  const bad: ReturnType<typeof define> = define('badR', {t: Rt}, natural, ({t}) => (t as Val).match({nd: () => badF(Fr.no)}))
  const badF: ReturnType<typeof define> = define('badF', {ts: Fr}, natural, ({ts}) => (ts as Val).match({no: () => 0, more: ({h}) => (bad(h) as Nat).plus(1)}))
  expect(() => programOf([law('bad', {t: Rt}, ({t}) => (bad(t) as Nat).eq(0))])).toThrow(/structural/)
  const l = laws.roseSizeMirror(), s = schemesOf(programOf([l]), l).find(x => x.name === 'mutual structure of t')!
  expect(s.companions!.map(c => showY(c.law.holds))).toEqual(['fsize(fmirror(tForest)) = fsize(tForest)'])
})

test('laws over the new shapes: proven and checked by the kernel; their broken variants refused', () => {
  for (const l of [laws.bagLength(), laws.replicateLength()]) {
    const v = proveData(l)
    expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true)
  }
  for (const mk of [broken.roseSumFlatten, broken.roseSizeMirror, broken.bagLength, broken.replicateLength, broken.takeDrop, broken.bstInsertAny]) expect(proveData(mk()).counterexample).toBeDefined()
})
