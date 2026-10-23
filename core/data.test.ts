// Recursive datatypes as values (core/data.ts): the functions run as written, laws proven by cyclic proofs the search
// finds (checked again by the kernel), broken variants refused with a value that breaks them, a definition that isn't
// structural recursion refused unless its termination is proven (a measure every call lowers, each call's obligation
// proven by the kernel), and a tampered proof refused by the kernel.
import {expect, test} from 'bun:test'
import {type Bool, type Nat, type Val, EvalLimit, conjectures, data, define, evalX, law, mutual, natural, programOf, proveData, refute, schemesOf, self, showValue, showY, when} from './data.ts'
import {checkCyclic} from '../kernel/cyclic.ts'
import {transferPlan} from './transfer.ts'
import {Bag, Forest, List, Rose, Tree, a3, app, broken, drp, ilv, laws, leq, len, merge, mir, mrg, nonterminating, qsort, refusal, rev, same, sorted, ins, through as through_, throughBroken} from '../examples/data.ts'

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

// (the rose and bag laws take seconds: examples/data.ts proves them)
test('laws over the new shapes: proven and checked by the kernel; their broken variants refused', () => {
  for (const l of [laws.replicateLength()]) {
    const v = proveData(l)
    expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true)
  }
  for (const mk of [broken.roseSumFlatten, broken.roseSizeMirror, broken.bagLength, broken.replicateLength, broken.takeDrop, broken.bstInsertAny]) expect(proveData(mk()).counterexample).toBeDefined()
})

test('well-founded recursion: a measure found, and each call proven to lower it (every obligation checked by the kernel)', () => {
  for (const [f, text] of [[mrg, '(size(xs), size(ys))'], [ilv, 'size(xs) + size(ys)'], [a3, '(x, y)'], [qsort, 'size(xs)'], [merge('stated'), 'size(xs) + size(ys)']] as const) {
    const t = f.fn.termination!
    expect(t.text).toBe(text)
    expect(t.obligations.length).toBeGreaterThan(0)
    for (const o of t.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
  }
  // qsort's calls are on filters of the tail: each obligation by the filter's own recursion
  expect(qsort.fn.termination!.obligations.map(o => o.scheme)).toEqual([expect.stringMatching(/^recursion of atMost/), expect.stringMatching(/^recursion of above/)])
  expect(showValue(List, run({x: {op: 'call', fn: 'qsort', args: [{op: 'var', name: 'xs'}]}}, {xs: list(3, 1, 2, 1)}) as never)).toBe('cons(1, cons(1, cons(2, cons(3, nil))))')
  expect(showValue(List, run({x: {op: 'call', fn: 'merge', args: [{op: 'var', name: 'xs'}, {op: 'var', name: 'ys'}]}}, {xs: list(1, 4), ys: list(2, 3)}) as never)).toBe('cons(1, cons(2, cons(3, cons(4, nil))))')
}, 60_000)

test('a definition that does not terminate is refused with its reason, and no law about it is read', () => {
  const up: ReturnType<typeof define> = define('up', {x: natural}, natural, ({x}) => (up(x) as Nat).plus(1))
  // f(x) = f(x) + 1 has no model: were its equation a fact, x = 0 would follow
  expect(() => proveData(law('up is 0', {x: natural}, ({x}) => (up(x) as Nat).eq(0)))).toThrow(/no measure is proven to fall at every call/)
  for (const mk of Object.values(nonterminating)) expect(refusal(mk)).toMatch(/no measure is proven to fall at every call/)
  expect(refusal(nonterminating.mergeStatedWrong)).toMatch(/a measure is given.*size\(xs\): a call of its runs doesn't lower it/)
}, 60_000)

test('laws over well-founded functions: by the function\'s own recursion, ranked by its measure; broken variants refused', () => {
  const l = laws.interleaveLength(), s = schemesOf(programOf([l]), l).find(x => x.name === 'recursion of interleave on xs, ys')!
  expect(s.uses.length).toBe(1)
  for (const l2 of [laws.interleaveLength(), laws.add3acc()]) {
    const v = proveData(l2)
    expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true)
    expect(v.scheme).toMatch(/^recursion of (interleave|add3acc)/)
  }
  for (const mk of [broken.mergeLength, broken.add3acc]) expect(proveData(mk()).counterexample).toBeDefined()
}, 60_000)

test('a law through the built-ins: its bridges proven first, a copy of a function over them proven its copy, the law read back; checked by the kernel', () => {
  expect(proveData(through_.leqPlus())).toMatchObject({proven: true, checked: true})
  for (const [mk, through] of [[through_.leqPlusLeft, ['leq is ≤', 'plus is +']], [through_.geqSelf, ['leq is ≤', 'unfolded: geq']], [through_.occursCons, ['same is =', 'occurs is occurs_bi']]] as const) {
    const v = proveData(mk())
    expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true)
    for (const t of through) expect(v.through).toContain(t)
  }
  // by the cases of n alone (n ≤ 0 is n = 0, both ways), and the broken one refused
  expect(proveData(law('at most zero is zero', {n: natural}, ({n}) => (leq(n, 0) as Bool).iff(same(n, 0) as Bool))).proven).toBe(true)
  expect(proveData(throughBroken.leqPlus()).counterexample).toBeDefined()
})

test('a function that agrees with + on small values only: its bridge is not proven, and nothing false is proven through it', () => {
  // x + y up to x = 7, then 0
  const near: ReturnType<typeof define> = define('nearPlus', {x: natural, y: natural}, natural, ({x, y}) => (x as Nat).match({zero: () => y as Nat, succ: ({pred}) => when(pred.atLeast(7), 0 as number, (near(pred, y) as Nat).plus(1) as never)}))
  const v = proveData(law('nearPlus adds', {x: natural, y: natural}, ({x, y}) => (near(x, y) as Nat).eq((x as Nat).plus(y))), {ms: 5_000})
  expect(v.proven).toBe(false)
})

test('a function that agrees with x + 1 on small values only, read inside a larger law: its bridge is tried and not proven, and nothing false is proven through it', () => {
  // n + 1 up to n = 12, then 0: the samples (naturals up to 5) and the bridge's check (up to 12) see x + 1. The law isn't
  // its bridge: through it, n + 1 >= n + 1 would hold. Each search ends at its counted budget, the same on any machine.
  const inc: ReturnType<typeof define> = define('nearSucc', {n: natural}, natural, ({n}) => (n as Nat).match({zero: () => 1, succ: ({pred}) => when(pred.atLeast(12), 0 as number, (inc(pred) as Nat).plus(1) as never)}))
  const l = law('nearSucc is above n', {n: natural}, ({n}) => (inc(n) as Nat).atLeast((n as Nat).plus(1)))
  expect(transferPlan(l)?.bridges.get('nearSucc')?.name).toBe('x + 1')
  const bridge = proveData(law('nearSucc is x + 1', {n: natural}, ({n}) => (inc(n) as Nat).eq((n as Nat).plus(1))), {ms: 200})
  expect(bridge.proven).toBe(false)
  expect(bridge.counterexample).toBeUndefined()
  expect(bridge.stopped).toBe(true)
  const v = proveData(l, {ms: 200})
  expect(v.proven).toBe(false)
  expect(v.counterexample).toBeUndefined()
  expect(v.through).toBeUndefined()
  expect(v.stopped).toBe(true)
})

test('a function of three naturals that computes their sum (add3acc, by well-founded recursion): its bridge proven by its own recursion, a law read through it; one that agrees with a sum on small values only is not proven to', () => {
  const l = law('add3acc is symmetric in its first two', {x: natural, y: natural, z: natural}, ({x, y, z}) => (a3(x, y, z) as Nat).eq(a3(y, x, z) as Nat))
  expect(transferPlan(l)?.bridges.get('add3acc')?.name).toBe('x + y + z')
  const v = proveData(l)
  expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true)
  expect(v.through).toContain('add3acc is x + y + z')
  // x + y + z up to x = 5 (the bridge's check reads each argument up to 5), then 0
  const near: ReturnType<typeof define> = define('nearSum3', {x: natural, y: natural, z: natural}, natural, ({x, y, z}) => (x as Nat).match({zero: () => (y as Nat).plus(z as Nat), succ: ({pred}) => when(pred.atLeast(5), 0 as number, (near(pred, y, z) as Nat).plus(1) as never)}))
  const l2 = law('nearSum3 is symmetric in its first two', {x: natural, y: natural, z: natural}, ({x, y, z}) => (near(x, y, z) as Nat).eq(near(y, x, z) as Nat))
  expect(transferPlan(l2)?.bridges.get('nearSum3')?.name).toBe('x + y + z')
  // (no conjectures: their attempts' instances aren't counted work, and the bridge's own search is what is checked)
  const v2 = proveData(l2, {ms: 1000, lemmas: false})
  expect(v2.proven).toBe(false)
  expect(v2.through).toBeUndefined()
})

test('theory exploration: an equation over two lists generalised apart (append\'s associativity, over three), and a lemma use through another\'s conclusion', () => {
  const l = laws.lengthAppend(), names = conjectures(programOf([l]), l).map(c => c.name)
  expect(names).toContain('append(append(list1, list2), list3) = append(list1, append(list2, list3))')
  // drop of a successor is the definition at n + 1, whose predecessor (n + 1) ∸ 1 is n: one class, by arithmetic
  const v = proveData(law('drop of one more', {n: natural, x: natural, xs: List}, ({n, x, xs}) => (drp((n as Nat).plus(1), List.cons(x, xs)) as Val).eq(drp(n, xs) as Val)), {ms: 5000})
  expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true)
})

test('evaluation within bounds: a natural past 2^53 throws, a sample past the bounds is skipped, a datatype read only through a constructor is collected', () => {
  const big: ReturnType<typeof define> = define('bigPower', {n: natural}, natural, ({n}) => (n as Nat).match({zero: () => 1, succ: ({pred}) => (big(pred) as Nat).times(100_000)}))
  expect(() => evalX({op: 'call', fn: 'bigPower', args: [{op: 'nat', value: 5}]}, new Map(), {})).toThrow(EvalLimit)
  expect(refute(law('a power is at least one', {n: natural}, ({n}) => (big(n) as Nat).atLeast(1)))).toBeUndefined()
  const l = law('the head of one item', {n: natural}, ({n}) => (List.cons(n, List.nil).match({nil: () => 0, cons: ({head}) => head as Nat}) as Nat).eq(n))
  expect(programOf([l]).datas.map(d => d.name)).toContain('List')
  expect(proveData(l).proven).toBe(true)
})
