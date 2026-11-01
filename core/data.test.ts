// Recursive datatypes as values (core/data.ts): the functions run as written, laws proven by cyclic proofs the search
// finds (checked again by the kernel), broken variants refused with a value that breaks them, a definition that isn't
// structural recursion refused unless its termination is proven (a measure every call lowers, each call's obligation
// proven by the kernel), and a tampered proof refused by the kernel.
import {expect, test} from 'bun:test'
import {type Bool, type Nat, type Val, type X, type Y, EvalLimit, boolean, checkMeasures, conjectures, data, define, evalX, law, mutual, natural, programOf, proveData, refute, schemesOf, self, showValue, showY, valueVar, when} from './data.ts'
import {checkCyclic} from '../kernel/cyclic.ts'
import {transferPlan} from './transfer.ts'
import {Bag, Forest, List, both, ev, Rose, Tree, a3, ack, adversarial, app, bmerge, broken, bsort, heapList, drp, ilv, laws, leq, len, merge, mergeRuns, mir, mrg, nest, nestA, nestB, nested, nonterminating, nz, paren, qsort, refusal, rev, same, sorted, ins, through as through_, throughBroken, tokens, wellFounded} from '../examples/data.ts'

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
  // a ring that isn't structural (badR passes a constant): taken by well-founded recursion, a measure each (badR's call
  // of badF at Fr.no is below badR's own size by its constant); one that passes its tree round in a forest is refused
  const bad: ReturnType<typeof define> = define('badR', {t: Rt}, natural, ({t}) => (t as Val).match({nd: () => badF(Fr.no)}))
  const badF: ReturnType<typeof define> = define('badF', {ts: Fr}, natural, ({ts}) => (ts as Val).match({no: () => 0, more: ({h}) => (bad(h) as Nat).plus(1)}))
  expect(() => programOf([law('bad', {t: Rt}, ({t}) => (bad(t) as Nat).eq(0))])).not.toThrow()
  expect([...bad.fn.ring].sort()).toEqual(['badF', 'badR'])
  for (const f of [bad, badF]) for (const o of f.fn.termination!.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
  const loopR: ReturnType<typeof define> = define('loopR', {t: Rt}, natural, ({t}) => loopF(Fr.more(t, Fr.no)) as Nat)
  const loopF: ReturnType<typeof define> = define('loopF', {ts: Fr}, natural, ({ts}) => (ts as Val).match({no: () => 0, more: ({h}) => (loopR(h) as Nat).plus(1)}))
  expect(() => programOf([law('loop', {t: Rt}, ({t}) => (loopR(t) as Nat).eq(0))])).toThrow(/structural.*no measure is proven to fall/)
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
  // qsort's calls are on filters of the tail: each obligation through a size law about the filter (no longer than the
  // tail), proven by the filter's own recursion
  expect(qsort.fn.termination!.obligations.map(o => o.lemmas)).toEqual([[expect.stringMatching(/^size law: size\(atMost\(/)], [expect.stringMatching(/^size law: size\(above\(/)]])
  expect(showValue(List, run({x: {op: 'call', fn: 'qsort', args: [{op: 'var', name: 'xs'}]}}, {xs: list(3, 1, 2, 1)}) as never)).toBe('cons(1, cons(1, cons(2, cons(3, nil))))')
  expect(showValue(List, run({x: {op: 'call', fn: 'merge', args: [{op: 'var', name: 'xs'}, {op: 'var', name: 'ys'}]}}, {xs: list(1, 4), ys: list(2, 3)}) as never)).toBe('cons(1, cons(2, cons(3, cons(4, nil))))')
}, 60_000)

test('a ring of functions that is not structural recursion: a measure each (one length), each call within the ring proven to lower the callee\'s below the caller\'s', () => {
  // tokens reads paren at the same value: the size first at both, then 1 at tokens and 0 at paren (the call the size
  // leaves equal, ranked by the runs)
  expect([tokens.fn.termination!.text, paren.fn.termination!.text]).toEqual(['(size(e), 1)', '(size(e), 0)'])
  expect(tokens.fn.ring).toEqual(['tokens', 'paren'])
  for (const t of [tokens.fn.termination!, paren.fn.termination!]) for (const o of t.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
  // mergeRuns' call is on the runs merged in pairs: a size law about pairwise, proven by induction, then used
  const o = mergeRuns.fn.termination!.obligations[0]!
  expect(mergeRuns.fn.termination!.text).toBe('size(rs)')
  expect(o.lemmas).toEqual([expect.stringMatching(/^size law: 2·size\(pairwise\(rs0\)\) <= size\(rs0\) \+ 2/)])
  expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
  for (const mk of Object.values(wellFounded)) { const v = proveData(mk()); expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true) }
}, 60_000)

test('nested recursion (well-founded, a call in another\'s argument): taken with an invariant of the function, proven with each decrease; its obligations as Nested.lean states them', () => {
  // nz 0 = 0, nz (n + 1) = nz (nz n): the inner call's value read as r under lexLt([pred], [pred + 1]) ⇒ r ≤ pred
  const t = nz.fn.termination!
  expect([t.text, showY(t.invariant!)]).toEqual(['n', 'nz#value <= nz.n'])
  expect(t.obligations.map(o => showY(o.law.holds))).toEqual([
    'pred < pred + 1',
    'not (not (pred < pred + 1) or nz#r1 <= pred) or nz#r1 < pred + 1',
    '0 <= 0',
    'not (not (pred < pred + 1) or nz#r1 <= pred) or not (not (nz#r1 < pred + 1) or nz#r2 <= nz#r1) or nz#r2 <= pred + 1',
  ])
  // nest keeps its list's size; Ackermann's outer call lowers m whatever the inner's value (no invariant); a ring
  expect([nest.fn.termination!.text, showY(nest.fn.termination!.invariant!)]).toEqual(['size(xs)', 'size(nest#value) = size(nest.xs)'])
  expect([ack.fn.termination!.text, ack.fn.termination!.invariant]).toEqual(['(m, n)', undefined])
  expect(nestA.fn.ring).toEqual(['nestA', 'nestB'])
  for (const f of [nz, nest, ack, nestA, nestB]) for (const o of f.fn.termination!.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof), o.law.name).toBe(true)
  for (const mk of Object.values(nested)) { const v = proveData(mk()); expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof), v.goal).toBe(true) }
}, 120_000)

test('halves and a merge over the user\'s ≤: taken by size laws proven by induction on both halves at once, and by cases on the user\'s ≤', () => {
  expect([bmerge, bsort, heapList].map(f => f.fn.termination!.text)).toEqual(['(size(x), size(y))', 'size(x)', 'size(x)'])
  // the halves' law, one of evens and odds (each the other's induction step)
  expect(bsort.fn.termination!.obligations[0]!.lemmas).toEqual([expect.stringMatching(/^size law: 2·size\(odds\(xs0\)\) <= size\(xs0\) \+ 1 and 2·size\(evens\(xs0\)\) <= size\(xs0\) \+ 2/)])
  expect(heapList.fn.termination!.obligations[0]!.lemmas).toEqual([expect.stringMatching(/^size law: size\(hmerge\(x0, y1\)\) \+ 1 <= size\(x0\) \+ size\(y1\)/)])
  for (const f of [bmerge, bsort, heapList]) for (const o of f.fn.termination!.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
}, 60_000)

test('a ring weighted across its functions (a formula\'s fold, Not weighing twice, at each function), then ranked by the runs: no size falls at ¬(l ∧ r) to l ∧ ¬r', () => {
  const t = [ev.fn.termination!, both.fn.termination!]
  expect([...ev.fn.ring].sort()).toEqual(['both', 'ev'])
  expect(t.map(x => x.text)).toEqual([expect.stringMatching(/^\(foldForm_\d+\(f\), 0\)$/), expect.stringMatching(/^\(foldForm_\d+\(f\), 1\)$/)])
  for (const x of t) for (const o of x.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof), o.law.name).toBe(true)
}, 60_000)

test('nested recursion refused where a call\'s value has no place to be read (a call under a case of a match in another\'s argument); stated measures of a ring of two lengths padded (terminating)', () => {
  const L2 = data('Lst2', {none: {}, more: {item: natural, rest: self}})
  const under: ReturnType<typeof define> = define('underCase', {xs: L2}, natural, ({xs}) => (xs as Val).match({none: () => 0, more: ({rest}) => under((rest as Val).match({none: () => L2.none, more: ({rest: r2}) => L2.more(under(r2), r2)}))}))
  expect(refusal(() => law('under', {xs: L2}, ({xs}) => (under(xs) as Nat).eq(0)))).toMatch(/nested recursion isn't taken there/)
  // stated2A (size(xs)), read as (size(xs), 0), stated2B (size(xs), size(xs)): its call of stated2A at xs lower by the second
  const a: ReturnType<typeof define> = define('stated2A', {xs: L2}, natural, ({xs}) => (xs as Val).match({none: () => 0, more: ({rest}) => b(rest)}), {measure: ['xs']})
  const b: ReturnType<typeof define> = define('stated2B', {xs: L2}, natural, ({xs}) => a(xs), {measure: ['xs', 'xs']})
  expect(refusal(() => law('stated2', {xs: L2}, ({xs}) => (a(xs) as Nat).eq(0)))).toBeUndefined()
  expect([a.fn.termination!.measure.comps.length, b.fn.termination!.measure.comps.length]).toEqual([2, 2])
}, 60_000)

test('invariants given with measures (nested recursion, well-founded): one reading anything but its function\'s parameters and value, binding, or calling the ring is refused; a call under a natural\'s match in an argument is refused', () => {
  const v = (n: string): X => ({op: 'var', name: n}), size = (x: X): X => ({op: 'size', data: 'List', of: x})
  const keeps = (f: typeof nest, other: X): Y => ({op: '=', a: size(v(valueVar(f.fn))), b: other})
  const S = {comps: [{coef: [1], c: 0}]}
  const bad: [string, Y][] = [
    ['another variable', keeps(nest, size(v('zz')))],
    ['a match', keeps(nest, {op: 'match', data: 'List', of: v('nest.xs'), cases: [{binds: [], body: size(v('nest.xs'))}, {binds: ['h9', 't9'], body: size(v('nest.xs'))}]})],
    ['a natural\'s match', {op: '=', a: {op: 'natmatch', of: size(v('nest.xs')), zero: {op: 'nat', value: 0}, pred: 'p9', succ: {op: 'nat', value: 0}}, b: {op: 'nat', value: 0}}],
    ['a function parameter', keeps(nest, {op: 'apply', param: 'fp', arg: size(v('nest.xs'))})],
    ['a call of the function', keeps(nest, size({op: 'call', fn: 'nest', args: [v('nest.xs')]}))],
  ]
  for (const [what, y] of bad) expect(() => checkMeasures([nest.fn], [S], 10_000, [y]), what).toThrow(/an invariant reads its parameters and value alone/)
  // a ring of two: an invariant of nestA calling nestB
  expect(() => checkMeasures([nestA.fn, nestB.fn], [S, S], 10_000, [keeps(nestA, size({op: 'call', fn: 'nestB', args: [v('nestA.xs')]})), undefined])).toThrow(/an invariant reads its parameters and value alone/)
  // one through a function taken before (len), and the size: proven
  const r = checkMeasures([nest.fn], [S], 20_000, [{op: 'and', xs: [keeps(nest, size(v('nest.xs'))), {op: '=', a: {op: 'call', fn: 'len', args: [v(valueVar(nest.fn))]}, b: {op: 'call', fn: 'len', args: [v('nest.xs')]}}]}])
  expect(r.proven).toBe(true)
  // an empty measure, and a measure folding the function itself, refused
  expect(() => checkMeasures([nest.fn], [{comps: []}], 10_000)).toThrow(/measures of one length/)
  expect(() => checkMeasures([nz.fn], [{comps: [{coef: [0], c: 0, fold: {fn: 'nz', of: 0}}]}], 10_000)).toThrow(/a measure reads the ring/)
  // (in a ring, the second component of one function's measure folding the other)
  expect(() => checkMeasures([nestA.fn, nestB.fn], [{comps: [S.comps[0]!, {coef: [0], c: 0, fold: {fn: 'nestB', of: 0}}]}, {comps: [S.comps[0]!, S.comps[0]!]}], 10_000)).toThrow(/a measure reads the ring/)
  // a call in a natural's zero case, itself in a case of a match within the argument (the field bound there)
  const L3 = data('Lst3', {none: {}, more: {item: natural, rest: self}})
  const zc: ReturnType<typeof define> = define('underZero', {xs: L3}, natural, ({xs}) => (xs as Val).match({none: () => 0, more: ({rest}) => zc((rest as Val).match({none: () => L3.none, more: ({item, rest: r2}) => (item as Nat).match({zero: () => L3.more(zc(r2), r2), succ: () => r2})}))}))
  expect(refusal(() => law('underZero', {xs: L3}, ({xs}) => (zc(xs) as Nat).eq(0)))).toMatch(/nested recursion isn't taken there/)
  // f(n + 1) = f(case n of 0 → 0, q + 1 → f(q)): the inner call under the natural's match, its predecessor bound there
  const nm: ReturnType<typeof define> = define('underNat', {n: natural}, natural, ({n}) => (n as Nat).match({zero: () => 0, succ: ({pred}) => nm((pred as Nat).match({zero: () => 0, succ: ({pred: q}) => nm(q)}))}))
  expect(refusal(() => law('underNat', {n: natural}, ({n}) => (nm(n) as Nat).eq(0)))).toMatch(/nested recursion isn't taken there/)
}, 120_000)

test('definitions that do not terminate, made to look as if they do (rings, a size law true of short lists only, a guard past the runs\' values), are refused with the measures tried', () => {
  const why = Object.fromEntries(Object.entries(adversarial).map(([name, mk]) => [name, refusal(mk)])) as Record<keyof typeof adversarial, string | undefined>
  for (const [name, w] of Object.entries(why)) expect(w, name).toMatch(/no measure is proven to fall at every call|nested recursion isn't taken|no parameter a measure reads/)
  // a measure each was tried and refused, by a call of the runs or its obligation
  for (const name of ['passRound', 'lowerRaise', 'swapRing', 'lateRing', 'stepUp', 'nearTail', 'nearTailRing', 'ringStatedWrong', 'halvesTill9', 'guardKeeps'] as const) expect(why[name], name).toMatch(/(doesn't lower it|not proven to lower it)/)
  // nested: an invariant its runs suggest lowers the outer call, and a body past them doesn't keep it
  for (const name of ['nestedLate', 'nestedGrow', 'nestedGrowRing'] as const) expect(why[name], name).toMatch(/keeping .*(doesn't keep its invariant|not proven to keep its invariant)/)
}, 240_000)

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

// A weighted size of a parameter (core/data.ts's foldMeasures): a tree turned right at its root until its left is a
// leaf, the left subtree weighing 2 (the only weights its runs' calls all lower). A function a user defined under the
// fold's name is never read as the fold: there the turn is refused.
test('a weighted size: a turned tree taken by a fold defined for it, never by a user\'s function of the same name', () => {
  const turnOf = (dname: string, name: string) => {
    const D = data(dname, {leaf: {}, node: {l: self, v: natural, r: self}})
    const turn: ReturnType<typeof define> = define(name, {t: D}, natural, ({t}) => (t as Val).match({leaf: () => 0,
      node: ({l, v, r}) => (l as Val).match({leaf: () => (turn(r) as Nat).plus(1), node: ({l: p, v: x, r: q}) => turn(D.node(p, x, D.node(q, v, r)))})}))
    return {D, turn}
  }
  const {D: TT, turn} = turnOf('TT', 'turnTT')
  expect(() => programOf([law('turned', {t: TT}, ({t}) => (turn(t) as Nat).eq(turn(t)))])).not.toThrow()
  expect(turn.fn.measure!.comps[0]!.fold?.fn).toBe('foldTT_201')
  for (const o of turn.fn.termination!.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
  // (a user's own foldTU_201, defined before the fold would be: the turn on TU is refused)
  define('foldTU_201', {x: data('TUx', {none: {}})}, natural, () => 0)
  const {D: TU, turn: turn2} = turnOf('TU', 'turnTU')
  expect(refusal(() => law('turned', {t: TU}, ({t}) => (turn2(t) as Nat).eq(turn2(t))))).toMatch(/no measure is proven to fall/)
  // (and one defined after it, over the fold's name: a second turn on TT doesn't read it as the fold)
  define('foldTT_201', {x: data('TTx', {none: {}})}, natural, () => 0)
  const turn3: ReturnType<typeof define> = define('turnTT2', {t: TT}, natural, ({t}) => (t as Val).match({leaf: () => 0,
    node: ({l, v, r}) => (l as Val).match({leaf: () => (turn3(r) as Nat).plus(1), node: ({l: p, v: x, r: q}) => turn3(TT.node(p, x, TT.node(q, v, r)))})}))
  const t3 = (() => { try { return turn3.fn.termination } catch { return undefined } })()
  expect(t3?.measure.comps.some(c => c.fold?.fn === 'foldTT_201') ?? false).toBe(false)
}, 60_000)

// The paths core/data.ts reads a call's obligation under (sitesOf): a second match on a variable matched before takes
// the case its first match took, its fields the first's, and never reaches the others (where a call that doesn't
// descend may sit); a match on a term that is no variable wraps the obligation in that term's case. And a measure
// found is one checkMeasures proves again; a parameter no measure reads (a flag) doesn't keep a function from one.
test('the paths of a call\'s obligation: a variable matched again, a term matched, a flag beside', () => {
  const PL = data('PL', {nil: {}, cons: {h: natural, t: self}})
  const tl = define('plTail', {xs: PL}, PL, ({xs}) => (xs as Val).match({nil: () => PL.nil, cons: ({t}) => t as Val}))
  // (the unreached case calls itself at the same list: read, it would be refused)
  const again: ReturnType<typeof define> = define('plAgain', {xs: PL}, natural, ({xs}) => (xs as Val).match({nil: () => 0,
    cons: () => (xs as Val).match({nil: () => again(xs), cons: ({t}) => (again(t) as Nat).plus(1)})}))
  // (the call descends only where the tail of xs is a cons, so xs is one)
  const onTail: ReturnType<typeof define> = define('plOnTail', {xs: PL}, natural, ({xs}) => (tl(xs) as Val).match({nil: () => 0, cons: () => (onTail(tl(xs)) as Nat).plus(1)}))
  // (a flag passed along, read by no measure)
  const flagged: ReturnType<typeof define> = define('plFlagged', {b: boolean, xs: PL, ys: PL}, natural, ({b, xs, ys}) => (xs as Val).match({nil: () => 0,
    cons: ({t}) => (ys as Val).match({nil: () => (flagged(b, t, ys) as Nat).plus(1), cons: ({t: u}) => (flagged(b, PL.cons(0, t), u) as Nat).plus(1)})}))
  // (a natural matched on a term, n − 1: the call at n − 1 below n where n − 1 is a successor)
  const pred: ReturnType<typeof define> = define('plPred', {n: natural}, natural, ({n}) => ((n as Nat).minus(1)).match({zero: () => 0, succ: () => (pred((n as Nat).minus(1)) as Nat).plus(1)}))
  // (a ring one of whose functions reads a flag alone: its measure a constant, between its callers' and callees')
  const viaFlag: ReturnType<typeof define> = define('plViaFlag', {xs: PL}, natural, ({xs}) => (xs as Val).match({nil: () => 0, cons: () => (flagOnly(xs.ne(xs)) as Nat).plus(1)}))
  const flagOnly: ReturnType<typeof define> = define('plFlagOnly', {b: boolean}, natural, ({b}) => when(b as Bool, 0 as number, viaFlag(PL.nil) as never))
  for (const f of [again, onTail, flagged, pred, viaFlag]) {
    expect(refusal(() => law('taken', Object.fromEntries(f.fn.params.map(p => [p.name, p.sort])) as never, vs => (f(...f.fn.params.map(p => vs[p.name])) as Nat).eq(f(...f.fn.params.map(p => vs[p.name])) as Nat))), f.fn.name).toBeUndefined()
    if (f.fn.decreases !== undefined) continue
    for (const o of f.fn.termination!.obligations) expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
    if (f.fn.ring.length === 1) expect(checkMeasures([f.fn], [f.fn.measure!]).proven, f.fn.name).toBe(true)
  }
  expect(again.fn.decreases).toBeUndefined()
  expect([...viaFlag.fn.ring].sort()).toEqual(['plFlagOnly', 'plViaFlag'])
}, 120_000)
