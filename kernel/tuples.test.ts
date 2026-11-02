// Tuple keys at the kernel (kernel.ts's keyParts, the tuple cells M[⟨k1|…⟩], sameKey, tupleEq's truth and facts, the
// reserved ⟨ ⟩ |, mapArities, eachParts): each case a goal with a model (a bad proof must be refused) beside one without
// (a good proof accepted). A proof here is forged, not searched: at each node the solver refutes the kernel's own rows
// if it can, else the node splits on the next atom given, so a kernel that gave a leaf a row it shouldn't (a cell pair,
// a tuple's part, a fact) has its forged tree accepted for a goal that has a model, which the test sees. The rows and
// facts are pinned too where a case reads one alone. Then the comprehensions of core/dsl.ts's relations (a law proven
// only if true, its proof checked by checkLaws) and the interpreter against a brute-force set semantics.
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, type State, cpair, cunpair, evalC, interpret, seeded} from '../core/machine.ts'
import {type Lin, add, k, scale, solve, sub, v} from '../core/solver.ts'
import {forall, nat, oneOf, rule} from '../core/dsl.ts'
import {type Goal, type Path, type Tree, canon, cellParts, check, checkLaws, facts, leafConstraints, linear, mapArities, scope, truth, tuple} from './kernel.ts'
import {proveLaws} from './prove.ts'

const X = (name: string): E => ({op: 'var', name}), K = (value: number): E => ({op: 'const', value})
const T = (...parts: E[]): E => tuple(parts), P = (k: 0 | 1, a: E): E => ({op: 'proj', k, a})
const M = (key: E, map = 'M'): E => ({op: 'get', map, key}), plus = (a: E, b: E): E => ({op: 'add', a, b})
const eq = (a: E, b: E): C => ({op: '=', a, b}), le = (a: E, b: E): C => ({op: '<=', a, b}), not = (x: C): C => ({op: 'not', x})
const ite = (c: C, a: E, b: E): E => ({op: 'if', c, then: a, else: b})
// x − y <= 0, the atom a split decides; both ways, and the path that decides atoms.
const d = (x: string | Lin, y: string | Lin): Lin => sub(typeof x === 'string' ? v(x) : x, typeof y === 'string' ? v(y) : y)
const both = (x: string | Lin, y: string | Lin): Lin[] => [d(x, y), d(y, x)]
const pathOf = (...ds: [Lin, boolean][]): Path => new Map(ds.map(([lin, holds]) => [canon(lin), {lin, holds}]))

// A tree for the goal from the kernel's rows alone: a leaf where the solver refutes them, else a split on the next atom.
function forge(goal: Goal, splits: Lin[], path: Path = new Map()): Tree | undefined {
  const out = solve(leafConstraints(goal, path))
  if (out.kind === 'refuted') return {leaf: out.steps}
  const s = splits.find(l => !path.has(canon(l)))
  if (!s) return undefined
  const yes = forge(goal, splits, new Map(path).set(canon(s), {lin: s, holds: true}))
  const no = yes && forge(goal, splits, new Map(path).set(canon(s), {lin: s, holds: false}))
  return yes && no && {split: s, yes, no}
}
// The goal's hypotheses all hold at the model (its variables, and each map's cells by key, every other cell 0).
const holds = (goal: Goal, vars: Record<string, number>, cells: Record<string, [number, number][]> = {}): boolean => {
  const maps = [...new Set([...JSON.stringify(goal.hyps).matchAll(/"op":"get","map":("(?:[^"\\]|\\.)*")/g)].map(m => JSON.parse(m[1]!) as string))]
  const st: State = {scalars: {}, maps: Object.fromEntries(maps.map(n => [n, new Map(cells[n] ?? [])]))}
  return goal.hyps.every(h => evalC(h, vars, st, {name: 'model', params: [], inputs: [], state: {}, step: {}, maps: Object.fromEntries(maps.map(n => [n, 0]))}))
}
// A goal with a model: no tree forged from the kernel's rows is accepted.
function refused(goal: Goal, splits: Lin[], vars: Record<string, number>, cells: Record<string, [number, number][]> = {}) {
  expect(holds(goal, vars, cells), `${goal.name}: the model given is one`).toBe(true)
  const tree = forge(goal, splits)
  expect(tree === undefined || !check(goal, tree), `${goal.name}: a tree accepted, and the goal has a model`).toBe(true)
}
// A goal with no model: the forged tree is accepted.
function proven(goal: Goal, splits: Lin[] = []) {
  const tree = forge(goal, splits)
  expect(tree, `${goal.name}: no tree forged`).toBeDefined()
  expect(check(goal, tree!), `${goal.name}: its tree refused`).toBe(true)
}
const pairRows = (goal: Goal, path: Path) => leafConstraints(goal, path).filter(r => r.src && 'pair' in r.src).map(r => (r.src as {pair: [string, string]}).pair)
const [a, b, c, dd, u, w, x, y, kk] = ['a', 'b', 'c', 'd', 'u', 'w', 'x', 'y', 'k'].map(X) as [E, E, E, E, E, E, E, E, E]

test('a tuple cell is another only when every part is decided equal, both ways', () => {
  // M[⟨a|b⟩] and M[⟨a|c⟩]: a = a, b and c apart.
  const g1: Goal = {name: 'one part equal', hyps: [eq(M(T(a, b)), K(1)), eq(M(T(a, c)), K(0))]}
  refused(g1, [...both('b', 'c'), ...both('a', 'c')], {a: 0, b: 0, c: 1}, {M: [[cpair(0, 0), 1]]})
  refused({...g1, name: 'one part equal (the first apart)', hyps: [eq(M(T(a, b)), K(1)), eq(M(T(c, b)), K(0))]}, both('a', 'c'), {a: 0, b: 0, c: 1}, {M: [[cpair(0, 0), 1]]})
  proven({name: 'b = c', hyps: [eq(b, c), ...g1.hyps]}, both('b', 'c'))
  proven({name: 'a = c, b', hyps: [eq(a, c), eq(M(T(a, b)), K(1)), eq(M(T(c, b)), K(0))]}, both('a', 'c'))
  // Decided one way only, no pair; both ways, the pair.
  expect(pairRows(g1, pathOf([d('b', 'c'), true]))).toEqual([])
  expect(pairRows(g1, pathOf([d('c', 'b'), true]))).toEqual([])
  expect(pairRows(g1, pathOf([d('b', 'c'), true], [d('c', 'b'), true]))).toHaveLength(2)
  // ⟨x|y⟩ and ⟨u|w+1⟩ with y = w: the second parts one apart, never one cell.
  const g2: Goal = {name: '⟨x|y⟩, ⟨u|w+1⟩, y = w', hyps: [eq(x, u), eq(y, w), eq(M(T(x, y)), K(1)), eq(M(T(u, plus(w, K(1)))), K(0))]}
  refused(g2, [...both('x', 'u'), ...both('y', 'w'), ...both('y', add(v('w'), k(1)))], {x: 0, u: 0, y: 0, w: 0}, {M: [[cpair(0, 0), 1]]})
  proven({...g2, name: '⟨x|y⟩, ⟨u|w+1⟩, y = w + 1', hyps: [eq(x, u), eq(y, plus(w, K(1))), ...g2.hyps.slice(2)]}, [...both('x', 'u'), ...both('y', add(v('w'), k(1)))])
  expect(pairRows(g2, pathOf(...both('x', 'u').map((l): [Lin, boolean] => [l, true]), ...both('y', 'w').map((l): [Lin, boolean] => [l, true])))).toEqual([])
  // Parts that are sums (',' inside a part): ⟨a+b|c⟩ and ⟨d|c⟩ with d = a + b, and with d one more.
  const sum = add(v('a'), v('b'))
  proven({name: '⟨a+b|c⟩, ⟨d|c⟩, d = a + b', hyps: [eq(dd, plus(a, b)), eq(M(T(plus(a, b), c)), K(1)), eq(M(T(dd, c)), K(0))]}, both('d', sum))
  refused({name: '⟨a+b|c⟩, ⟨d|c⟩, d = a + b + 1', hyps: [eq(dd, plus(plus(a, b), K(1))), eq(M(T(plus(a, b), c)), K(1)), eq(M(T(dd, c)), K(0))]},
    [...both('d', sum), ...both('d', add(sum, k(1)))], {a: 0, b: 0, c: 0, d: 1}, {M: [[cpair(0, 0), 1]]})
  // A part that is itself a tuple cell (brackets and bars inside a part): N[⟨M[⟨a|b⟩]|c⟩] and N[⟨M[⟨a|e⟩]|c⟩].
  const mab = M(T(a, b)), mae = M(T(a, X('e'))), cab = 'M[⟨a:1|b:1⟩]', cae = 'M[⟨a:1|e:1⟩]'
  proven({name: 'tuple cells in a part', hyps: [eq(b, X('e')), eq(M(T(mab, c), 'N'), K(1)), eq(M(T(mae, c), 'N'), K(0))]}, [...both('b', 'e'), ...both(cab, cae)])
  refused({name: 'tuple cells in a part, b and e apart', hyps: [eq(M(T(mab, c), 'N'), K(1)), eq(M(T(mae, c), 'N'), K(0))]}, [...both('b', 'e'), ...both(cab, cae)],
    {a: 0, b: 0, c: 0, e: 1}, {M: [[0, 1]], N: [[cpair(1, 0), 1]]})
  expect(cellParts('N[⟨M[⟨a:1|b:1⟩]:1|c:1⟩]')).toEqual({map: 'N', keys: [{'M[⟨a:1|b:1⟩]': 1}, {c: 1}]})
  expect(cellParts('N[⟨M[⟨a:1|b:1⟩]:1,M[x:1]:2|1:3⟩]')).toEqual({map: 'N', keys: [{'M[⟨a:1|b:1⟩]': 1, 'M[x:1]': 2}, {1: 3}]})
  expect(cellParts('N[⟨|b:1⟩]')).toEqual({map: 'N', keys: [{}, {b: 1}]})
  expect(cellParts('M[a:1,M[⟨b:1|c:1⟩]:2]')).toEqual({map: 'M', key: {a: 1, 'M[⟨b:1|c:1⟩]': 2}})
})

test('tuples of different lengths: never one cell, never equal part by part', () => {
  // M[⟨a|b⟩] and M[⟨a|b|c⟩]: cpair(0, 0) = 0, cpair(0, cpair(0, 1)) = 5.
  const g: Goal = {name: '2 and 3 parts', hyps: [eq(M(T(a, b)), K(1)), eq(M(T(a, b, c)), K(0))]}
  refused(g, both('b', 'c'), {a: 0, b: 0, c: 1}, {M: [[0, 1]]})
  refused({...g, hyps: [eq(M(T(a, b, c)), K(1)), eq(M(T(a, b)), K(0))]}, both('b', 'c'), {a: 0, b: 0, c: 1}, {M: [[5, 1]]})
  expect(pairRows(g, pathOf(...both('b', 'c').map((l): [Lin, boolean] => [l, true])))).toEqual([])
  // tup(tup(a, b), c) and tup(a, tup(b, c)): the first has no parts (its first part is a tuple), as a key or an equality.
  const left = T(T(a, b), c), right = T(a, T(b, c))
  expect(linear(M(left), new Map())).toBeUndefined()
  expect(linear(M(right), new Map())).toBeDefined()
  expect(truth(eq(left, right), new Map())).toBeUndefined()
  const splits = [...both('a', 'b'), ...both('b', 'c'), ...both('a', 'c'), v('a'), v('b'), v('c')]
  refused({name: '((a, b), c) = (a, (b, c))', hyps: [eq(left, right)]}, splits, {a: 0, b: 0, c: 0})
  refused({name: '((a, b), c) ≠ (a, (b, c))', hyps: [not(eq(left, right))]}, splits, {a: 0, b: 1, c: 0})
  refused({name: 'M[((a, b), c)], M[(a, (b, c))]', hyps: [eq(M(left), K(1)), eq(M(right), K(0))]}, splits, {a: 0, b: 1, c: 0}, {M: [[cpair(cpair(0, 1), 0), 1]]})
  // (a, b) = (a, (b, c)) holds at b = c = 0 only, and fails elsewhere; neither is refuted.
  refused({name: '(a, b) = (a, (b, c))', hyps: [eq(T(a, b), right)]}, splits, {a: 0, b: 0, c: 0})
  refused({name: '(a, b) ≠ (a, (b, c))', hyps: [not(eq(T(a, b), right))]}, splits, {a: 0, b: 0, c: 1})
  // Nested alike on both sides: part by part.
  proven({name: '((a, b), c) ≠ ((d, e), f) with a = d, b = e, c = f', hyps: [not(eq(left, T(T(dd, X('e')), X('f')))), eq(a, dd), eq(b, X('e')), eq(c, X('f'))]},
    [...both('a', 'd'), ...both('b', 'e'), ...both('c', 'f')])
})

test('a plain cell and a tuple cell of one map are never claimed equal', () => {
  // M[k] and M[⟨a|b⟩] with k = a: cpair(0, 1) = 2 is not 0.
  const g: Goal = {name: 'M[k], M[⟨a|b⟩], k = a', hyps: [eq(kk, a), eq(M(kk), K(1)), eq(M(T(a, b)), K(0))]}
  const splits = [v('k'), scale(v('k'), -1), ...both('k', 'a'), v('b'), scale(v('b'), -1)]
  refused(g, splits, {k: 0, a: 0, b: 1}, {M: [[0, 1]]})
  // At k = a = b = 0 they are one cell (cpair(0, 0) = 0), but the kernel never says so: no pair, at any path.
  const zero: Goal = {name: 'M[k], M[⟨a|b⟩] at 0', hyps: [eq(kk, K(0)), eq(a, K(0)), eq(b, K(0)), eq(M(kk), K(1)), eq(M(T(a, b)), K(0))]}
  const all0 = pathOf(...['k', 'a', 'b'].flatMap((n): [Lin, boolean][] => [[v(n), true], [scale(v(n), -1), true]]), ...both('k', 'a').map((l): [Lin, boolean] => [l, true]))
  expect(pairRows(zero, all0)).toEqual([])
  expect(forge(zero, splits)).toBeUndefined()
  // A plain key equal to a tuple key's part, in either order of the cells.
  refused({name: 'M[⟨a|b⟩], M[k], k = a', hyps: [eq(M(T(a, b)), K(1)), eq(M(kk), K(0)), eq(kk, a)]}, splits, {k: 0, a: 0, b: 1}, {M: [[2, 1]]})
})

test('aliasing: a map read at two shapes is refused; two maps never share a cell', () => {
  const base: Machine = {name: 'shapes', params: [], inputs: ['a', 'b', 'k'], state: {}, maps: {M: 0, N: 0}, step: {}}
  const reads = (...cs: C[]): Machine => ({...base, step: {flags: Object.fromEntries(cs.map((c, i) => [`f${i}`, c]))}})
  expect(mapArities(reads(le(M(T(a, b)), K(1))))).toEqual({M: 2})
  expect(() => scope(reads(le(M(T(a, b)), K(1))))).not.toThrow()
  for (const m of [
    reads(le(M(T(a, b)), K(1)), le(M(kk), K(1))), // a tuple and a plain key
    reads(le(M(kk), K(1)), le(M(T(a, b)), K(1))),
    reads(le(M(T(a, b)), K(1)), le(M(T(a, b, kk)), K(1))), // 2 and 3 parts
    {...reads(le(M(T(a, b)), K(1))), step: {flags: {f0: le(M(T(a, b)), K(1))}, maps: {M: {key: kk, value: K(1)}}}}, // written at a plain key
    {...reads(le(M(kk), K(1))), step: {flags: {f0: le(M(kk), K(1))}, maps: {M: {key: T(a, b), value: K(1)}}}}, // written at a tuple
    {...reads(le(M(T(a, b)), K(1))), maps: {}, inputMaps: ['M']}, // a carried map
    {...reads(le(M(T(a, b)), K(1))), maps: {}, fns: {M: {js: 'k => k'}}} as Machine, // a function
  ]) expect(() => mapArities(m), JSON.stringify(m.step)).toThrow()
  for (const m of [reads(le(M(T(a, b)), K(1)), le(M(kk), K(1))), reads(le(M(T(a, b)), K(1)), le(M(T(a, b, kk)), K(1)))]) expect(() => scope(m)).toThrow()
  // A law reading the map at the other shape.
  const law: Law = {name: 'M at a plain key', holds: le(M(X('s')), K(1)), forall: 's'}
  expect(() => mapArities(reads(le(M(T(a, b)), K(1))), [law])).toThrow()
  // Two maps: no pair, whatever the keys; one map: the pair.
  const g: Goal = {name: 'M[⟨a|b⟩], N[⟨a|b⟩]', hyps: [eq(M(T(a, b)), K(1)), eq(M(T(a, b), 'N'), K(0))]}
  refused(g, both('a', 'b'), {a: 0, b: 0}, {M: [[0, 1]]})
  expect(pairRows(g, new Map())).toEqual([])
  proven({name: 'M[⟨a|b⟩], M[⟨c|b⟩], a = c', hyps: [eq(a, c), eq(M(T(a, b)), K(1)), eq(M(T(c, b)), K(0))]}, both('a', 'c'))
})

test('proj: of a non-tuple no linear form; of a 2-tuple its part, never a tuple; of a 3-tuple its rest', () => {
  for (const e of [P(0, x), P(1, x), P(0, M(kk)), P(1, plus(x, K(1))), P(0, P(1, T(a, b))), P(1, P(1, T(a, b))), P(0, T(T(a, b), c))]) expect(linear(e, new Map()), JSON.stringify(e)).toBeUndefined()
  expect(linear(P(0, T(a, b)), new Map())).toEqual(v('a'))
  expect(linear(P(1, T(a, b)), new Map())).toEqual(v('b'))
  expect(linear(P(0, T(a, b, c)), new Map())).toEqual(v('a'))
  expect(linear(P(1, T(a, b, c)), new Map())).toBeUndefined() // (a tuple)
  expect(linear(P(0, P(1, T(a, b, c))), new Map())).toEqual(v('b'))
  expect(linear(P(1, P(1, T(a, b, c))), new Map())).toEqual(v('c'))
  // proj 0 x = x only where x is 0 or 1 (cun(2) = (0, 1)); proj 0 of proj 1 of (a, b) is proj 0 of b, not b.
  refused({name: 'proj 0 x ≠ x', hyps: [not(eq(P(0, x), x))]}, [v('x'), scale(v('x'), -1)], {x: 2})
  refused({name: 'proj 1 x ≠ x', hyps: [not(eq(P(1, x), x))]}, [v('x'), scale(v('x'), -1)], {x: 2})
  refused({name: 'proj 0 (proj 1 (a, b)) ≠ b', hyps: [not(eq(P(0, P(1, T(a, b))), b))]}, [v('b'), scale(v('b'), -1)], {a: 0, b: 2})
  refused({name: 'proj 1 (proj 1 (a, b)) ≠ b', hyps: [not(eq(P(1, P(1, T(a, b))), b))]}, [v('b'), scale(v('b'), -1)], {a: 0, b: 2})
  for (const [e, part] of [[P(0, T(a, b)), a], [P(1, T(a, b)), b], [P(0, T(a, b, c)), a], [P(0, P(1, T(a, b, c))), b], [P(1, P(1, T(a, b, c))), c]] as [E, E][])
    proven({name: `${JSON.stringify(e)} is its part`, hyps: [not(eq(e, part))]}, both('a', 'b'))
  // A read at proj 1 of a 2-tuple is the plain cell at its part; at proj 1 of a 3-tuple, the tuple cell of the rest.
  expect(linear(M(P(1, T(a, b))), new Map())).toEqual(v('M[b:1]'))
  expect(linear(M(P(1, T(a, b, c))), new Map())).toEqual(v('M[⟨b:1|c:1⟩]'))
  expect(linear(M(P(1, P(1, T(a, b, c)))), new Map())).toEqual(v('M[c:1]'))
  expect(linear(M(P(1, T(a, b, c, dd))), new Map())).toEqual(v('M[⟨b:1|c:1|d:1⟩]'))
  expect(linear(M(P(0, T(a, b))), new Map())).toEqual(v('M[a:1]'))
  proven({name: 'M[proj 1 (a, b)] is M[b]', hyps: [eq(M(P(1, T(a, b))), K(1)), eq(M(b), K(0))]})
  proven({name: 'M[proj 1 (a, b, c)] is M[⟨b|c⟩]', hyps: [eq(M(P(1, T(a, b, c))), K(1)), eq(M(T(b, c)), K(0))]})
  // proj 1 of a 2-tuple is no tuple key: M[proj 1 (a, b)] and M[⟨…⟩] apart.
  // (b = 2, c = 0: M[2] and M[cpair(2, 0) = 3])
  refused({name: 'M[proj 1 (a, b)], M[⟨b|c⟩], b = 2', hyps: [eq(b, K(2)), eq(M(P(1, T(a, b))), K(1)), eq(M(T(b, c)), K(0))]}, [...both('b', 'c'), v('c'), scale(v('c'), -1)], {a: 0, b: 2, c: 0}, {M: [[2, 1]]})
})

test('names with ⟨ ⟩ | are refused by scope, and have no linear form', () => {
  const ok: Machine = {name: 'names', params: ['p'], inputs: ['i'], state: {s: K(0)}, maps: {M: 0}, step: {state: {s: X('i')}, flags: {f: le(X('s'), X('p'))}}}
  expect(() => scope(ok)).not.toThrow()
  const rename = (m: Machine, from: string, to: string): Machine => JSON.parse(JSON.stringify(m).replaceAll(`"${from}"`, `"${to}"`))
  for (const ch of ['⟨', '⟩', '|']) for (const name of ['p', 'i', 's', 'M', 'f']) {
    expect(() => scope(rename(ok, name, `${name}${ch}`)), `${name}${ch}`).toThrow()
    expect(() => scope(rename(ok, name, `${ch}${name}`)), `${ch}${name}`).toThrow()
  }
  expect(() => scope({...ok, step: {...ok.step, maps: {M: {each: 'j|', value: K(0)}}}})).toThrow()
  for (const name of ['a|b', '⟨a', 'a⟩', 'p:1|q']) expect(linear(X(name), new Map())).toBeUndefined()
  // A name that would spell a tuple's parts: M[⟨p:1|q:1|r:1⟩] from the 2-tuple (p:1|q, r) is the 3-tuple (p, q, r)'s cell.
  // cpair(5, 0) = 15; cpair(0, cpair(0, 0)) = 0.
  const [p, q, r] = ['p', 'q', 'r'].map(X) as [E, E, E]
  refused({name: 'a spelled tuple', hyps: [eq(M(T(X('p:1|q'), r)), K(1)), eq(M(T(p, q, r)), K(0))]}, [], {'p:1|q': 5, p: 0, q: 0, r: 0}, {M: [[15, 1]]})
  refused({name: 'a spelled tuple (⟨⟩)', hyps: [eq(M(X('⟨p:1|q:1⟩')), K(1)), eq(M(T(p, q)), K(0))]}, [], {'⟨p:1|q:1⟩': 5, p: 0, q: 0}, {M: [[5, 1]]})
})

test('a tuple equality: its truth and facts are its parts\', positive and negated', () => {
  const tq = eq(T(a, b), T(c, dd)), none = new Map() as Path
  const yes = (...ls: Lin[]) => ls.map((l): [Lin, boolean] => [l, true])
  const ac = pathOf(...yes(...both('a', 'c'))), acbd = pathOf(...yes(...both('a', 'c'), ...both('b', 'd'))), bd = pathOf(...yes(...both('b', 'd')))
  // Truth: open, true when every part is, false when one is.
  expect(truth(tq, none)).toBeUndefined()
  expect(truth(tq, ac)).toBeUndefined()
  expect(truth(tq, acbd)).toBe(true)
  expect(truth(tq, pathOf([add(d('a', 'c'), k(1)), true]))).toBe(false) // a < c
  expect(truth(tq, pathOf(...yes(...both('a', 'c')), [add(d('d', 'b'), k(1)), true]))).toBe(false) // d < b
  // Positive facts: both parts' equalities.
  expect(facts(tq, none)).toEqual([...facts(eq(a, c), none), ...facts(eq(b, dd), none)])
  // Negated: two parts open give nothing; exactly one open, its disequality; none open, 1 <= 0.
  expect(facts(not(tq), none)).toEqual([])
  expect(facts(not(tq), ac)).toEqual(facts(not(eq(b, dd)), ac))
  expect(facts(not(tq), bd)).toEqual(facts(not(eq(a, c)), bd))
  const dLeB = pathOf(...yes(...both('a', 'c'), d('d', 'b'))) // a = c, d <= b: the open part's fact d <= b − 1
  expect(facts(not(tq), dLeB)).toEqual(facts(not(eq(b, dd)), dLeB))
  expect(facts(not(tq), dLeB)).toEqual([add(d('d', 'b'), k(1))])
  expect(facts(not(tq), acbd)).toEqual([k(1)])
  // At the check: a negated equality refuted once both parts are decided equal; not with one part only.
  const splits = [...both('a', 'c'), ...both('b', 'd')]
  proven({name: '(a, b) ≠ (c, d), a = c, b = d', hyps: [not(tq), eq(a, c), eq(b, dd)]}, splits)
  refused({name: '(a, b) ≠ (c, d), a = c', hyps: [not(tq), eq(a, c)]}, splits, {a: 0, b: 0, c: 0, d: 1})
  refused({name: '(a, b) ≠ (c, d), b = d', hyps: [not(tq), eq(b, dd)]}, splits, {a: 0, b: 0, c: 1, d: 0})
  refused({name: '(a, b) ≠ (c, d)', hyps: [not(tq)]}, splits, {a: 0, b: 0, c: 1, d: 0})
  proven({name: '(a, b) = (c, d), a < c', hyps: [tq, le(plus(a, K(1)), c)]})
  proven({name: '(a, b) = (c, d), d < b', hyps: [tq, le(plus(dd, K(1)), b)]})
  refused({name: '(a, b) = (c, d), a + b = 1', hyps: [tq, eq(plus(a, b), K(1))]}, splits, {a: 0, b: 1, c: 0, d: 1})
  refused({name: '(a, b) = (c, d), a + 1 = d', hyps: [tq, eq(plus(a, K(1)), dd)]}, splits, {a: 0, b: 1, c: 0, d: 1})
  // Its truth read in a term: if (a, b) = (c, d) then 1 else 0.
  const t = ite(tq, K(1), K(0))
  proven({name: 'if (a, b) = (c, d): 1, with a < c', hyps: [eq(t, K(1)), le(plus(a, K(1)), c)]}, [add(d('a', 'c'), k(1))])
  proven({name: 'if (a, b) = (c, d): 0, with a = c, b = d', hyps: [eq(t, K(0)), eq(a, c), eq(b, dd)]}, splits)
  refused({name: 'if (a, b) = (c, d): 0, with a = c', hyps: [eq(t, K(0)), eq(a, c)]}, splits, {a: 0, b: 0, c: 0, d: 1})
  refused({name: 'if (a, b) = (c, d): 1, with b = d', hyps: [eq(t, K(1)), eq(b, dd)]}, [...splits, add(d('a', 'c'), k(1)), add(d('c', 'a'), k(1))], {a: 0, b: 0, c: 0, d: 0})
  refused({name: 'if (a, b) = (c, d): 0', hyps: [eq(t, K(0))]}, [...splits, add(d('a', 'c'), k(1))], {a: 0, b: 0, c: 1, d: 0})
  // 3-tuples: the rest compared as a tuple again.
  const t3 = eq(T(a, b, c), T(x, y, u))
  proven({name: '(a, b, c) ≠ (x, y, u), all equal', hyps: [not(t3), eq(a, x), eq(b, y), eq(c, u)]}, [...both('a', 'x'), ...both('b', 'y'), ...both('c', 'u')])
  refused({name: '(a, b, c) ≠ (x, y, u), the first two equal', hyps: [not(t3), eq(a, x), eq(b, y)]}, [...both('a', 'x'), ...both('b', 'y'), ...both('c', 'u')], {a: 0, b: 0, c: 0, x: 0, y: 0, u: 1})
  proven({name: '(a, b, c) = (x, y, u), c < u', hyps: [t3, le(plus(c, K(1)), u)]})
})

// --- comprehensions: R' = {(x, y): R(y, x)}, with tuples added ------------------------------------------------------------
// The flip reads at (y, x) the tuple it writes at (x, y): a law about R holds after it only by the law at the swapped key.
const diagonal = (off: boolean) => rule(off ? 'diagonal, off' : 'diagonal').sorts('N').relations({R: ['N', 'N']})
  .inputs({op: oneOf('add', 'flip'), a: nat, b: nat})
  .step(({op, a, b, R}: any) => ({
    R: R.each((x: any, y: any) => op.is('flip').and(R.has(y, x)).or(op.is('add').and(R.has(x, y).or(x.eq(a).and(y.eq(off ? b : a)))))),
  }))
const ordered = (back: boolean) => rule(back ? 'ordered, flipped' : 'ordered').sorts('N').relations({R: ['N', 'N']})
  .inputs({op: oneOf('add', 'keep'), a: nat, b: nat})
  .step(({op, a, b, R}: any) => ({
    R: R.each((x: any, y: any) => (back ? op.is('keep').and(R.has(y, x)) : op.is('keep').and(R.has(x, y))).or(op.is('add').and(R.has(x, y).or(x.eq(a).and(y.eq(b), a.atMost(b)))))),
  }))
const onDiagonal = (r: any): Law => r.law('on the diagonal', ({R}: any) => forall((x, y) => R.has(x, y).implies(x.eq(y))))
const inOrder = (r: any): Law => r.law('ordered', ({R}: any) => forall((x, y) => R.has(x, y).implies(x.atMost(y))))

test('a comprehension that writes the tuples it reads: a law proven only if true, the proof the kernel\'s', () => {
  for (const [r, twin, lawOf] of [[diagonal(false), diagonal(true), onDiagonal], [ordered(false), ordered(true), inOrder]] as const) {
    const m = r.machine, law = lawOf(r), out = proveLaws(m, [law])
    expect(mapArities(m, [law])).toEqual({R: 2})
    expect(out.proven, `${m.name}: ${law.name}`).toBe(true)
    expect(checkLaws(m, [law], out.proof!), `${m.name}: the kernel checks its proof`).toBe(true)
    // The false twin: not proven, its own proof (if any) and the true machine's refused, and a run breaks it.
    const f = twin.machine, fl = lawOf(twin), fout = proveLaws(f, [fl])
    expect(fout.proven, `${f.name}: ${fl.name} proven, and it is false`).toBe(false)
    if (fout.proof) expect(checkLaws(f, [fl], fout.proof)).toBe(false)
    expect(checkLaws(f, [fl], out.proof!), `${f.name}: the true machine's proof accepted`).toBe(false)
    // (op 0 adds (0, 1); op 1 flips it, or keeps it flipped: (1, 0) alone, neither on the diagonal nor ordered)
    const run = interpret(f)
    let st = run.init({})
    st = run.step({}, st, {op: 0, a: 0, b: 1})
    if (f.name === 'ordered, flipped') st = run.step({}, st, {op: 1, a: 0, b: 0})
    const cell = (i: number, j: number) => st.maps.R!.get(cpair(i, j)) ?? st.defaults?.R ?? 0
    expect(f.name === 'ordered, flipped' ? [cell(1, 0), cell(0, 1)] : [cell(0, 1), cell(1, 0)]).toEqual([1, 0])
  }
})

// --- the interpreter against sets ----------------------------------------------------------------------------------------
// R (2 places) and S (3 places) under random steps, each a comprehension or a tuple added or removed; after each, every
// tuple of a small universe read from the interpreter's state equals the brute force's set, and nothing lies outside it.
const OPS = ['addR', 'remR', 'flip', 'band', 'sym', 'offdiag', 'addS', 'rot', 'lift', 'drop'] as const
const sets = rule('sets').sorts('N').relations({R: ['N', 'N'], S: ['N', 'N', 'N']})
  .inputs({op: oneOf(...OPS), a: nat, b: nat, c: nat})
  .step(({op, a, b, c, R, S}: any) => {
    const is = (o: typeof OPS[number]) => op.is(o)
    return {
      R: R.each((x: any, y: any) => is('addR').and(R.has(x, y).or(x.eq(a).and(y.eq(b))))
        .or(is('remR').and(R.has(x, y), x.eq(a).and(y.eq(b)).not()))
        .or(is('flip').and(R.has(y, x)))
        .or(is('band').and(R.has(x, y).or(x.eq(a).and(y.lt(b)))))
        .or(is('sym').and(R.has(x, y).or(R.has(y, x))))
        .or(is('offdiag').and(R.has(x, y), x.eq(y).not()))
        .or(is('drop').and(R.has(x, y), S.has(x, y, c).not()))
        .or(is('addS').or(is('rot'), is('lift')).and(R.has(x, y)))),
      S: S.each((x: any, y: any, z: any) => is('addS').and(S.has(x, y, z).or(x.eq(a).and(y.eq(b), z.eq(c))))
        .or(is('rot').and(S.has(y, z, x)))
        .or(is('lift').and(S.has(x, y, z).or(R.has(x, y).and(z.eq(c)))))
        .or(is('addR').or(is('remR'), is('flip'), is('band'), is('sym'), is('offdiag'), is('drop')).and(S.has(x, y, z)))),
    }
  })

test('the interpreter\'s relations after random steps are the brute force\'s sets', () => {
  const m = sets.machine, run = interpret(m), rand = seeded(Number(process.env.FUZZ_SEED ?? 7)), U = 5
  expect(mapArities(m)).toEqual({R: 2, S: 3})
  const key = (t: number[]) => t.join(',')
  let checked = 0
  for (let trial = 0; trial < 40; trial++) {
    let st = run.init({})
    let R = new Set<string>(), S = new Set<string>()
    for (let i = 0; i < 12; i++) {
      const o = OPS[rand(OPS.length)]!, a = rand(U), b = rand(U), c = rand(U)
      st = run.step({}, st, {op: OPS.indexOf(o), a, b, c})
      const R2 = new Set<string>(), S2 = new Set<string>()
      for (let x = 0; x < U + 1; x++) for (let y = 0; y < U + 1; y++) {
        const r = R.has(key([x, y]))
        const inR = o === 'addR' ? r || (x === a && y === b) : o === 'remR' ? r && !(x === a && y === b) : o === 'flip' ? R.has(key([y, x]))
          : o === 'band' ? r || (x === a && y < b) : o === 'sym' ? r || R.has(key([y, x])) : o === 'offdiag' ? r && x !== y
          : o === 'drop' ? r && !S.has(key([x, y, c])) : r
        if (inR) R2.add(key([x, y]))
        for (let z = 0; z < U + 1; z++) {
          const s = S.has(key([x, y, z]))
          const inS = o === 'addS' ? s || (x === a && y === b && z === c) : o === 'rot' ? S.has(key([y, z, x])) : o === 'lift' ? s || (r && z === c) : s
          if (inS) S2.add(key([x, y, z]))
        }
      }
      R = R2; S = S2
      const at = (map: 'R' | 'S', k: number) => st.maps[map]!.get(k) ?? st.defaults?.[map] ?? 0
      expect(st.defaults?.R ?? 0).toBe(0)
      expect(st.defaults?.S ?? 0).toBe(0)
      for (let x = 0; x < U + 2; x++) for (let y = 0; y < U + 2; y++) {
        expect(at('R', cpair(x, y)), `${o} step ${i}: R(${x}, ${y})`).toBe(R.has(key([x, y])) ? 1 : 0)
        for (let z = 0; z < U + 2; z++) expect(at('S', cpair(x, cpair(y, z))), `${o} step ${i}: S(${x}, ${y}, ${z})`).toBe(S.has(key([x, y, z])) ? 1 : 0)
      }
      // Nothing set outside the universe: every nonzero cell is a tuple of the sets.
      for (const [kz, val] of st.maps.R!) if (val) expect(R.has(key(unpair(kz, 2)))).toBe(true)
      for (const [kz, val] of st.maps.S!) if (val) expect(S.has(key(unpair(kz, 3)))).toBe(true)
      checked++
    }
  }
  expect(checked).toBe(480)
})
const unpair = (z: number, n: number): number[] => {
  const out: number[] = []
  for (let i = 0; i + 1 < n; i++) { const [p, rest] = cunpair(z); out.push(p); z = rest }
  return [...out, z]
}

// Known hole (reported, kernel.ts not this file's to change): a map's name is not checked where a read becomes a column
// (linearOp's get), so a map named with the reserved characters spells another read's column. Here a 2-tuple's cell
// (its second part the read of the map "Q:1|v") and a 3-tuple's both read M[⟨x:1|Q:1|v[w:1]:1⟩]: one column, so the
// goal is refuted, and it has a model (x = w = 0, Q = 1: M at cpair(0, 0) = 0 and at cpair(0, cpair(1, 0)) = 2).
// Lean numbers its maps, so its cellT columns stay apart. The fix: refuse a map named 1 or with * [ ] , : ⟦ ⟧ ⟨ ⟩ | in
// linearOp's get, as a variable is. `bun test --todo` runs it.
test.todo('a map named with reserved characters spells no other read\'s column', () => {
  const g: Goal = {name: 'a spelled column', hyps: [eq(M(T(x, M(w, 'Q:1|v'))), K(0)), eq(M(T(x, X('Q'), M(w, 'v'))), K(1))]}
  refused(g, [], {x: 0, w: 0, Q: 1}, {M: [[2, 1]]})
  // (and with plain keys: A[B[Q[w:1]:1] read as A at B[Q[w] and as A[B at Q[w])
  refused({name: 'a spelled plain column', hyps: [eq(M(M(w, 'B[Q'), 'A'), K(0)), eq(M(M(w, 'Q'), 'A[B'), K(1))]}, [], {w: 0}, {'A[B': [[0, 1]]})
})
