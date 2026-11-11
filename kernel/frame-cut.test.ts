// The kernel twin of Count.lean's FrameCuts against the same inputs as research/track-fable/FrameCuts.lean (kernel-reduced there).
import {expect, test} from 'bun:test'
import type {C, E} from '../core/machine.ts'
import {type Lin, type Step, add, k, scale, sub, v} from '../core/solver.ts'
import {type Count, type FrameCut, type Goal, type LinCut, type MonoCut, type Path, type Tree, canon, check, checkGoalLemmas, frameActive, frameOk, frameRows, framePath, leafConstraints, linOk, linRows, monoOk, monoRows, simpE} from './kernel.ts'
import {grow} from './prove.ts'

const x = (name: string): E => ({op: 'var', name}), n = (value: number): E => ({op: 'const', value})
const flip = (r: Lin): Lin => add(k(1), scale(r, -1))
const op4: C = {op: '=', a: x('op'), b: n(4)}
const pre: Count = {v: 'v0', key: 'kk', below: n(2), body: {op: 'get', map: 'M', key: x('kk')}}
const post: Count = {v: 'v1', key: 'kk', below: n(2), body: {op: 'if', c: op4, then: {op: 'get', map: 'M', key: x('kk')}, else: n(0)}}
const counts = [pre, post]
const opLe = sub(v('op'), k(4)), opGe = sub(k(4), v('op'))
const frame: FrameCut = {when: [opLe, opGe], post: 'v1', pre: 'v0'}
const hyps: C[] = [{op: '<', a: x('v0'), b: x('v1')}, op4]
const goal: Goal = {name: 'frame', hyps}
const at = (...atoms: [Lin, boolean][]): Path => new Map(atoms.map(([lin, holds]) => [canon(lin), {lin, holds}]))
// A leaf from named rows, as the lemma-cut fixture builds them: the rows must be among the leaf's constraints.
function leaf(path: Path, wanted: Lin[]): Tree {
  const rows = leafConstraints(goal, path)
  const steps: Step[] = wanted.map(lin => {
    const index = rows.findIndex(r => canon(r.lin) === canon(lin))
    if (index < 0) throw Error('test input row missing: ' + canon(lin))
    return {kind: 'input', index}
  })
  steps.push({kind: 'combine', a: 0, b: 1, ma: 1, mb: 1})
  return {leaf: steps}
}
const postLePre = sub(v('v1'), v('v0')), preLtPost = add(sub(v('v0'), v('v1')), k(1))
const main: Tree = {
  split: opLe,
  yes: {split: opGe, yes: leaf(framePath([frame], [], at([opLe, true], [opGe, true])), [postLePre, preLtPost]), no: leaf(at([opLe, true], [opGe, false]), [flip(opGe), opGe])},
  no: leaf(at([opLe, false]), [flip(opLe), opLe]),
}

test('simpE resolves only conditions decided under the path and free of the key', () => {
  const path = at([opLe, true], [opGe, true])
  expect(simpE(post.body, path, 'kk')).toEqual(pre.body)
  expect(simpE(post.body, at([opLe, true]), 'kk')).toEqual(post.body)
  const keyed: E = {op: 'if', c: {op: '=', a: x('kk'), b: n(4)}, then: n(1), else: n(0)}
  expect(simpE(keyed, at([sub(v('kk'), k(4)), true], [sub(k(4), v('kk')), true]), 'kk')).toEqual(keyed)
})

test('frameOk accepts the op = 4 frame and refuses the variants Lean refuses', () => {
  expect(frameOk(counts, frame)).toBe(true)
  expect(frameActive(frame, at([opLe, true], [opGe, true]))).toBe(true)
  expect(frameActive(frame, at([opLe, true]))).toBe(false)
  expect(frameActive(frame, at([opLe, true], [opGe, false]))).toBe(false)
  expect(frameRows(frame)).toEqual([{v1: 1, v0: -1}, {v0: 1, v1: -1}])
  expect(frameOk(counts, {...frame, when: [opLe]})).toBe(false)
  expect(frameOk(counts, {...frame, when: []})).toBe(false)
  expect(frameOk([pre, {...post, key: 'other'}], frame)).toBe(false)
  expect(frameOk([pre, {...post, below: n(3)}], frame)).toBe(false)
  expect(frameOk([pre, {...post, body: {op: 'if', c: op4, then: {op: 'get', map: 'M', key: {op: 'add', a: x('kk'), b: n(1)}}, else: n(0)}}], frame)).toBe(false)
  expect(frameOk(counts, {...frame, pre: 'v9'})).toBe(false)
  const pre2: Count = {...pre, body: {op: 'if', c: {op: '<=', a: n(4), b: x('op')}, then: {op: 'get', map: 'M', key: x('kk')}, else: n(0)}}
  expect(frameOk([pre2, post], frame)).toBe(true)
})

test('the frame row closes the op = 4 leaf and nowhere else', () => {
  expect(checkGoalLemmas(goal, main, [], [frame], counts)).toBe(true)
  expect(checkGoalLemmas(goal, main, [], [], counts)).toBe(false)
  expect(checkGoalLemmas(goal, main, [])).toBe(false)
  expect(check(goal, main)).toBe(false)
  // The frame row is not available where the path has not decided op = 4.
  expect(() => leaf(framePath([frame], [], at([opLe, true])), [postLePre, preLtPost])).toThrow('row missing')
  expect(checkGoalLemmas(goal, {split: opLe, yes: main.yes, no: main.no}, [], [{...frame, when: [opLe]}], counts)).toBe(false)
  // A frame the counts refuse fails the whole check even when the tree would not need it.
  expect(checkGoalLemmas(goal, main, [], [frame, {...frame, pre: 'v9'}], counts)).toBe(false)
})

test('framePath keeps every original atom and prepends the active frames\' rows', () => {
  const path = at([opLe, true], [opGe, true]), out = framePath([frame], [], path)
  expect(out.size).toBe(4)
  expect([...out.values()].slice(0, 2).map(a => a.lin)).toEqual(frameRows(frame))
  expect(framePath([frame], [], at([opLe, true]))).toEqual(framePath([], [], at([opLe, true])))
})

// Section 17 (MLDR-DESIGN.md): the step's write tree under the body's condition, reading the key through a stride — the
// same inputs as FrameCuts.lean's Section 17 examples.
const z17: E = {op: 'add', a: {op: 'mul', k: 64, a: x('row')}, b: x('member')}
const cell17: C = {op: '=', a: {op: 'get', map: 'Config', key: z17}, b: n(1)}
const pre17: Count = {v: 'c0', key: 'member', below: n(2), body: {op: 'if', c: cell17, then: n(1), else: n(0)}}
const pick17: C = {op: 'and', xs: [{op: '=', a: x('op'), b: n(0)}, {op: '<', a: z17, b: n(64)}]}
const w17: C = {op: 'or', xs: [{op: 'and', xs: [pick17, {op: '<=', a: n(1), b: {op: 'get', map: 'S', key: z17}}]}, {op: 'and', xs: [{op: 'not', x: pick17}, cell17]}]}
const post17: Count = {v: 'c1', key: 'member', below: n(2), body: {op: 'if', c: {op: '=', a: {op: 'if', c: w17, then: n(1), else: n(0)}, b: n(1)}, then: n(1), else: n(0)}}
const opLe2 = sub(v('op'), k(2)), opGe2 = sub(k(2), v('op')), opGe1 = sub(k(1), v('op'))
test('the write tree under the condition collapses to the pre body once the path refutes the writing operation', () => {
  expect(frameOk([pre17, post17], {when: [opLe2, opGe2, opGe1], post: 'c1', pre: 'c0'})).toBe(true)
  // truth is a lookup, not arithmetic: op = 2 on the path does not decide op = 0 by itself.
  expect(frameOk([pre17, post17], {when: [opLe2, opGe2], post: 'c1', pre: 'c0'})).toBe(false)
  expect(frameOk([pre17, post17], {when: [], post: 'c1', pre: 'c0'})).toBe(false)
  expect(simpE(post17.body, new Map([opLe2, opGe2, opGe1].map(w => [canon(w), {lin: w, holds: true}])), 'member')).toEqual(pre17.body)
})
test('a guard reading the key through the stride is decided at every key from the row bound, and not otherwise', () => {
  const post17b: Count = {v: 'c1', key: 'member', below: n(2), body: {op: 'if', c: {op: '=', a: {op: 'if', c: {op: '<', a: z17, b: n(64)}, then: {op: 'get', map: 'S', key: z17}, else: {op: 'get', map: 'Config', key: z17}}, b: n(1)}, then: n(1), else: n(0)}}
  const rowGe1 = sub(k(64), scale(v('row'), 64))
  expect(frameOk([pre17, post17b], {when: [rowGe1], post: 'c1', pre: 'c0'})).toBe(true)
  expect(frameOk([pre17, post17b], {when: [], post: 'c1', pre: 'c0'})).toBe(false)
  // A guard true at key 0 but not everywhere, or with the key on both sides, stays open.
  const post17c: Count = {...post17b, body: {op: 'if', c: {op: '=', a: {op: 'if', c: {op: '<', a: x('member'), b: {op: 'add', a: x('member'), b: n(1)}}, then: {op: 'get', map: 'S', key: z17}, else: {op: 'get', map: 'Config', key: z17}}, b: n(1)}, then: n(1), else: n(0)}}
  expect(frameOk([pre17, post17c], {when: [rowGe1, opLe2, opGe2, opGe1], post: 'c1', pre: 'c0'})).toBe(false)
})

// Section 17.4: the per-key cut — post ≤ pre proved for every key by the CDCL on the auxiliary goal, then one row at the leaf.
test('a per-key cut: the auxiliary goal proved by the CDCL gives post ≤ pre at the leaf, with the refusals Lean lists', () => {
  const preM: Count = {v: 'c0', key: 'kk', below: n(2), body: {op: 'get', map: 'M', key: x('kk')}}
  // The post body zeroes one key (as a write does) and keeps the rest: at every key it is at most the pre body.
  const postM: Count = {v: 'c1', key: 'kk', below: n(2), body: {op: 'if', c: {op: '=', a: x('kk'), b: x('j')}, then: n(0), else: {op: 'get', map: 'M', key: x('kk')}}}
  const aux: Goal = {name: 'aux', hyps: [{op: '<', a: x('kk'), b: n(2)}, {op: '<', a: preM.body, b: postM.body}]}
  const proved = grow(aux)
  expect('tree' in proved).toBe(true)
  const cut: MonoCut = {when: [], post: 'c1', pre: 'c0', tree: (proved as {tree: Tree}).tree}
  expect(monoOk([preM, postM], cut)).toBe(true)
  expect(monoRows(cut)).toEqual([{c1: 1, c0: -1}])
  // The mirror claim pre ≤ post is false (a key other than j with a positive cell): the CDCL finds no tree.
  expect('tree' in grow({name: 'aux', hyps: [{op: '<', a: x('kk'), b: n(2)}, {op: '<', a: postM.body, b: preM.body}]})).toBe(false)
  // Refusals: a different bound, a condition reading the key, an auxiliary tree that proves nothing, a count the goal lacks.
  expect(monoOk([preM, {...postM, below: n(3)}], cut)).toBe(false)
  expect(monoOk([preM, postM], {...cut, when: [{op: '<', a: x('kk'), b: n(64)}]})).toBe(false)
  expect(monoOk([preM, postM], {...cut, tree: {leaf: []}})).toBe(false)
  expect(monoOk([preM, postM], {...cut, pre: 'c9'})).toBe(false)
  // At a leaf the cut's row c1 − c0 ≤ 0 refutes c0 < c1, and nothing else does.
  const g: Goal = {name: 'mono', hyps: [{op: '<', a: x('c0'), b: x('c1')}]}
  const rows = leafConstraints(g, framePath([], [], new Map(), [cut]))
  const want = [add(sub(v('c0'), v('c1')), k(1)), sub(v('c1'), v('c0'))].map(lin => rows.findIndex(r => canon(r.lin) === canon(lin)))
  expect(want.every(i => i >= 0)).toBe(true)
  const tree: Tree = {leaf: [{kind: 'input', index: want[0]!}, {kind: 'input', index: want[1]!}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}
  expect(checkGoalLemmas(g, tree, [], [], [preM, postM], [cut])).toBe(true)
  expect(checkGoalLemmas(g, tree, [], [], [preM, postM], [])).toBe(false)
  expect(checkGoalLemmas(g, tree, [], [], [preM, postM], [{...cut, tree: {leaf: []}}])).toBe(false)
})

// Section 17.5: the linear per-key cut — a sum of two counts bounded by a third, proved per key by the CDCL, then one row at the leaf.
test('a linear cut: Σ pos ≤ Σ neg proved per key by the CDCL gives its row at the leaf, with the refusals Lean lists', () => {
  // Three counts over one key and bound: A[k], B[k] and their pointwise maximum; A + B ≤ 2·max(A, B) at every key.
  const cA: Count = {v: 'a', key: 'kk', below: n(3), body: {op: 'get', map: 'A', key: x('kk')}}
  const cB: Count = {v: 'b', key: 'kk', below: n(3), body: {op: 'get', map: 'B', key: x('kk')}}
  const cM: Count = {v: 'm', key: 'kk', below: n(3), body: {op: 'max', a: {op: 'get', map: 'A', key: x('kk')}, b: {op: 'get', map: 'B', key: x('kk')}}}
  const counts = [cA, cB, cM]
  const aux: Goal = {name: 'aux', hyps: [{op: '<', a: x('kk'), b: n(3)}, {op: '<', a: {op: 'add', a: {op: 'mul', k: 2, a: cM.body}, b: n(0)}, b: {op: 'add', a: {op: 'mul', k: 1, a: cA.body}, b: {op: 'add', a: {op: 'mul', k: 1, a: cB.body}, b: n(0)}}}]}
  const proved = grow(aux)
  expect('tree' in proved).toBe(true)
  const cut: LinCut = {when: [], pos: [[1, 'a'], [1, 'b']], neg: [[2, 'm']], tree: (proved as {tree: Tree}).tree}
  expect(linOk(counts, cut)).toBe(true)
  expect(linRows(cut)).toEqual([{a: 1, b: 1, m: -2}])
  // Refusals: a count the goal lacks, a differing bound, a condition reading the key, an auxiliary tree that proves nothing, no terms.
  expect(linOk(counts, {...cut, pos: [[1, 'zz']]})).toBe(false)
  expect(linOk([cA, cB, {...cM, below: n(4)}], cut)).toBe(false)
  expect(linOk(counts, {...cut, when: [{op: '<', a: x('kk'), b: n(9)}]})).toBe(false)
  expect(linOk(counts, {...cut, tree: {leaf: []}})).toBe(false)
  expect(linOk(counts, {...cut, pos: [], neg: []})).toBe(false)
  expect(linOk(counts, {...cut, pos: [[-1, 'a']]})).toBe(false)
  expect(linOk(counts, {...cut, pos: [[0.5, 'a']]})).toBe(false)
  expect(linOk(counts, {...cut, pos: [[Number.MAX_SAFE_INTEGER, 'a'], [1, 'a']]})).toBe(false)
  expect(linOk([{...cA, key:'other'}, cB, cM], cut)).toBe(false)
  // At a leaf the row a + b − 2m ≤ 0 refutes 2m < a + b, and nothing else does.
  const g: Goal = {name: 'lin', hyps: [{op: '<', a: {op: 'mul', k: 2, a: x('m')}, b: {op: 'add', a: x('a'), b: x('b')}}]}
  const rows = leafConstraints(g, framePath([], [], new Map(), [], [cut]))
  const want = [add(sub(scale(v('m'), 2), add(v('a'), v('b'))), k(1)), sub(add(v('a'), v('b')), scale(v('m'), 2))].map(lin => rows.findIndex(r => canon(r.lin) === canon(lin)))
  expect(want.every(i => i >= 0)).toBe(true)
  const tree: Tree = {leaf: [{kind: 'input', index: want[0]!}, {kind: 'input', index: want[1]!}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}
  expect(checkGoalLemmas(g, tree, [], [], counts, [], [cut])).toBe(true)
  expect(checkGoalLemmas(g, tree, [], [], counts, [], [])).toBe(false)
})
