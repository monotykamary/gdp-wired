import {expect, test} from 'bun:test'
import {type C, ite, n, not, x} from '../machine.ts'
import {type Lin, type Step, add, k, scale, sub, v} from '../solver.ts'
import {type Goal, type LemmaCut, type Path, type Tree, canon, check, leafConstraintsReusing as rowsAt, lemmaPath} from '../../kernel/kernel.ts'
import {admitConditionalCut, inlineConditionalCuts} from './conditional-cuts.ts'

const until = (): number => performance.now() + 2000
const le = (a: string, b: string | number): C => ({op: '<=', a: x(a), b: typeof b === 'number' ? n(b) : x(b)})
const put = (path: Path, lin: Lin, holds = true): Path => new Map(path).set(canon(lin), {lin, holds})
const flip = (lin: Lin): Lin => add(k(1), scale(lin, -1))
// Deliberately duplicate the kernel's list-to-Map representation in the tests.
const proofPath = (when: Lin[], cut: Lin): Path => {
  const path: Path = new Map()
  let duplicate = 0
  for (const atom of [{lin: cut, holds: false}, ...when.map(lin => ({lin, holds: true}))]) {
    const id = canon(atom.lin)
    path.set(path.has(id) ? `@${duplicate++}` : id, atom)
  }
  return path
}
const local = (goal: Goal, lemma: LemmaCut): Goal => ({...goal, hyps: lemma.slice?.map(i => goal.hyps[i]!) ?? goal.hyps})
function sumRows(goal: Goal, path: Path, forms: Lin[]): Tree {
  const rows = rowsAt(goal, path), leaf: Step[] = forms.map(form => {
    const index = rows.findIndex(row => canon(row.lin) === canon(form))
    expect(index).toBeGreaterThanOrEqual(0)
    return {kind: 'input', index}
  })
  let previous = 0
  for (let i = 1; i < forms.length; i++) {
    leaf.push({kind: 'combine', a: previous, b: i, ma: 1, mb: 1})
    previous = leaf.length - 1
  }
  return {leaf}
}
function fixture() {
  const guard = v('g'), cut = sub(v('a'), k(1)), second = sub(v('b'), k(1)), irrelevant = v('unused')
  const guarded: C = {op: '<=', a: x('a'), b: ite(le('g', 0), n(0), n(10))}
  const goal: Goal = {name: 'conditional cuts', hyps: [le('unrelated', 8), guarded, le('b', 'a')]}
  const source: Goal = {name: goal.name, hyps: [le('a', 0)]}
  const scope = put(put(new Map(), guard), irrelevant), from = put(scope, cut, false)
  const tree = sumRows(source, from, [v('a'), flip(cut)])
  const first = admitConditionalCut(goal, source, tree, from, scope, cut, [], until())!
  expect(first).toBeDefined()
  return {goal, source, scope, from, tree, first, guard, cut, second}
}
function chain() {
  const f = fixture()
  const source: Goal = {name: f.goal.name, hyps: [le('a', 1), le('b', 'a'), {op: '<=', a: n(2), b: x('b')}] }
  const tree = sumRows(source, f.scope, [f.cut, sub(f.second, f.cut), flip(f.second)])
  const second = admitConditionalCut(f.goal, source, tree, f.scope, f.scope, f.second, [f.first], until())!
  expect(second).toBeDefined()
  return {...f, secondCut: second, secondSource: source, secondTree: tree}
}

test('a cut activates only in its conditional scope and drops unrelated guards and source hypotheses', () => {
  const f = fixture()
  expect(f.first.when.map(canon)).toEqual([canon(f.guard)])
  expect(f.first.slice).toEqual([1])
  expect(check(local(f.goal, f.first), f.first.tree, proofPath(f.first.when, f.cut))).toBe(true)
  expect(lemmaPath([f.first], new Map()).size).toBe(0)
  expect(lemmaPath([f.first], put(new Map(), f.guard, false)).size).toBe(1)
  expect(lemmaPath([f.first], f.scope).size).toBe(f.scope.size + 1)
  // The goal is satisfiable at g=1,a=1,b=1. Its conditional proof is not
  // an unconditional refutation of the negated cut (nor of the goal itself).
  expect(check(local(f.goal, f.first), f.first.tree, proofPath([], f.cut))).toBe(false)
  expect(check(f.goal, f.first.tree)).toBe(false)
})

test('a required prior cut is inlined into an independently checked lemma', () => {
  const f = chain(), lemma = f.secondCut
  expect(lemma.when.map(canon)).toEqual([canon(f.guard)])
  expect(lemma.slice).toEqual([1, 2])
  expect('split' in lemma.tree).toBe(true)
  if ('split' in lemma.tree) expect(canon(lemma.tree.split)).toBe(canon(f.cut))
  expect(check(local(f.goal, lemma), lemma.tree, proofPath(lemma.when, lemma.cut))).toBe(true)
  expect(check(local(f.goal, lemma), lemma.tree, proofPath([], lemma.cut))).toBe(false)
})

test('an unavailable or independently invalid prerequisite fails admission', () => {
  const f = chain()
  expect(admitConditionalCut(f.goal, f.secondSource, f.secondTree, f.scope, f.scope, f.second, [], until())).toBeUndefined()
  const invalid: LemmaCut = {...f.first, tree: {leaf: []}}
  expect(admitConditionalCut(f.goal, f.secondSource, f.secondTree, f.scope, f.scope, f.second, [invalid], until())).toBeUndefined()
  const inactive = put(new Map(), f.guard, false)
  expect(admitConditionalCut(f.goal, f.secondSource, f.secondTree, f.scope, inactive, f.second, [f.first], until())).toBeUndefined()
})

test('unneeded cuts are not inlined or checked and cannot make prerequisites active', () => {
  const f = fixture(), invalid: LemmaCut = {cut: v('bad'), when: [], tree: {leaf: []}}
  const again = admitConditionalCut(f.goal, f.source, f.tree, f.from, f.scope, f.cut, [invalid], until())!
  expect(again).toBeDefined()
  expect('leaf' in again.tree).toBe(true)
  const source: Goal = {name: f.goal.name, hyps: [le('b', 1), {op: '<=', a: n(2), b: x('b')}] }
  const tree = sumRows(source, new Map(), [f.second, flip(f.second)])
  const gated: LemmaCut = {cut: f.second, when: [f.cut], tree: {leaf: []}}
  expect(inlineConditionalCuts(f.goal, source, tree, new Map(), f.scope, [f.first, gated], until())).toBeUndefined()
})

test('inline emits an ordinary kernel-checked tree at scope with only needed active cuts', () => {
  const f = chain(), goal: Goal = {...f.goal, hyps: [...f.goal.hyps, {op: '<=', a: n(2), b: x('b')}] }
  const from = lemmaPath([f.first, f.secondCut], f.scope)
  const tree = sumRows(goal, from, [f.second, flip(f.second)])
  const out = inlineConditionalCuts(goal, goal, tree, from, f.scope, [f.first, f.secondCut], until())!
  expect(out).toBeDefined()
  expect(check(goal, out, f.scope)).toBe(true)
  expect(check(goal, out)).toBe(false)
  // The a cut lives inside b's independent proof, not as an extra outer split.
  if ('split' in out) expect(canon(out.split)).toBe(canon(f.second))
  else throw new Error('expected the required b cut')
  expect(inlineConditionalCuts(goal, goal, tree, from, f.scope, [], until())).toBeUndefined()
  expect(inlineConditionalCuts(goal, goal, tree, from, put(new Map(), f.guard, false), [f.first, f.secondCut], until())).toBeUndefined()
})

test('a selected active cut reuses a target negated bound that folds to false', () => {
  const f = chain(), negated = not(le('b', 1))
  const goal: Goal = {...f.goal, hyps: [...f.goal.hyps, negated]}
  // Query the source at the raw scope with the already proved good hypothesis.
  const source: Goal = {name: goal.name, hyps: [le('b', 1), negated]}
  const tree = sumRows(source, f.scope, [f.second, flip(f.second)])
  const extended = lemmaPath([f.secondCut], f.scope)
  expect(rowsAt(goal, extended).some(row => canon(row.lin) === canon(k(1)))).toBe(true)
  expect(inlineConditionalCuts(goal, source, tree, f.scope, f.scope, [], until())).toBeUndefined()
  const out = inlineConditionalCuts(goal, source, tree, f.scope, f.scope, [f.secondCut], until())!
  expect(out).toBeDefined()
  expect(check(goal, out, f.scope)).toBe(true)
  expect(check(goal, out)).toBe(false)
  if (!('split' in out)) throw new Error('expected the independently proved b cut')
  expect(canon(out.split)).toBe(canon(f.second))
  if (!('leaf' in out.yes)) throw new Error('expected one exact contradictory target input')
  expect(out.yes.leaf).toHaveLength(1)
  expect(out.yes.leaf[0]?.kind).toBe('input')
})

test('opaque columns, including nested opaque column names, cannot be cuts', () => {
  const goal: Goal = {name: 'opaque', hyps: []}
  const cuts: Lin[] = [{'⟦0⟧': 1}, {'M[⟦0⟧:1]': 1}]
  for (const cut of cuts) {
    expect(admitConditionalCut(goal, goal, {leaf: []}, new Map(), new Map(), cut, [], until())).toBeUndefined()
  }
})

test('duplicate path atoms preserve rows and negcut wins deciding lookups', () => {
  const goal: Goal = {name: 'duplicates', hyps: []}, cut = v('a')
  const scope: Path = new Map([[canon(cut), {lin: cut, holds: true}], ['@0', {lin: cut, holds: true}]])
  const from = proofPath([cut, cut], cut)
  const tree: Tree = {leaf: [{kind: 'input', index: 0}, {kind: 'input', index: 2}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}
  expect(check(goal, tree, from)).toBe(true)
  const lemma = admitConditionalCut(goal, goal, tree, from, scope, cut, [], until())!
  expect(lemma).toBeDefined()
  expect(lemma.when).toHaveLength(1)
  expect(check(goal, lemma.tree, proofPath(lemma.when, cut))).toBe(true)
  expect(check(goal, lemma.tree, proofPath([], cut))).toBe(false)
  const contradictory: Path = new Map([[canon(cut), {lin: cut, holds: false}], ['@0', {lin: cut, holds: true}]])
  const direct = sumRows(goal, contradictory, [flip(cut), cut])
  const out = inlineConditionalCuts(goal, goal, direct, contradictory, contradictory, [], until())!
  expect(out).toBeDefined()
  expect(check(goal, out, contradictory)).toBe(true)
})

test('inline may discharge an already false cut without emitting a repeated split', () => {
  const f = fixture(), scope = put(f.scope, f.cut, false), from = lemmaPath([f.first], scope)
  const tree = sumRows(f.goal, from, [f.cut, flip(f.cut)])
  const out = inlineConditionalCuts(f.goal, f.goal, tree, from, scope, [f.first], until())!
  expect(out).toBeDefined()
  expect(check(f.goal, out, scope)).toBe(true)
  expect('leaf' in out).toBe(true)
})

test('expired wall deadlines and unchecked source refutations return no result', () => {
  const f = fixture(), expired = performance.now() - 1
  expect(admitConditionalCut(f.goal, f.source, f.tree, f.from, f.scope, f.cut, [], expired)).toBeUndefined()
  expect(inlineConditionalCuts(f.goal, f.source, f.tree, f.from, f.scope, [f.first], expired)).toBeUndefined()
  expect(admitConditionalCut(f.goal, f.source, {leaf: []}, f.from, f.scope, f.cut, [], until())).toBeUndefined()
  expect(inlineConditionalCuts(f.goal, f.goal, {leaf: []}, f.scope, f.scope, [], until())).toBeUndefined()
})
