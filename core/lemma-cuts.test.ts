import {expect, test} from 'bun:test'
import {type Goal, type Path, type Tree, canon, check, checkGoalLemmas} from '../kernel/kernel.ts'
import {v} from './solver.ts'
import {lemmaCutFixture} from '../lean-kernel/lemma-cases.ts'
import {shareLemmaCuts, setProofOrigin, proofOrigins, rememberProofRows} from './lemma-cuts.ts'
const f = lemmaCutFixture()
const put = (p: Path, lin: ReturnType<typeof v>, holds: boolean): Path => new Map(p).set(canon(lin), {lin, holds})
function repeated(g: Goal, root: Path, choice = f.c): Tree {
  const arm = (p: Path): Tree => {
    const no = put(p, f.a, false)
    return {split: f.a,
      yes: f.leaf(g, put(p, f.a, true), [f.a, f.flip(f.a)]),
      no: {split: f.b,
        yes: f.leaf(g, put(no, f.b, true), [f.ab, f.b, f.flip(f.a)]),
        no: f.leaf(g, put(no, f.b, false), [f.b, f.flip(f.b)])}}
  }
  return {split: choice, yes: arm(put(root, choice, true)), no: arm(put(root, choice, false))}
}

test('repeated forced splits become one independent checked lemma without search', () => {
  const g = {...f.goal, hyps: f.hyps.slice(0, 3)}, t = repeated(g, new Map())
  expect(check(g, t)).toBe(true)
  const shared = shareLemmaCuts(g, t, {minNodes: 1})
  expect(shared).toBeDefined()
  expect(shared!.stats.after).toBeLessThan(shared!.stats.before)
  expect(shared!.lemmas).toHaveLength(1)
  expect(shared!.lemmas[0]!.when).toHaveLength(0)
  expect(shared!.lemmas[0]!.slice).toEqual([0, 1])
  expect(checkGoalLemmas(shared!.goal, shared!.tree, shared!.lemmas)).toBe(true)
  expect(check(shared!.goal, shared!.tree)).toBe(false)
})

test('conditional input paths become explicit scope hypotheses and retain needed conditions', () => {
  const g: Goal = {...f.goal, hyps: [{op: 'or', xs: [{op: 'not', x: f.hyps[3]!}, f.hyps[0]!]}, ...f.hyps.slice(1, 3)]}
  const root = put(new Map(), f.c, true), t = repeated(g, root, v('choice'))
  expect(check(g, t, root)).toBe(true)
  const shared = shareLemmaCuts(g, t, {path: root, minNodes: 1})
  expect(shared).toBeDefined()
  expect(shared!.goal.hyps.length).toBe(g.hyps.length + 1)
  expect(shared!.lemmas[0]!.when.map(canon)).toContain(canon(f.c))
  expect(checkGoalLemmas(shared!.goal, shared!.tree, shared!.lemmas)).toBe(true)
  expect(checkGoalLemmas(shared!.goal, shared!.tree, shared!.lemmas.map(l => ({...l, when: []})))).toBe(false)
})

test('forged source provenance cannot become a checked lemma', () => {
  const g = {...f.goal, hyps: f.hyps.slice(0, 3)}, t = repeated(g, new Map())
  if (!('split' in t) || !('split' in t.yes) || !('split' in t.no)) throw Error('fixture shape')
  const forged = {goal: {name: 'forged', hyps: []}, tree: {leaf: []}, path: new Map()} satisfies Parameters<typeof setProofOrigin>[1]
  setProofOrigin(t.yes.no, forged); setProofOrigin(t.no.no, forged)
  expect(shareLemmaCuts(g, t, {minNodes: 1})).toBeUndefined()
})

test('row-cache hints are keyed by the exact goal and ordered source path', () => {
  const g = {...f.goal, hyps: f.hyps.slice(0, 3)}, t = repeated(g, new Map())
  const previous = proofOrigins.enabled
  proofOrigins.enabled = true
  const visit = (tree: Tree, path: Path): void => {
    if ('leaf' in tree) { rememberProofRows(tree, {...g}, path, []); return }
    visit(tree.yes, put(path, tree.split, true)); visit(tree.no, put(path, tree.split, false))
  }
  try {
    visit(t, new Map())
    const result = shareLemmaCuts(g, t, {minNodes: 1})
    expect(result).toBeDefined()
    expect(checkGoalLemmas(result!.goal, result!.tree, result!.lemmas)).toBe(true)
    const wrongOrder = (tree: Tree, path: Path): void => {
      if ('leaf' in tree) { rememberProofRows(tree, g, new Map([...path].reverse()), []); return }
      wrongOrder(tree.yes, put(path, tree.split, true)); wrongOrder(tree.no, put(path, tree.split, false))
    }
    wrongOrder(t, new Map())
    const ordered = shareLemmaCuts(g, t, {minNodes: 1})
    expect(ordered).toBeDefined()
    expect(checkGoalLemmas(ordered!.goal, ordered!.tree, ordered!.lemmas)).toBe(true)
  } finally { proofOrigins.enabled = previous }
})

test('forged matching row hints cannot bypass the trusted checker', () => {
  const g = {...f.goal, hyps: f.hyps.slice(0, 3)}, t = repeated(g, new Map())
  const previous = proofOrigins.enabled
  proofOrigins.enabled = true
  const visit = (tree: Tree, path: Path): void => {
    if ('leaf' in tree) { rememberProofRows(tree, g, path, []); return }
    visit(tree.yes, put(path, tree.split, true)); visit(tree.no, put(path, tree.split, false))
  }
  try { visit(t, new Map()); expect(shareLemmaCuts(g, t, {minNodes: 1})).toBeUndefined() }
  finally { proofOrigins.enabled = previous }
})

test('compression declines expired work and never certifies a satisfiable changed goal', () => {
  const g = {...f.goal, hyps: f.hyps.slice(0, 3)}, t = repeated(g, new Map())
  expect(shareLemmaCuts(g, t, {minNodes: 1, until: -1})).toBeUndefined()
  expect(shareLemmaCuts(g, t, {minNodes: 1, path: put(new Map(), v('M[0]'), true)})).toBeUndefined()
  expect(shareLemmaCuts({...g, hyps: [f.hyps[0]!, f.hyps[2]!]}, t, {minNodes: 1})).toBeUndefined()
})
