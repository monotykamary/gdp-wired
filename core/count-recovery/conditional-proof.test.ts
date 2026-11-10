import {expect, test} from 'bun:test'
import {type C, ite, n, not, x} from '../machine.ts'
import {type Lin, type Step, add, k, scale, sub, v} from '../solver.ts'
import {type Goal, type LemmaCut, type Path, type Tree, canon, check, checkGoalLemmas, leafConstraintsReusing as rowsAt, lemmaPath} from '../../kernel/kernel.ts'
import {checkConditionalProof, collectConditionalCertificate, conditionalProofStats, hasConditionalProof, markConditionalProof, transportConditionalProof} from './conditional-proof.ts'

const until = (): number => performance.now() + 2000
const le = (a: string, b: string | number): C => ({op: '<=', a: x(a), b: typeof b === 'number' ? n(b) : x(b)})
const ge = (a: string, b: number): C => ({op: '<=', a: n(b), b: x(a)})
const put = (path: Path, lin: Lin, holds = true): Path => new Map(path).set(canon(lin), {lin, holds})
const flip = (lin: Lin): Lin => add(k(1), scale(lin, -1))
const proofPath = (when: Lin[], cut: Lin): Path => {
  const path: Path = new Map()
  let duplicate = 0
  for (const atom of [{lin: cut, holds: false}, ...when.map(lin => ({lin, holds: true}))]) {
    const id = canon(atom.lin)
    path.set(path.has(id) ? `@${duplicate++}` : id, atom)
  }
  return path
}
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
function fixture(guarded = true) {
  const guard = v('g'), cut = sub(v('a'), k(1)), scope = put(new Map(), guard)
  const bound: C = guarded ? {op: '<=', a: x('a'), b: ite(le('g', 0), n(0), n(10))} : le('a', 0)
  const goal: Goal = {name: 'conditional metadata', hyps: [le('unused', 9), bound, ge('a', 2)]}
  const when = guarded ? [guard] : [], local = {...goal, hyps: [bound]}
  const lemma: LemmaCut = {when, cut, slice: [1], tree: sumRows(local, proofPath(when, cut), [v('a'), flip(cut)])}
  const tree = markConditionalProof(goal, sumRows(goal, lemmaPath([lemma], scope), [cut, sub(k(2), v('a'))]), [lemma])
  return {goal, guard, cut, scope, lemma, tree}
}

test('metadata is untrusted, root-local, and checked under ordinary entry paths', () => {
  const f = fixture()
  expect(hasConditionalProof(f.tree)).toBe(true)
  expect(checkConditionalProof(f.goal, f.tree, f.scope)).toBe(true)
  expect(check(f.goal, f.tree, f.scope)).toBe(false)
  expect(checkConditionalProof(f.goal, f.tree)).toBe(false)
  const copy = {...f.tree}
  expect(hasConditionalProof(copy)).toBe(false)
  expect(checkConditionalProof(f.goal, copy, f.scope)).toBe(false)
  expect(collectConditionalCertificate(f.goal, f.tree, until())).toBeUndefined()
})

test('mixed ordinary and conditional siblings globalize at an empty root', () => {
  const f = fixture(false), noPath = put(new Map(), f.guard, false)
  const no = sumRows(f.goal, noPath, [v('a'), sub(k(2), v('a'))])
  const tree: Tree = {split: f.guard, yes: f.tree, no}
  expect(hasConditionalProof(tree)).toBe(true)
  expect(checkConditionalProof(f.goal, tree)).toBe(true)
  const out = collectConditionalCertificate(f.goal, tree, until())!
  expect(out).toBeDefined()
  expect(out.lemmas).toHaveLength(1)
  expect(out.lemmas[0]!.when.map(canon)).toEqual([canon(f.guard)])
  expect(lemmaPath(out.lemmas, noPath)).toBe(noPath)
  expect(checkGoalLemmas(f.goal, out.tree, out.lemmas)).toBe(true)
  expect(hasConditionalProof(out.tree)).toBe(false)
})

test('rootless conditional cuts keep their guards as well as the subtree entry scope', () => {
  const f = fixture(), noPath = put(new Map(), f.guard, false)
  const goal: Goal = {...f.goal, hyps: [...f.goal.hyps, {op: '<=', a: x('b'), b: ite(le('g', 0), n(10), n(0))}, ge('b', 1)]}
  const yes = transportConditionalProof(f.goal, goal, f.tree, f.scope, f.scope, until())!
  expect(yes).toBeDefined()
  const no = sumRows(goal, noPath, [v('b'), sub(k(1), v('b'))])
  const tree: Tree = {split: f.guard, yes, no}
  const out = collectConditionalCertificate(goal, tree, until())!
  expect(out).toBeDefined()
  expect(out.lemmas[0]!.when.map(canon)).toEqual([canon(f.guard), canon(f.guard)])
  expect(checkGoalLemmas(goal, out.tree, out.lemmas)).toBe(true)
  expect(lemmaPath(out.lemmas, noPath)).toBe(noPath)
})

test('cross-goal added and reordered hypotheses preserve independent slices', () => {
  const f = fixture(), target: Goal = {...f.goal, hyps: [ge('irrelevant', 5), f.goal.hyps[2]!, f.goal.hyps[0]!, f.goal.hyps[1]!]}
  const moved = transportConditionalProof(f.goal, target, f.tree, f.scope, f.scope, until())!
  expect(moved).toBeDefined()
  expect(checkConditionalProof(target, moved, f.scope)).toBe(true)
  expect(checkConditionalProof(target, f.tree, f.scope)).toBe(false)
  // Use an unconditional fixture to inspect the exported slice at the root.
  const u = fixture(false), whole: Goal = {...u.goal, hyps: [ge('irrelevant', 5), u.goal.hyps[2]!, u.goal.hyps[0]!, u.goal.hyps[1]!]}
  const root = transportConditionalProof(u.goal, whole, u.tree, u.scope, new Map(), until())!
  expect(root).toBeDefined()
  const out = collectConditionalCertificate(whole, root, until())!
  expect(out.lemmas[0]!.slice).toEqual([3])
  expect(checkGoalLemmas(whole, out.tree, out.lemmas)).toBe(true)
})

test('unsliced source cuts become explicit slices and do not assume added hypotheses', () => {
  const f = fixture(false), local = {...f.goal, hyps: [f.goal.hyps[1]!]}
  const lemma: LemmaCut = {when: [], cut: f.cut, tree: sumRows(local, proofPath([], f.cut), [v('a'), flip(f.cut)])}
  const source: Goal = {...local, hyps: [...local.hyps, ge('a', 2)]}
  // Build the unsliced independent proof under precisely its source goal.
  lemma.tree = sumRows(source, proofPath([], f.cut), [v('a'), flip(f.cut)])
  const root = markConditionalProof(source, sumRows(source, lemmaPath([lemma], new Map()), [f.cut, sub(k(2), v('a'))]), [lemma])
  const target: Goal = {...source, hyps: [le('extra', 7), source.hyps[1]!, source.hyps[0]!]}
  const moved = transportConditionalProof(source, target, root, new Map(), new Map(), until())!
  const out = collectConditionalCertificate(target, moved, until())!
  expect(out.lemmas[0]!.slice).toEqual([2, 1])
  expect(checkGoalLemmas(target, out.tree, out.lemmas)).toBe(true)
})

test('inactive cuts cannot be used or activated by another cut', () => {
  const f = fixture(), wrong = put(new Map(), f.guard, false)
  expect(checkConditionalProof(f.goal, f.tree, wrong)).toBe(false)
  expect(transportConditionalProof(f.goal, f.goal, f.tree, f.scope, wrong, until())).toBeUndefined()
  const second: LemmaCut = {when: [f.cut], cut: v('b'), slice: [], tree: sumRows({name: 'empty', hyps: []}, proofPath([f.cut], v('b')), [flip(v('b')), scale(v('b'), -1)])}
  // b <= 0 is independently true under naturals only if b=0 is assumed;
  // this malformed proof must be refused, even though its guard is inactive.
  const invalid = markConditionalProof(f.goal, {...f.tree}, [f.lemma, second])
  expect(checkConditionalProof(f.goal, invalid, f.scope)).toBe(false)
  const validDependent: LemmaCut = {when: [f.cut], cut: f.cut, slice: [], tree: sumRows({name: 'empty', hyps: []}, proofPath([f.cut], f.cut), [flip(f.cut), f.cut])}
  const path = lemmaPath([f.lemma, validDependent], f.scope)
  expect(path.size).toBe(f.scope.size + 1)
})

test('missing target rows and missing source-slice hypotheses refuse exact transport', () => {
  const f = fixture(), missingMain: Goal = {...f.goal, hyps: f.goal.hyps.slice(0, 2)}
  expect(transportConditionalProof(f.goal, missingMain, f.tree, f.scope, f.scope, until())).toBeUndefined()
  const missingLemma: Goal = {...f.goal, hyps: [f.goal.hyps[0]!, f.goal.hyps[2]!]}
  expect(transportConditionalProof(f.goal, missingLemma, f.tree, f.scope, f.scope, until())).toBeUndefined()
  expect(transportConditionalProof(f.goal, f.goal, {leaf: [{kind: 'input', index: -1}]}, f.scope, f.scope, until())).toBeUndefined()
})

test('removed guard hypotheses are discharged by explicit entry conditions, not assumed', () => {
  const guard = v('g'), cut = sub(v('a'), k(1)), scope = put(new Map(), guard)
  const goal: Goal = {name: 'guard discharge', hyps: [le('a', 'g'), ge('a', 2)]}
  const source: Goal = {...goal, hyps: [le('g', 0), ...goal.hyps]}
  const local = {...source, hyps: source.hyps.slice(0, 2)}
  const lemma: LemmaCut = {when: [], cut, slice: [0, 1], tree: sumRows(local, proofPath([], cut), [guard, sub(v('a'), guard), flip(cut)])}
  const tree = markConditionalProof(source, sumRows(source, lemmaPath([lemma], scope), [cut, sub(k(2), v('a'))]), [lemma])
  expect(checkConditionalProof(source, tree, scope)).toBe(true)
  const moved = transportConditionalProof(source, goal, tree, scope, scope, until())!
  expect(moved).toBeDefined()
  expect(checkConditionalProof(goal, moved, scope)).toBe(true)
  expect(checkConditionalProof(goal, moved)).toBe(false)
  expect(transportConditionalProof(source, goal, tree, scope, new Map(), until())).toBeUndefined()
  const unrelated: Goal = {...source, hyps: [...source.hyps, le('unmapped', 42)]}
  const extra: LemmaCut = {...lemma, slice: [0, 1, 3], tree: sumRows({...unrelated, hyps: [unrelated.hyps[0]!, unrelated.hyps[1]!, unrelated.hyps[3]!]}, proofPath([], cut), [guard, sub(v('a'), guard), flip(cut)])}
  const unused = markConditionalProof(unrelated, sumRows(unrelated, lemmaPath([extra], scope), [cut, sub(k(2), v('a'))]), [extra])
  expect(checkConditionalProof(unrelated, unused, scope)).toBe(true)
  expect(transportConditionalProof(unrelated, goal, unused, scope, scope, until())).toBeUndefined()
  const contradictory: Goal = {...goal, hyps: [...goal.hyps, {op: '<=', a: n(1), b: ite(le('g', 0), n(1), n(0))}]}
  const yes = transportConditionalProof(goal, contradictory, moved, scope, scope, until())!
  const noPath = put(new Map(), guard, false), no = sumRows(contradictory, noPath, [k(1)])
  const out = collectConditionalCertificate(contradictory, {split: guard, yes, no}, until())!
  expect(out).toBeDefined()
  expect(out.lemmas[0]!.slice).toEqual([0])
  expect(out.lemmas[0]!.when.map(canon)).toEqual([canon(guard), canon(guard)])
  expect(checkGoalLemmas(contradictory, out.tree, out.lemmas)).toBe(true)
})

test('malformed independent cuts are refused by checking, transport and collection', () => {
  const f = fixture(false)
  for (const lemma of [{...f.lemma, tree: {leaf: []}}, {...f.lemma, slice: [-1]}, {...f.lemma, slice: [99]}, {...f.lemma, cut: {a: Infinity}}]) {
    const tree = markConditionalProof(f.goal, {...f.tree}, [lemma])
    expect(checkConditionalProof(f.goal, tree, f.scope)).toBe(false)
    expect(transportConditionalProof(f.goal, f.goal, tree, f.scope, f.scope, until())).toBeUndefined()
    expect(collectConditionalCertificate(f.goal, tree, until())).toBeUndefined()
  }
})

test('constant-positive target row short-circuits obsolete source rows', () => {
  const f = fixture(false), goal: Goal = {...f.goal, hyps: [f.goal.hyps[1]!, not(le('a', 1))]}
  const source: Goal = {...goal, hyps: [le('a', 1), ge('a', 2)]}
  const lemma = {...f.lemma, slice: [0], tree: sumRows({...source, hyps: [source.hyps[0]!] }, proofPath([], f.cut), [f.cut, flip(f.cut)])}
  const plain = sumRows(source, lemmaPath([lemma], new Map()), [f.cut, sub(k(2), v('a'))])
  const markedSource = markConditionalProof(source, plain, [lemma])
  expect(checkConditionalProof(source, markedSource)).toBe(true)
  // Preserve the slice's hypothesis while adding a negation that folds to false.
  const target: Goal = {...source, hyps: [...source.hyps, goal.hyps[1]!]}
  const out = transportConditionalProof(source, target, markedSource, new Map(), new Map(), until())!
  expect(out).toBeDefined()
  expect('leaf' in out && out.leaf).toHaveLength(1)
  expect(checkConditionalProof(target, out)).toBe(true)
})

test('duplicate path atoms keep rows and negcut-first lookup semantics', () => {
  const cut = v('a'), goal: Goal = {name: 'duplicate atoms', hyps: []}
  const scope: Path = new Map([[canon(cut), {lin: cut, holds: true}], ['@0', {lin: cut, holds: true}]])
  const lemma: LemmaCut = {when: [cut, cut], cut, slice: [], tree: sumRows(goal, proofPath([cut, cut], cut), [flip(cut), cut])}
  const contradictory: Path = new Map([[canon(cut), {lin: cut, holds: false}], ['@0', {lin: cut, holds: true}]])
  const ordinary = sumRows(goal, contradictory, [flip(cut), cut])
  const moved = transportConditionalProof(goal, goal, ordinary, contradictory, contradictory, until())!
  expect(check(goal, moved, contradictory)).toBe(true)
  const invalid = markConditionalProof(goal, sumRows(goal, lemmaPath([lemma], scope), [cut, scale(cut, -1)]), [lemma])
  expect(checkConditionalProof(goal, invalid, scope)).toBe(false)
  const truth = markConditionalProof(goal, ordinary, [lemma])
  // The first a atom is false: the duplicate true atom cannot activate this cut.
  expect(lemmaPath([lemma], contradictory)).toBe(contradictory)
  expect(checkConditionalProof(goal, truth, contradictory)).toBe(true)
  expect(transportConditionalProof(goal, goal, truth, contradictory, contradictory, until())).toBeDefined()
})

test('ordinary siblings reindex when global cuts change their leaf rows', () => {
  const f = fixture(false), noPath = put(new Map(), f.guard, false)
  const no = sumRows(f.goal, noPath, [v('a'), sub(k(2), v('a'))])
  // The root's cut is inherited by yes, but a nested empty mark resets no to
  // ordinary rows. Exporting the root cut shifts that formerly ordinary leaf.
  const rootPath = new Map<string, {lin: Lin, holds: boolean}>()
  const yes = sumRows(f.goal, lemmaPath([f.lemma], f.scope), [f.cut, sub(k(2), v('a'))])
  const tree = markConditionalProof(f.goal, {split: f.guard, yes, no: markConditionalProof(f.goal, no, [])}, [f.lemma])
  expect(checkConditionalProof(f.goal, tree, rootPath)).toBe(true)
  const out = collectConditionalCertificate(f.goal, tree, until())!
  expect(out).toBeDefined()
  expect(checkGoalLemmas(f.goal, out.tree, out.lemmas)).toBe(true)
  if (!('split' in out.tree)) throw new Error('expected split')
  expect(out.tree.no).not.toEqual(no)
})

test('transport can prune a known split without losing a descendant mark', () => {
  const f = fixture(false), noPath = put(new Map(), f.guard, false)
  const no = sumRows(f.goal, noPath, [v('a'), sub(k(2), v('a'))])
  const tree: Tree = {split: f.guard, yes: f.tree, no}
  const moved = transportConditionalProof(f.goal, f.goal, tree, new Map(), f.scope, until())!
  expect(moved).toBeDefined()
  expect('leaf' in moved).toBe(true)
  expect(hasConditionalProof(moved)).toBe(true)
  expect(checkConditionalProof(f.goal, moved, f.scope)).toBe(true)
})

test('ordinary square and product references follow the relocated base rows', () => {
  const goal: Goal = {name: 'products', hyps: [le('a', 0), ge('a', 2)]}, target: Goal = {...goal, hyps: [le('extra', 4), ...goal.hyps]}
  const path = put(new Map(), v('g')), rows = rowsAt(goal, path)
  const a = rows.findIndex(row => canon(row.lin) === canon(v('a'))), lower = rows.findIndex(row => canon(row.lin) === canon(sub(k(2), v('a'))))
  const tree: Tree = {squares: [v('a')], products: [[a, lower], [rows.length, rows.length + 1]], leaf: [{kind: 'input', index: a}, {kind: 'input', index: lower}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}
  expect(check(goal, tree, path)).toBe(true)
  const out = transportConditionalProof(goal, target, tree, path, path, until())!
  expect(check(target, out, path)).toBe(true)
  if (!('leaf' in out)) throw new Error('expected leaf')
  const after = rowsAt(target, path).length
  expect(out.products?.[1]).toEqual([after, after + 1])
  expect(out.squares).toEqual(tree.squares)
})

test('ordinary checking retains the kernel constant and repeated split refusals', () => {
  const goal: Goal = {name: 'false', hyps: [{op: '<=', a: n(1), b: n(0)}]}, leaf = sumRows(goal, new Map(), [k(1)])
  expect(checkConditionalProof(goal, leaf)).toBe(true)
  expect(checkConditionalProof(goal, {split: k(0), yes: leaf, no: leaf})).toBe(false)
  const guard = v('g'), branch: Tree = {split: guard, yes: leaf, no: leaf}
  expect(checkConditionalProof(goal, branch, put(new Map(), guard))).toBe(false)
})

test('retarget cache hits across unrelated scopes and equivalent target objects', () => {
  const f=fixture(false), before=conditionalProofStats()
  for(const name of ['left','right','third']){
    const target:Goal={...f.goal,name,hyps:[...f.goal.hyps]}, path=put(f.scope,v(name))
    const moved=transportConditionalProof(f.goal,target,f.tree,f.scope,path,until())
    expect(moved).toBeDefined();expect(checkConditionalProof(target,moved!,path)).toBe(true)
    const root=transportConditionalProof(target,target,moved!,path,new Map(),until())!
    const out=collectConditionalCertificate(target,root,until())!
    expect(checkGoalLemmas(target,out.tree,out.lemmas)).toBe(true)
  }
  const after=conditionalProofStats()
  expect(after.retargetHits-before.retargetHits).toBeGreaterThanOrEqual(2)
  expect(after.independentHits-before.independentHits).toBeGreaterThan(0)
})

test('retarget cache distinguishes slice vectors and never covers missing hypotheses', () => {
  const f=fixture(false), first=transportConditionalProof(f.goal,f.goal,f.tree,f.scope,f.scope,until())!
  expect(first).toBeDefined()
  const before=conditionalProofStats(), reordered:Goal={...f.goal,hyps:[f.goal.hyps[1]!,f.goal.hyps[2]!,f.goal.hyps[0]!]}
  const moved=transportConditionalProof(f.goal,reordered,f.tree,f.scope,f.scope,until())!
  expect(moved).toBeDefined();expect(checkConditionalProof(reordered,moved,f.scope)).toBe(true)
  expect(conditionalProofStats().retargetHits-before.retargetHits).toBe(0)
  const missing:Goal={...f.goal,hyps:[f.goal.hyps[0]!,f.goal.hyps[2]!]}
  expect(transportConditionalProof(f.goal,missing,f.tree,f.scope,f.scope,until())).toBeUndefined()
  expect(transportConditionalProof(f.goal,f.goal,f.tree,f.scope,f.scope,performance.now()-1)).toBeUndefined()
})

test('retarget cache does not alias equal slice vectors with different source content', () => {
  const f=fixture(false)
  expect(transportConditionalProof(f.goal,f.goal,f.tree,f.scope,f.scope,until())).toBeDefined()
  const other:Goal={...f.goal,hyps:[f.goal.hyps[0]!,le('a',1),f.goal.hyps[2]!]}
  const tree=markConditionalProof(other,{...f.tree},[f.lemma]), before=conditionalProofStats()
  expect(checkConditionalProof(other,tree,f.scope)).toBe(true)
  const moved=transportConditionalProof(other,other,tree,f.scope,f.scope,until())
  expect(moved).toBeDefined();expect(checkConditionalProof(other,moved!,f.scope)).toBe(true)
  expect(conditionalProofStats().retargetHits-before.retargetHits).toBe(0)
})

test('warm pre-check caches do not replace final kernel verification', () => {
  const f=fixture(false)
  expect(checkConditionalProof(f.goal,f.tree,f.scope)).toBe(true)
  const root=transportConditionalProof(f.goal,f.goal,f.tree,f.scope,new Map(),until())!
  const out=collectConditionalCertificate(f.goal,root,until())!
  expect(checkGoalLemmas(f.goal,out.tree,out.lemmas)).toBe(true)
  expect(checkGoalLemmas(f.goal,{leaf:[]},out.lemmas)).toBe(false)
  const corrupt=out.lemmas.map(l=>({...l,tree:{leaf:[]} as Tree}))
  expect(checkGoalLemmas(f.goal,out.tree,corrupt)).toBe(false)
})

test('expired absolute wall deadlines never produce certificates', () => {
  const f = fixture(false), expired = performance.now() - 1
  expect(transportConditionalProof(f.goal, f.goal, f.tree, f.scope, f.scope, expired)).toBeUndefined()
  expect(collectConditionalCertificate(f.goal, f.tree, expired)).toBeUndefined()
  expect(transportConditionalProof(f.goal, f.goal, f.tree, f.scope, f.scope, NaN)).toBeUndefined()
  expect(collectConditionalCertificate(f.goal, f.tree, NaN)).toBeUndefined()
})
