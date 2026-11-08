import {expect, test} from 'bun:test'
import {type C, type Law, type Machine, atMost, n, x} from '../core/machine.ts'
import {type Lin, type Step, add, k, scale, sub, v} from '../core/solver.ts'
import {type CountCert, type Goal, type LemmaCut, type Path, type Tree, canon, check, checkCounted, checkCountedLaws, checkGoalLemmas, checkMC, countedObligations, leafConstraints, lemmaPath, mcGoal} from './kernel.ts'

const flip = (r: Lin): Lin => add(k(1), scale(r, -1))
const a = v('a'), b = v('b'), c = v('c'), ab = sub(a, b)
const hyps: C[] = [
  {op: '<=', a: {op: 'var', name: 'a'}, b: {op: 'var', name: 'b'}},
  {op: '<=', a: {op: 'var', name: 'b'}, b: {op: 'const', value: 0}},
  {op: '<', a: {op: 'const', value: 0}, b: {op: 'var', name: 'a'}},
  {op: '<=', a: {op: 'var', name: 'c'}, b: {op: 'const', value: 0}},
]
const goal: Goal = {name: 'conditional cut', hyps}
const decide = (r: Lin, holds: boolean): Path => new Map([[canon(r), {lin: r, holds}]])
function leaf(g: Goal, path: Path, wanted: Lin[]): Tree {
  const rows = leafConstraints(g, path)
  const steps: Step[] = wanted.map(lin => {
    const index = rows.findIndex(r => canon(r.lin) === canon(lin))
    if (index < 0) throw Error('test input row missing: ' + canon(lin))
    return {kind: 'input', index}
  })
  steps.push({kind: 'combine', a: 0, b: 1, ma: 1, mb: 1})
  if (wanted.length === 3) steps.push({kind: 'combine', a: 3, b: 2, ma: 1, mb: 1})
  return {leaf: steps}
}
const proofPath = decide(a, false)
proofPath.set(canon(c), {lin: c, holds: true})
const entry: LemmaCut = {when: [c], cut: a, slice: [0, 1], tree: leaf({...goal, hyps: hyps.slice(0, 2)}, proofPath, [ab, b, flip(a)])}
const yes = decide(c, true), no = decide(c, false)
const tree: Tree = {split: c, yes: leaf(goal, lemmaPath([entry], yes), [a, flip(a)]), no: leaf(goal, no, [c, flip(c)])}
const legacy = leaf(goal, new Map(), [ab, b, flip(a)])

test('a separately checked conditional lemma closes only below its decision', () => {
  expect(checkGoalLemmas(goal, tree, [entry])).toBe(true)
  expect(check(goal, tree)).toBe(false)
  expect(checkGoalLemmas(goal, tree, [])).toBe(false)
  expect(checkGoalLemmas(goal, tree.yes, [entry])).toBe(false)
  expect(checkGoalLemmas(goal, tree, [{...entry, when: [flip(c)]}])).toBe(false)
})

test('empty lemma lists preserve the original goal and counted checkers', () => {
  expect(check(goal, legacy)).toBe(true)
  expect(checkGoalLemmas(goal, legacy)).toBe(true)
  expect(checkCounted({...goal, counts: []}, {insts: [], tree: legacy})).toBe(true)
  expect(checkCounted({...goal, counts: []}, {insts: [], tree: legacy, lemmas: []})).toBe(true)
  expect(checkMC(hyps, [], {reads: [], insts: [], tree: legacy})).toBe(true)
  expect(checkMC(hyps, [], {reads: [], insts: [], tree: legacy, lemmas: []})).toBe(true)
})

test('the actual counted and MC wrappers carry the lemma list', () => {
  expect(checkCounted({...goal, counts: []}, {insts: [], tree, lemmas: [entry]})).toBe(true)
  expect(checkMC(hyps, [], {reads: [], insts: [], tree, lemmas: [entry]})).toBe(true)
})

test('a lemma is checked against exactly its selected hypotheses', () => {
  expect(checkGoalLemmas(goal, tree, [{...entry, slice: [0, 3]}])).toBe(false)
  for (const index of [-1, 40, 0.5, NaN, Infinity]) expect(checkGoalLemmas(goal, tree, [{...entry, slice: [0, index]}])).toBe(false)
})

test('non-refuting, self-citing and circular lemma payloads are refused', () => {
  expect(checkGoalLemmas(goal, tree, [{...entry, tree: {leaf: []}}])).toBe(false)
  const self = {...entry, tree: {lemma: 0} as unknown as Tree}
  expect(checkGoalLemmas(goal, tree, [self])).toBe(false)
  expect(checkGoalLemmas(goal, tree, [self, {...entry, tree: {lemma: 1} as unknown as Tree}])).toBe(false)
})

test('read capture is still refused with a nonempty valid lemma list', () => {
  const decl = {map: 'total', j: 'j', key: 'i', below: n(1), body: n(0)}
  const cert: CountCert = {reads: [['fresh', 'total', n(0)]], insts: [], tree, lemmas: [entry]}
  const expanded = mcGoal(hyps, [decl], cert)!
  cert.tree = {split: c, yes: leaf(expanded, lemmaPath([entry], yes), [a, flip(a)]), no: leaf(expanded, no, [c, flip(c)])}
  expect(checkMC(hyps, [decl], cert)).toBe(true)
  const captured: CountCert = {...cert, reads: [['a', 'total', n(0)]]}
  expect(checkMC(hyps, [decl], captured)).toBe(false)
})

test('witness capture of parameters, ?flag names and law skolems remains refused', () => {
  const m: Machine = {name: 'capture control', params: ['p'], inputs: [], state: {}, pre: atMost(x('p'), x('p')), step: {flags: {flag: atMost(n(0), n(0))}}}
  const laws: Law[] = [{name: 'tautology', forall: 'key', holds: atMost(n(0), n(0))}]
  const inactive: LemmaCut = {when: [k(1)], cut: {}, slice: [], tree: {leaf: [{kind: 'input', index: 0}]}}
  const certs: Record<string, CountCert> = {}
  for (const {goal: g, decls} of countedObligations(m, laws, {})) {
    const partial = {reads: [], insts: [{wit: 'fresh', below: n(0), terms: [], unit: 0}]} satisfies Omit<CountCert, 'tree'>
    const expanded = mcGoal(g.hyps, decls, partial)!
    const index = leafConstraints(expanded, new Map()).findIndex(r => canon(r.lin) === canon(k(1)))
    expect(index).toBeGreaterThanOrEqual(0)
    certs[g.name] = {...partial, tree: {leaf: [{kind: 'input', index}]}, lemmas: [inactive]}
  }
  expect(checkCountedLaws(m, laws, {instances: {}, certs})).toBe(true)
  for (const wit of ['p', '?flag', 'key#']) {
    const changed = Object.fromEntries(Object.entries(certs).map(([name, c]) => [name, {...c, insts: c.insts.map(i => ({...i, wit}))}]))
    expect(checkCountedLaws(m, laws, {instances: {}, certs: changed})).toBe(false)
  }
})

test('malformed new fields do not grant assumptions or throw', () => {
  expect(checkGoalLemmas(goal, tree, null as unknown as LemmaCut[])).toBe(false)
  expect(checkGoalLemmas(goal, tree, new Array<LemmaCut>(1))).toBe(false)
  expect(checkGoalLemmas(goal, tree, [{...entry, when: new Array<Lin>(1)}])).toBe(false)
  expect(checkGoalLemmas(goal, tree, [{...entry, cut: {a: NaN}}])).toBe(false)
  expect(checkGoalLemmas(goal, tree, [{...entry, cut: {a: Number.MAX_SAFE_INTEGER + 1}}])).toBe(false)
})
