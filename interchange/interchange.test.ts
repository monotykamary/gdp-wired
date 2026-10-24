// The interchange format: certificates of each kind written and read back to the same objects, checked by the kernel
// through the standalone checker (in this process and as the bundled CLI in another), refused when tampered or outside
// the format, and their goals' trees checked by the second checker (python3) where it is installed.
import {expect, test} from 'bun:test'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {type Law, type Machine, atMost, get, ite, min, n, plus, x} from '../core/machine.ts'
import {type Fold, type Goal, type Loop, type QGoal, type Tree, canon, check, foldObligations, leafConstraints, loopObligations, termColumn} from '../kernel/kernel.ts'
import {type Lin, solve} from '../core/solver.ts'
import {grow, proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {growQ} from '../kernel/qprove.ts'
import {kindCases, recurRegressions, reseed} from '../core/conformance.ts'
import {q} from '../core/q.ts'
import {type Certificate, type Document, FormatError, fromInterchange, toInterchange} from './format.ts'
import {checkDocument, goalsOf} from './check.ts'

const cap: Machine = {name: 'cap', params: ['cap'], inputs: ['amt', 'k'], state: {used: n(0)}, maps: {M: 0},
  step: {state: {used: ite(atMost(plus(x('used'), x('amt')), x('cap')), plus(x('used'), x('amt')), x('used'))}, maps: {M: {key: x('k'), value: min(plus(get('M', x('k')), x('amt')), x('cap'))}}}}
const capLaws: Law[] = [{name: 'under', holds: atMost(x('used'), x('cap'))}, {name: 'cell', forall: 'j', holds: atMost(get('M', x('j')), x('cap'))}]
const budget: Machine = {name: 'budget', params: ['b', 'm'], inputs: ['c'], state: {s: n(0)}, step: {state: {s: ite({op: '<', a: x('s'), b: x('b')}, plus(x('s'), min(x('c'), x('m'))), x('s'))}}}
const trees = (goals: {name: string}[]) => Object.fromEntries(goals.map(g => { const o = grow(g as never); if (!('tree' in o)) throw new Error(`${g.name}: stuck`); return [g.name, o.tree] }))

function certificates(): Certificate[] {
  const env = process.env as Record<string, string | undefined>, was = env.GDP_CERT
  env.GDP_CERT = 'usual'
  const laws = proveLaws(cap, capLaws)
  const steps = proveStepLaws(cap, capLaws, [{name: 'used grows', then: atMost(x('used'), x("used'"))}])
  const twice = proveStepLaws(budget, [], [{name: 'two spend at most 2m', steps: 2, then: atMost(x("s'"), plus(x('s'), {op: 'mul', k: 2, a: x('m')}))}])
  // a tree that splits on a term column (min(a, b) ≤ 1 or not), each leaf's derivation found by the solver: the
  // document names the column by its term
  const cg: Goal = {name: 'a column', hyps: [atMost(n(1), min(x('a'), x('b'))), atMost(x('a'), n(0))]}
  const split: Lin = {[termColumn(min(x('a'), x('b')))]: 1, 1: -1}
  const leafAt = (holds: boolean): Tree => { const v = solve(leafConstraints(cg, new Map([[canon(split), {lin: split, holds}]]))); if (v.kind !== 'refuted') throw new Error('not refuted'); return {leaf: v.steps} }
  const colTree: Tree = {split, yes: leafAt(true), no: leafAt(false)}
  // (the cyclic certificate, made whatever the run's GDP_CERT: anything but usual)
  env.GDP_CERT = 'cyclic'
  const cyc = (proveLaws(cap, capLaws).proof as {cyclic?: import('../kernel/cyclic.ts').Cyclic} | undefined)?.cyclic
  if (was === undefined) delete env.GDP_CERT; else env.GDP_CERT = was
  const loop: Loop = {name: 'down', params: ['p'], inputs: [], state: {i: x('p')}, while: {op: '<', a: n(0), b: x('i')}, body: {i: {op: 'sub', a: x('i'), b: n(1)}}}
  const fold: Fold = {name: 'size', params: [], inputs: [], leaf: {s: n(1)}, node: {s: plus(plus(x('l_s'), x('r_s')), n(1))}}
  const foldLaws: Law[] = [{name: 'positive', holds: atMost(n(1), x('s'))}]
  reseed(7)
  const kc = kindCases(1)[0]!, rc = recurRegressions()[0]!
  const qg: QGoal = {name: 'q', hyps: [{op: '<=', a: {op: 'var', name: 'a'}, b: {op: 'const', q: q(1, 3)}}, {op: '<', a: {op: 'const', q: q(1, 2)}, b: {op: 'var', name: 'a'}}]}
  const qt = growQ(qg)
  if (!laws.proof || !steps.proof || !twice.proof || !cyc || !('tree' in qt)) throw new Error('a proof not made')
  return [
    {kind: 'laws', machine: cap, laws: capLaws, proof: {instances: laws.proof.instances, trees: laws.proof.trees}},
    {kind: 'stepLaws', machine: cap, laws: capLaws, stepLaws: [{name: 'used grows', then: atMost(x('used'), x("used'"))}], proof: steps.proof},
    {kind: 'stepLaws', machine: budget, laws: [], stepLaws: [{name: 'two spend at most 2m', steps: 2, then: atMost(x("s'"), plus(x('s'), {op: 'mul', k: 2, a: x('m')}))}], proof: twice.proof},
    {kind: 'cyclic', cyclic: cyc},
    {kind: 'loop', loop, laws: [], rank: x('i'), trees: trees(loopObligations(loop, [], x('i')))},
    {kind: 'fold', fold, laws: foldLaws, trees: trees(foldObligations(fold, foldLaws))},
    {kind: 'kInduction', machine: kc.m, laws: kc.laws, kInduction: kc.kl, proof: kc.proof},
    {kind: 'recur', loop: rc.loop, recur: rc.recur},
    {kind: 'qgoals', goals: [{goal: qg, tree: qt.tree}]},
    {kind: 'goals', goals: [{goal: cg, tree: colTree}]},
    {kind: 'goals', goals: [{goal: {name: 'g', hyps: [atMost(x('a'), n(2)), atMost(n(3), x('a'))]}, tree: trees([{name: 'g', hyps: [atMost(x('a'), n(2)), atMost(n(3), x('a'))]} as never]).g!}]},
  ]
}
const certs = certificates()
const docs = certs.map(c => JSON.parse(JSON.stringify(toInterchange(c))) as Document)

test('each certificate reads back to itself, and the kernel accepts it', () => {
  for (const [i, c] of certs.entries()) {
    expect(fromInterchange(docs[i])).toEqual(c)
    const r = checkDocument(docs[i])
    expect([c.kind, r.malformed, r.accepted]).toEqual([c.kind, undefined, true])
  }
})

test('tampered, a document is refused', () => {
  const t = (i: number, f: (d: Record<string, unknown>) => void) => { const d = JSON.parse(JSON.stringify(docs[i])) as Record<string, unknown>; f(d); return checkDocument(d).accepted }
  expect(t(0, d => { (d.laws as {holds: {b: unknown}}[])[0]!.holds.b = {op: 'const', value: 3} })).toBe(false) // a law changed
  expect(t(0, d => { (d.machine as {state: unknown[][]}).state[0]![1] = {op: 'const', value: 5} })).toBe(false) // the start changed
  expect(t(7, d => { (d.recur as {start: unknown[][]}).start = [['p', 0]] })).toBe(false) // a start whose stem ends outside the set
  const leaf = (x: unknown): {leaf: unknown[]} | undefined => (Array.isArray(x) ? x.map(leaf).find(Boolean) : x && typeof x === 'object' ? ('leaf' in x && Array.isArray((x as {leaf: unknown[]}).leaf) && (x as {leaf: unknown[]}).leaf.length > 1 ? x as {leaf: unknown[]} : Object.values(x).map(leaf).find(Boolean)) : undefined)
  for (const i of certs.keys()) expect([i, t(i, d => { leaf(d)?.leaf.pop() })]).toEqual([i, false]) // a derivation cut short
})

test('outside the format, a document is refused with where', () => {
  const bad = (f: (d: Record<string, unknown>) => void) => { const d = JSON.parse(JSON.stringify(docs[0])) as Record<string, unknown>; f(d); try { fromInterchange(d); return 'read' } catch (e) { return e instanceof FormatError ? 'refused' : 'threw' } }
  expect(bad(d => { d.version = '2.0' })).toBe('refused')
  expect(bad(d => { d.extra = 1 })).toBe('refused')
  expect(bad(d => { (d.machine as Record<string, unknown>).params = ['0'] })).toBe('refused') // a name a JavaScript object reorders
  expect(bad(d => { (d.machine as {state: unknown[]}).state.push(['used', {op: 'const', value: 0}]) })).toBe('refused') // a name twice
  expect(bad(d => { (d.machine as {state: unknown[][]}).state[0]![1] = {op: 'const', value: 0.5} })).toBe('refused') // not a natural
  expect(bad(d => { (d.machine as {state: unknown[][]}).state[0]![1] = {op: 'const', value: -1} })).toBe('refused')
  const withCols = docs.find(d => d.columns)!
  const noCols = JSON.parse(JSON.stringify(withCols)) as Record<string, unknown>
  delete noCols.columns
  expect(checkDocument(noCols).malformed).toContain('column')
})

test('another process (the bundled CLI, or the source) gives the same answers, and the second checker the same per goal', () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-ix-'))
  const files = docs.map((d, i) => { const f = join(dir, `${i}.json`); writeFileSync(f, JSON.stringify(d)); return f })
  const r = Bun.spawnSync(['bun', join(import.meta.dir, 'cli.ts'), '--json', ...files], {stdout: 'pipe'})
  expect((JSON.parse(r.stdout.toString()) as {report: {accepted: boolean}}[]).map(o => o.report.accepted)).toEqual(docs.map(() => true))
  const py = Bun.which('python3')
  if (!py) return
  for (const [i, c] of certs.entries()) {
    const g = goalsOf(c)
    if (g.kind !== 'goals' || !g.goals.length) continue
    const f = join(dir, `g${i}.json`)
    writeFileSync(f, JSON.stringify(toInterchange(g)))
    const out = Bun.spawnSync([py, join(import.meta.dir, 'py', 'check.py'), '--json', f], {stdout: 'pipe'})
    expect((JSON.parse(out.stdout.toString()) as [string, boolean][]).map(p => p[1])).toEqual(g.goals.map(x => check(x.goal, x.tree)))
  }
})
