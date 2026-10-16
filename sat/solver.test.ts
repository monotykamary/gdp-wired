import {expect, test} from 'bun:test'
import {checkModel, checkProof} from './check.ts'
import {checkLrat} from './lrat.ts'
import {type Clause, type LratStep, type Result, type Step, solve} from './solver.ts'

// A seeded generator, so failures reproduce.
const rng = (seed: number) => () => ((seed = (seed * 1103515245 + 12345) & 0x7fffffff) / 0x80000000)
const random3 = (n: number, m: number, next: () => number): Clause[] =>
  Array.from({length: m}, () => Array.from({length: 3}, () => (Math.floor(next() * n) + 1) * (next() < 0.5 ? -1 : 1)))
const modes = ['backward', 'forward'] as const
// An answer checks: a model satisfies the formula, or both DRUP checkers and the LRAT checker accept its refutation.
const checks = (vars: number, cnf: Clause[], r: Result) =>
  r.kind === 'sat' ? checkModel(cnf, r.model) : r.kind === 'unsat' && modes.every(mode => checkProof(cnf, r.proof, mode)) && checkLrat(vars, cnf, r.lrat)

// Brute force for small n: is there a model?
function brute(n: number, clauses: Clause[]): boolean {
  for (let a = 0; a < 1 << n; a++) if (clauses.every(c => c.some(l => ((a >> (Math.abs(l) - 1)) & 1) === (l > 0 ? 1 : 0)))) return true
  return false
}

test('random 3-SAT, n = 16, against brute force, every checker', () => {
  const next = rng(1)
  for (let i = 0; i < 300; i++) {
    const cnf = random3(16, 68, next)
    const r = solve(16, cnf)
    expect(r.kind === 'sat').toBe(brute(16, cnf))
    expect(checks(16, cnf, r)).toBe(true)
  }
})

test('random 3-SAT near the threshold, n = 40..60, solver with and without its options: every answer checks', () => {
  const next = rng(7)
  const kinds = {sat: 0, unsat: 0, unknown: 0}
  for (let i = 0; i < 120; i++) {
    const n = 40 + Math.floor(next() * 21)
    const cnf = random3(n, Math.round(4.26 * n), next)
    const answers = [solve(n, cnf), solve(n, cnf, {minimize: false, reduce: false})]
    expect(answers[0]!.kind).toBe(answers[1]!.kind)
    for (const r of answers) {
      kinds[r.kind]++
      expect(checks(n, cnf, r)).toBe(true)
    }
  }
  expect(kinds.sat).toBeGreaterThan(10)
  expect(kinds.unsat).toBeGreaterThan(10)
})

// Pigeonhole: p pigeons in h holes, each pigeon somewhere, no two in one hole. Unsatisfiable when p > h.
function php(p: number, h: number): {vars: number, cnf: Clause[]} {
  const at = (i: number, j: number) => i * h + j + 1
  const cnf: Clause[] = []
  for (let i = 0; i < p; i++) cnf.push(Array.from({length: h}, (_, j) => at(i, j)))
  for (let j = 0; j < h; j++) for (let a = 0; a < p; a++) for (let b = a + 1; b < p; b++) cnf.push([-at(a, j), -at(b, j)])
  return {vars: p * h, cnf}
}

test('PHP(6, 5) and PHP(8, 7) are unsatisfiable, with proofs (and deletions) both checkers accept', () => {
  for (const [p, h] of [[6, 5], [8, 7]]) {
    const {vars, cnf} = php(p, h)
    const r = solve(vars, cnf)
    expect(r.kind).toBe('unsat')
    if (r.kind !== 'unsat') continue
    expect(checks(vars, cnf, r)).toBe(true)
    if (p === 8) expect(r.proof.some(s => !Array.isArray(s)) && r.lrat.some(s => 'del' in s)).toBe(true)
  }
})

test('tampering: no checker accepts a proof of a satisfiable formula, or a broken one', () => {
  const {vars, cnf} = php(6, 5)
  const r = solve(vars, cnf)
  if (r.kind !== 'unsat') throw new Error('PHP(6, 5) should be unsat')
  // Without one pigeon's "somewhere" clause the formula has a model, so nothing may refute it: neither the real proof
  // nor any tampered version of it.
  const weaker = cnf.slice(1)
  expect(solve(vars, weaker).kind).toBe('sat')
  const lemmas = r.proof.map((s, i) => [s, i] as const).filter(([s]) => Array.isArray(s) && s.length > 0)
  const tampered: Step[][] = [
    r.proof,
    ...lemmas.map(([, i]) => r.proof.filter((_, j) => j !== i)),
    ...lemmas.map(([s, i]) => r.proof.map((t, j) => (j === i ? [-(s as Clause)[0]!, ...(s as Clause).slice(1)] : t))),
  ]
  for (const mode of modes) for (const proof of tampered) expect(checkProof(weaker, proof, mode)).toBe(false)
  // On the real formula: the forward checker rejects any lemma that doesn't follow; the backward one only checks the
  // lemmas the empty clause depends on, so it may accept a proof whose broken lemma is never used (what remains is
  // still a proof). That it accepts nothing unsound is what the satisfiable case above tests.
  const counts = Object.fromEntries(modes.map(mode => [mode, tampered.slice(1).filter(proof => !checkProof(cnf, proof, mode)).length]))
  console.log(`PHP(6,5): ${lemmas.length} lemmas; of ${tampered.length - 1} tampered proofs, forward rejects ${counts.forward}, backward ${counts.backward}`)
  expect(counts.forward!).toBeGreaterThan(0)
  expect(counts.backward!).toBeGreaterThan(0)
  expect(counts.backward!).toBeLessThanOrEqual(counts.forward!)
  for (const mode of modes) {
    expect(checkProof(cnf, r.proof.slice(0, -1), mode)).toBe(false) // no empty clause
    expect(checkProof(cnf, [[1], []], mode)).toBe(false) // [1] doesn't follow
    expect(checkProof(cnf, [], mode)).toBe(false)
  }
})

test('deletions are honoured, and deleting what a later lemma needs makes it fail', () => {
  const cnf = [[1], [-1, 2], [-2]]
  for (const mode of modes) {
    expect(checkProof(cnf, [[]], mode)).toBe(true)
    expect(checkProof(cnf, [{d: [-2]}, []], mode)).toBe(false) // [1], [−1, 2] alone are satisfiable
    expect(checkProof(cnf, [{d: [5, 6]}, []], mode)).toBe(true) // deleting a clause that isn't there changes nothing
    expect(checkProof(cnf, [[2], {d: [-1, 2]}, []], mode)).toBe(true) // [2] was derived before the deletion
    expect(checkProof(cnf, [{d: [-1, 2]}, [2], []], mode)).toBe(false) // and can't be after it
  }
})

test('LRAT tampering: a wrong, dropped or reordered hint, or a changed lemma', () => {
  const {vars, cnf} = php(6, 5)
  const r = solve(vars, cnf)
  if (r.kind !== 'unsat') throw new Error('PHP(6, 5) should be unsat')
  expect(checkLrat(vars, cnf, r.lrat)).toBe(true)
  const at = r.lrat.map((s, i) => [s, i] as const).filter(([s]) => 'id' in s && s.hints.length > 1) as [Extract<LratStep, {id: number}>, number][]
  const edit = (i: number, f: (s: Extract<LratStep, {id: number}>) => LratStep) => r.lrat.map((t, j) => (j === i ? f(t as Extract<LratStep, {id: number}>) : t))
  const kinds: Record<string, LratStep[][]> = {
    'a wrong hint': at.map(([, i]) => edit(i, s => ({...s, hints: [s.hints[0]! === 1 ? 2 : 1, ...s.hints.slice(1)]}))),
    'a dropped hint': at.map(([, i]) => edit(i, s => ({...s, hints: s.hints.slice(0, -1)}))),
    'hints reversed': at.map(([, i]) => edit(i, s => ({...s, hints: [...s.hints].reverse()}))),
    'a literal negated': at.filter(([s]) => s.clause.length > 0).map(([, i]) => edit(i, s => ({...s, clause: [-s.clause[0]!, ...s.clause.slice(1)]}))),
    'a lemma dropped': at.map(([, i]) => r.lrat.filter((_, j) => j !== i)),
  }
  // The same formula with one pigeon's "somewhere" clause made a tautology: satisfiable, with every id where it was.
  const weaker = [[1, -1], ...cnf.slice(1)]
  expect(solve(vars, weaker).kind).toBe('sat')
  expect(checkLrat(vars, weaker, r.lrat)).toBe(false)
  expect(checkLrat(vars, cnf.slice(1), r.lrat)).toBe(false)
  const counts: string[] = []
  for (const [kind, proofs] of Object.entries(kinds)) {
    for (const proof of proofs) expect(checkLrat(vars, weaker, proof)).toBe(false)
    const rejected = proofs.filter(proof => !checkLrat(vars, cnf, proof)).length
    counts.push(`${kind} ${rejected}/${proofs.length}`)
    expect(rejected).toBeGreaterThan(proofs.length / 2)
  }
  console.log(`LRAT, PHP(6,5), rejected on the real formula: ${counts.join(', ')}`)
  expect(checkLrat(vars, cnf, r.lrat.slice(0, -1))).toBe(false) // no empty clause
  expect(checkLrat(vars, cnf, [...r.lrat.slice(0, -1), {...(r.lrat.at(-1) as Extract<LratStep, {id: number}>), hints: []}])).toBe(false)
  const reused = r.lrat.findIndex(s => 'id' in s && s.id > cnf.length + 1)
  expect(checkLrat(vars, cnf, edit(reused, s => ({...s, id: cnf.length + 1})))).toBe(false) // an id used twice
  expect(checkLrat(vars, [[1], [-1, 2], [-2]], [{id: 4, clause: [], hints: [1, 2, 3]}])).toBe(true)
  expect(checkLrat(vars, [[1], [-1, 2], [-2]], [{del: [3]}, {id: 4, clause: [], hints: [1, 2, 3]}])).toBe(false) // deleted
  expect(checkLrat(vars, [[1], [-1, 2], [-2]], [{id: 4, clause: [], hints: [2, 1, 3]}])).toBe(false) // [−1, 2] isn't unit first
  // Refutations found before any decision: an empty input clause, clashing units, a conflict from the units alone.
  for (const tiny of [[[]], [[1], [-1]], [[1], [-1, 2], [-2]], [[1, 2], [-1], [-2, 3], [-3, 1]]] as Clause[][]) {
    const t = solve(3, tiny)
    expect(t.kind === 'unsat' && checkLrat(3, tiny, t.lrat)).toBe(true)
  }
})

test('a wrong model is rejected', () => {
  const cnf = [[1, 2], [-1, 2], [-2, 3]]
  expect(checkModel(cnf, [false, true, true, true])).toBe(true)
  expect(checkModel(cnf, [false, true, false, true])).toBe(false)
})
