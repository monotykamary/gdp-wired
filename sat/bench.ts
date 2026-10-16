// Harder honest benchmarks: solve time, proof size, and the check three ways (DRUP forward: every lemma; DRUP backward:
// only the lemmas the empty clause depends on; LRAT: the solver's hints, no search). `bun bench.ts [limit] [name regex]`,
// limit = the solver's conflict budget per problem; NO_DRUP=1 skips both DRUP checks, CHECKS=lrat,backward,forward picks.
// SOLVER=v1 runs the previous solver (solver-v1.ts); RESTARTS=luby uses Luby restarts instead of glucose-style;
// TUNE='{"lubyUnit":256,"decay":0.9}' sets the solver's tuning options.
import {checkModel, checkProof} from './check.ts'
import {checkLrat} from './lrat.ts'
import {type Clause, type Options, solve as solveV2} from './solver.ts'
import {solve as solveV1} from './solver-v1.ts'
import {Circuit, type Vec} from './cnf.ts'

// a × b by shift-and-add, modulo 2^width.
const mul = (g: Circuit, a: Vec, b: Vec): Vec => b.reduce((acc, bit, i) => g.add(acc, g.bite(bit, g.shl(a, i), g.const(a.length, 0n))), g.const(a.length, 0n))
const circuit = (build: (g: Circuit) => number) => { const g = new Circuit(); g.assert(build(g)); return {vars: g.vars, cnf: g.clauses} }
function php(p: number, h: number): {vars: number, cnf: Clause[]} {
  const at = (i: number, j: number) => i * h + j + 1
  const cnf: Clause[] = []
  for (let i = 0; i < p; i++) cnf.push(Array.from({length: h}, (_, j) => at(i, j)))
  for (let j = 0; j < h; j++) for (let a = 0; a < p; a++) for (let b = a + 1; b < p; b++) cnf.push([-at(a, j), -at(b, j)])
  return {vars: p * h, cnf}
}

export const problems: [string, () => {vars: number, cnf: Clause[]}][] = [
  ['a + b = b + a, 32 bits', () => circuit(g => { const a = g.input(32), b = g.input(32); return -g.eq(g.add(a, b), g.add(b, a)) })],
  ['(a + b) + c = a + (b + c), 16 bits', () => circuit(g => { const [a, b, c] = [g.input(16), g.input(16), g.input(16)]; return -g.eq(g.add(g.add(a, b), c), g.add(a, g.add(b, c))) })],
  ['a < b, b < c imply a < c, 32 bits', () => circuit(g => { const [a, b, c] = [g.input(32), g.input(32), g.input(32)]; return g.every([g.ult(a, b), g.ult(b, c), -g.ult(a, c)]) })],
  ...[6, 8, 10, 12, 16].map(w => [`a × b = b × a, ${w} bits`, () => circuit(g => { const a = g.input(w), b = g.input(w); return -g.eq(mul(g, a, b), mul(g, b, a)) })] as [string, () => {vars: number, cnf: Clause[]}]),
  ['PHP(7, 6)', () => php(7, 6)],
  ['PHP(8, 7)', () => php(8, 7)],
  ['PHP(9, 8)', () => php(9, 8)],
  ['PHP(10, 9)', () => php(10, 9)],
]

if (import.meta.main) {
  const limit = Number(process.argv[2] ?? 2_000_000)
  const only = process.argv[3]
  const checks = (process.env.CHECKS ?? (process.env.NO_DRUP ? 'lrat' : 'lrat,backward,forward')).split(',')
  const opts: Options = {limit, minimize: !process.env.NO_MINIMIZE, reduce: !process.env.NO_REDUCE, restarts: process.env.RESTARTS === 'luby' ? 'luby' : 'ema', drup: process.env.CHECKS === undefined || /backward|forward/.test(process.env.CHECKS),
    ...(process.env.TUNE ? JSON.parse(process.env.TUNE) : {})}
  const solve = process.env.SOLVER === 'v1' ? solveV1 : solveV2
  console.log('| problem | vars / clauses | solve | proof (lemmas, literals; LRAT after trimming) | DRUP forward | DRUP backward (lemmas checked) | LRAT |\n| --- | --- | --- | --- | --- | --- | --- |')
  for (const [name, make] of problems) {
    if (only && !new RegExp(only).test(name)) continue
    const {vars, cnf} = make()
    const t0 = performance.now()
    const r = solve(vars, cnf, opts)
    const solveMs = performance.now() - t0
    const row = (rest: string) => console.log(`| ${name} | ${vars} / ${cnf.length} | ${(solveMs / 1000).toFixed(2)} s | ${rest} |`)
    if (r.kind === 'unknown') { row(`gave up after ${r.conflicts} conflicts | | `); continue }
    if (r.kind === 'sat') { row(`a model, ${checkModel(cnf, r.model) ? 'checked' : 'REJECTED'} | | `); continue }
    const added = r.proof.filter(c => Array.isArray(c)), lits = added.reduce((s, c) => s + c.length, 0)
    const time = (mode: 'forward' | 'backward') => { const t = performance.now(), stats = {checked: 0}; const ok = checkProof(cnf, r.proof, mode, stats); return `${((performance.now() - t) / 1000).toFixed(2)} s ${ok ? 'ok' : 'REJECTED'}${mode === 'backward' ? ` (${stats.checked})` : ''}` }
    const skipForward = !checks.includes('forward') || (process.env.NO_FORWARD && added.length > 20000)
    const kept = r.lrat.filter(s => 'id' in s).length, hints = r.lrat.reduce((n, s) => n + ('hints' in s ? s.hints.length : 0), 0)
    const t1 = performance.now(), lrat = checks.includes('lrat') && checkLrat(vars, cnf, r.lrat)
    const lratCheck = checks.includes('lrat') ? `${((performance.now() - t1) / 1000).toFixed(2)} s ${lrat ? 'ok' : 'REJECTED'}` : 'skipped'
    row(`${added.length - 1}, ${lits}; LRAT keeps ${kept}, ${hints} hints${r.proof.length > added.length ? ` (${r.proof.length - added.length} deleted)` : ''} | ${skipForward ? 'skipped' : time('forward')} | ${checks.includes('backward') ? time('backward') : 'skipped'} | ${lratCheck}`)
  }
}
