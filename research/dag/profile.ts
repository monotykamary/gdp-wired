// The tree search on one dumped step goal, profiled: `bun research/dag/profile.ts <goal.json> [--ms 55000] [--out <dir>]`.
// tree.ts (kernel/prove.ts's search, copied, with a recorder) grows the goal under its own budget (a second a
// hypothesis, at least 20 s) within --ms, as given.ts's proveRule did. Then, outside that time, each leaf it found:
//   - its derivation checked again over leafConstraints at its path (kernel.ts, fresh);
//   - its core (cores.ts: the decisions the rows it reads depend on), replayed at the core alone;
//   - whether it repeats an earlier leaf: the same rows (as linear forms), the same core, or a path that already holds
//     an earlier leaf's verified core (a learned clause would have closed it with no solve).
// And the goal's variables: yes/no ones (a hypothesis `x <= 1` at the top) against the rest, how many yes/no ones a
// hypothesis reads beside its bound, and what is left open once every yes/no one is fixed (8 random assignments: the
// atoms still open, the rows, the variables the rows read that aren't yes/no, the solver's verdict there).
// Prints one JSON line (and writes it to <dir>/profile.json).
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import type {C, E} from '../../core/machine.ts'
import {checkRefutation} from '../../core/check.ts'
import {type Lin, solve} from '../../core/solver.ts'
import {type Path, canon, leafConstraints, withProducts} from '../../kernel/kernel.ts'
import {loadGoal} from './goalio.ts'
import {coreOf, replay, sub, usedRows} from './cores.ts'
import {countLeavesOf, grow, openAtoms, profile, rec, withDeadline} from './tree.ts'

const file = process.argv[2]!
const arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('--ms') ?? 55000), outDir = arg('--out')
const goal = loadGoal(readFileSync(file, 'utf8'))

// --- the search ---
profile.on = true; rec.on = true; rec.t0 = performance.now()
const t0 = performance.now()
const out = withDeadline(performance.now() + ms, () => grow(goal))
const searchMs = performance.now() - t0
rec.on = false

// --- the leaves ---
const t1 = performance.now()
const leaves = rec.leaves
let checked = 0, coreReplayed = 0, sameRows = 0, sameCore = 0, subsumed = 0
const depth: number[] = [], coreSize: number[] = []
const rowsSeen = new Set<string>(), coresSeen = new Set<string>()
// Verified cores so far, indexed by their first literal (a path holds a core when it holds each of its literals).
const byFirst = new Map<string, string[][]>()
const postBudget = performance.now() + 240_000
let processed = 0
for (const l of leaves) {
  if (performance.now() > postBudget) break
  processed++
  const path: Path = new Map(l.path.map(([key, lin, holds]) => [key, {lin, holds}]))
  const lits = new Set(l.path.map(([key, , holds]) => `${key}=${holds ? 1 : 0}`))
  depth.push(path.size)
  // Would an earlier core have closed this case (every literal of it on this path)?
  let hit = false
  for (const x of ['', ...lits]) { for (const c of byFirst.get(x) ?? []) if (c.every(y => lits.has(y))) { hit = true; break } if (hit) break }
  if (hit) subsumed++
  const rows = leafConstraints(goal, path)
  if (checkRefutation(withProducts(rows, l.products ?? [], l.squares), l.steps)) checked++
  const used = usedRows(rows.length, l.steps, l.products, l.squares)
  const rowKey = [...used].map(i => canon(rows[i]!.lin)).sort().join('|')
  if (rowsSeen.has(rowKey)) sameRows++; else rowsSeen.add(rowKey)
  const core = coreOf(goal, path, rows, used)
  const replayed = replay(goal, rows, sub(path, core), l.steps, l.products, l.squares)
  const coreLits = [...core].map(key => `${key}=${path.get(key)!.holds ? 1 : 0}`).sort()
  coreSize.push(core.size)
  if (replayed) {
    coreReplayed++
    const ck = coreLits.join('|')
    if (coresSeen.has(ck)) sameCore++; else { coresSeen.add(ck); if (coreLits.length) { const f = coreLits[0]!; byFirst.set(f, [...(byFirst.get(f) ?? []), coreLits]) } else byFirst.set('', [[]]) }
  }
}
const postMs = performance.now() - t1

// --- the variables ---
const names = new Set<string>()
const walkE = (e: E): void => { switch (e.op) { case 'var': names.add(e.name); return; case 'const': return; case 'mul': return walkE(e.a); case 'get': return walkE(e.key); case 'if': walkC(e.c); walkE(e.then); return walkE(e.else); case 'add': case 'sub': case 'min': case 'max': case 'prod': walkE(e.a); return walkE(e.b) } }
const walkC = (c: C): void => { switch (c.op) { case 'and': case 'or': return c.xs.forEach(walkC); case 'not': return walkC(c.x); case 'flag': case 'all': return; case '<': case '<=': case '=': walkE(c.a); return walkE(c.b) } }
goal.hyps.forEach(walkC)
const tops = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(tops) : [c])
const bound = (c: C): string | undefined => (c.op === '<=' && c.a.op === 'var' && c.b.op === 'const' && c.b.value <= 1 ? c.a.name : undefined)
const bools = new Set(goal.hyps.flatMap(tops).map(bound).filter((x): x is string => !!x))
const readers = new Set<string>()
for (const h of goal.hyps) for (const t of tops(h)) {
  if (bound(t)) continue
  const before = new Set(names); names.clear(); walkC(t)
  for (const n of names) if (bools.has(n)) readers.add(n)
  for (const n of before) names.add(n)
}
goal.hyps.forEach(walkC)
let seed = 12345
const rand = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648)
const fixed = Array.from({length: 8}, () => {
  const path: Path = new Map()
  for (const b of [...bools].sort()) { const lin: Lin = {[b]: 1}; path.set(canon(lin), {lin, holds: rand() < 0.5}) }
  const t = performance.now(), rows = leafConstraints(goal, path), open = openAtoms(goal, path)
  const vars = new Set(rows.flatMap(r => Object.keys(r.lin)).filter(n => n !== '1' && !bools.has(n)))
  const v = solve(rows)
  return {open: open.length, openNumeric: open.filter(lin => Object.keys(lin).some(n => n !== '1' && !bools.has(n))).length, rows: rows.length, numericVars: vars.size, verdict: v.kind, ms: Math.round(performance.now() - t)}
})

const q = (xs: number[], p: number) => { if (!xs.length) return undefined; const s = [...xs].sort((a, b) => a - b); return s[Math.min(s.length - 1, Math.floor(p * s.length))] }
const result = {
  goal: goal.name, hyps: goal.hyps.length,
  outcome: 'tree' in out ? 'proven' : out.stuck, why: 'tree' in out ? undefined : out.why?.slice(0, 90),
  treeLeaves: 'tree' in out ? countLeavesOf(out.tree) : undefined,
  searchMs: Math.round(searchMs), phases: Object.fromEntries(Object.entries(rec.phases).map(([key, x]) => [key, Math.round(x)])),
  nodes: profile.nodes, solves: profile.solves, solveMs: Math.round(profile.solveMs), rowsMs: Math.round(profile.rowsMs),
  leavesFound: leaves.length, leavesProcessed: processed, leafChecked: checked, coreReplayed,
  sameRows, sameCore, subsumedByEarlierCore: subsumed,
  depth: {median: q(depth, 0.5), p90: q(depth, 0.9), max: depth.length ? Math.max(...depth) : undefined},
  coreSize: {median: q(coreSize, 0.5), p90: q(coreSize, 0.9), max: coreSize.length ? Math.max(...coreSize) : undefined},
  vars: {all: names.size, yesNo: bools.size, numeric: names.size - bools.size, yesNoRead: readers.size},
  fixedYesNo: fixed, postMs: Math.round(postMs),
}
console.log(JSON.stringify(result))
if (outDir) { mkdirSync(outDir, {recursive: true}); writeFileSync(`${outDir}/profile.json`, JSON.stringify(result)) }
process.exit(0)
