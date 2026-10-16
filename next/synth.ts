// Guards from laws. A step acts only when its guard allows; the weakest guard that keeps a law is "acting can't break
// it, whatever the inputs the guard can't see". Fourier–Motzkin elimination is quantifier elimination for linear
// arithmetic, so the unsafe region, ∃ hidden. path ∧ ¬law(after), projects onto what the guard may read; its
// complement, within the law before the step, is the weakest guard. Every claim is then checked with the solver:
// the derived guard keeps the law, and anything weaker breaks it.
import {type Constraint, type Lin, add, eq, k, le, lt, nat, negate, show, solve, sub, v} from '../core/solver.ts'

const vars = (lin: Lin) => Object.keys(lin).filter(key => key !== '1')
const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b))

// Fourier–Motzkin projection: the constraints on `keep` that the system implies, with no other variable. Exact here,
// since every elimination below combines rows with a coefficient ±1 on the eliminated variable.
export function project(constraints: Constraint[], keep: string[]): Lin[] {
  let rows = constraints.map(c => c.lin)
  const others = [...new Set(rows.flatMap(vars))].filter(x => !keep.includes(x))
  for (const x of others) {
    const pos = rows.filter(r => (r[x] ?? 0) > 0), neg = rows.filter(r => (r[x] ?? 0) < 0)
    const next = rows.filter(r => (r[x] ?? 0) === 0)
    for (const p of pos) for (const n of neg) {
      const a = p[x]!, b = -n[x]!, g = gcd(a, b)
      const row = add(Object.fromEntries(Object.entries(p).map(([key, c]) => [key, (c * b) / g])), Object.fromEntries(Object.entries(n).map(([key, c]) => [key, (c * a) / g])))
      const h = vars(row).reduce((acc, key) => gcd(acc, row[key]!), 0)
      next.push(h > 1 ? {...Object.fromEntries(vars(row).map(key => [key, row[key]! / h])), 1: Math.ceil((row['1'] ?? 0) / h)} : row)
    }
    rows = next
  }
  return rows
}

// The rows of `rows` not implied by `given` (and by the others kept so far): a readable minimal form.
function minimize(rows: Lin[], given: Constraint[]): Lin[] {
  let kept = rows.filter(r => vars(r).length > 0 || (r['1'] ?? 0) > 0)
  for (const r of [...kept]) {
    const others = kept.filter(o => o !== r)
    const implied = solve([...given, ...others.map(lin => ({lin, label: ''})), negate({lin: r, label: ''})]).kind === 'refuted'
    if (implied) kept = others
  }
  return kept
}

export type Act = {name: string, path: Constraint[]}
export type Problem = {
  name: string
  reads: string[] // what the guard may read
  domain: Constraint[] // naturals, and facts true of every state and input
  before: Constraint[] // the law, before the step
  acts: Act[] // the ways acting can go, e.g. both sides of a min
  after: Constraint[] // the law, after the step (a conjunction)
}

// The unsafe region on the guard's reads, as a disjunction of conjunctions, each minimized under the law before.
export function unsafe(p: Problem): Lin[][] {
  const regions: Lin[][] = []
  for (const act of p.acts) for (const broken of p.after.map(negate)) {
    const system = [...p.domain, ...p.before, ...act.path, broken]
    if (solve(system).kind === 'refuted') continue
    const region = minimize(project(system, p.reads), [...p.domain, ...p.before].filter(c => vars(c.lin).every(x => p.reads.includes(x))))
    if (!regions.some(r => r.length === region.length && r.every((lin, i) => show(lin) === show(region[i]!)))) regions.push(region)
  }
  return regions
}

// Does `guard` keep the law? Every act from a state where the law and the guard hold ends where it holds.
export function keeps(p: Problem, guard: Constraint[]): boolean {
  return p.acts.every(act => p.after.every(a => solve([...p.domain, ...p.before, ...guard, ...act.path, negate(a)]).kind === 'refuted'))
}
// Is `weaker` allowed somewhere `guard` isn't, and is that somewhere unsafe? Then nothing weaker than guard is safe there.
export function implies(p: Problem, a: Constraint[], b: Constraint[]): boolean {
  return b.every(c => solve([...p.domain, ...p.before, ...a, negate(c)]).kind === 'refuted')
}

export const readable = (regions: Lin[][]) =>
  regions.map(r => r.map(lin => `${show(sub(lin, k(lin['1'] ?? 0)))} <= ${-(lin['1'] ?? 0)}`).join(' and ')).join('  or  ')

void eq, le, lt, nat, v
