// A step goal's variables, for a bit-sliced evaluation: `bun research/dag/vars.ts <goal.json>`. Classes: yes/no (a
// top-level hypothesis x <= 1), finite (a top-level x < n or x <= n with n <= 64: a clause index, a location), the
// halves of an integer (x and x$neg, a CHC integer as a difference of naturals) and the rest. Which of them the
// hypotheses read beside their own bound. Then, for 16 random assignments of every yes/no and finite variable (each
// value drawn within its bound), the kernel's reading there: the atoms still open and the variables they read, the
// rows and their variables, and the solver's verdict on the rows. Prints one JSON line.
import {readFileSync} from 'node:fs'
import type {C, E} from '../../core/machine.ts'
import {type Lin, solve} from '../../core/solver.ts'
import {type Path, canon, leafConstraints} from '../../kernel/kernel.ts'
import {loadGoal} from './goalio.ts'
import {openAtoms} from './tree.ts'

const goal = loadGoal(readFileSync(process.argv[2]!, 'utf8'))
const namesOf = (c: C): Set<string> => {
  const out = new Set<string>()
  const e = (x: E): void => { switch (x.op) { case 'var': out.add(x.name); return; case 'const': return; case 'mul': return e(x.a); case 'get': return e(x.key); case 'if': c1(x.c); e(x.then); return e(x.else); case 'add': case 'sub': case 'min': case 'max': case 'prod': e(x.a); return e(x.b) } }
  const c1 = (x: C): void => { switch (x.op) { case 'and': case 'or': return x.xs.forEach(c1); case 'not': return c1(x.x); case 'flag': case 'all': return; case '<': case '<=': case '=': e(x.a); return e(x.b) } }
  c1(c)
  return out
}
const tops = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(tops) : [c])
const all = new Set<string>(), max = new Map<string, number>()
for (const h of goal.hyps) for (const n of namesOf(h)) all.add(n)
for (const t of goal.hyps.flatMap(tops)) {
  if ((t.op === '<=' || t.op === '<') && t.a.op === 'var' && t.b.op === 'const') {
    const m = t.op === '<' ? t.b.value - 1 : t.b.value
    if (m <= 64) max.set(t.a.name, Math.min(max.get(t.a.name) ?? Infinity, m))
  }
}
const bounded = (t: C) => (t.op === '<=' || t.op === '<') && t.a.op === 'var' && t.b.op === 'const' && max.has(t.a.name)
const read = new Set<string>()
for (const t of goal.hyps.flatMap(tops)) if (!bounded(t)) for (const n of namesOf(t)) read.add(n)
const yesNo = [...all].filter(n => max.get(n) === 1), finite = [...all].filter(n => (max.get(n) ?? 0) > 1)
const halves = [...all].filter(n => !max.has(n) && (n.endsWith('$neg') || all.has(`${n}$neg`)))
const rest = [...all].filter(n => !max.has(n) && !halves.includes(n))
let seed = 4242
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2147483648; return Math.floor(seed / 2147483648 * k) }
const fixedVars = new Set([...yesNo, ...finite])
const samples = Array.from({length: 16}, () => {
  const path: Path = new Map()
  for (const n of [...fixedVars].sort()) {
    const value = rand(max.get(n)! + 1)
    // x = value as x <= value and x >= value (the second only when value > 0: x >= 0 is every natural's row)
    const le: Lin = value ? {[n]: 1, 1: -value} : {[n]: 1}
    path.set(canon(le), {lin: le, holds: true})
    if (value) { const ge: Lin = value === 1 ? {[n]: 1} : {[n]: 1, 1: -(value - 1)}; path.set(canon(ge), {lin: ge, holds: false}) }
  }
  const rows = leafConstraints(goal, path), open = openAtoms(goal, path)
  const openVars = new Set(open.flatMap(l => Object.keys(l)).filter(n => n !== '1' && !fixedVars.has(n)))
  const rowVars = new Set(rows.flatMap(r => Object.keys(r.lin)).filter(n => n !== '1' && !fixedVars.has(n)))
  return {open: open.length, openVars: openVars.size, rows: rows.length, rowVars: rowVars.size, verdict: solve(rows).kind}
})
const m = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)]
console.log(JSON.stringify({goal: goal.name, hyps: goal.hyps.length, vars: all.size, yesNo: yesNo.length, finite: finite.length, intHalves: halves.length, other: rest.length,
  yesNoRead: yesNo.filter(n => read.has(n)).length, finiteRead: finite.filter(n => read.has(n)).length, intHalvesRead: halves.filter(n => read.has(n)).length,
  fixed: {openMedian: m(samples.map(s => s.open)), openVarsMedian: m(samples.map(s => s.openVars)), rowsMedian: m(samples.map(s => s.rows)), rowVarsMedian: m(samples.map(s => s.rowVars)),
    verdicts: samples.reduce<Record<string, number>>((a, s) => ({...a, [s.verdict]: (a[s.verdict] ?? 0) + 1}), {}), noneOpen: samples.filter(s => s.open === 0).length}}))
