// Not a solver: whether interpolants of bounded refutations find the directions of Spacer's invariant atoms,
// `bun compare/chc/prof/itpdirs.ts <task.smt2> <models.json> [--ms 30000]` (`--tools itpdirs`). For depth k = 2, 3, ...
// and each cut j < k, the interpolant of the first j steps from the start against the rest and the law broken
// (core/interp.ts, the stuttering machine, relaxed goals); each comparison it reads as a direction over the Int
// arguments (an integer's two naturals with opposite coefficients, divided by their divisor, the first positive).
// Beside them, the directions of Spacer's invariant (its define-funs' comparisons, linear over the Int arguments).
// Prints one JSON line: both sets' sizes, those shared, and Spacer's beyond the join's templates (more than three
// values, or a coefficient past 3) and how many of those the interpolants have.
import {readFileSync} from 'node:fs'
import {parseChc, parseSx, type Sx} from '../chc.ts'
import {build} from '../translate.ts'
import type {C, E} from '../../../core/machine.ts'
import {byStep, interpolate, stutter} from '../../../core/interp.ts'
import {relax} from '../../../core/bmc.ts'
import {stepLawObligations, substC} from '../../../kernel/kernel.ts'
import {counted} from '../../../kernel/prove.ts'
import {gcd, linOfE, plus} from '../../../core/solver.ts'

const args = process.argv.slice(2), [file, modelsFile] = args as [string, string]
const ms = Number(args[args.indexOf('--ms') + 1] ?? 30_000) || 30_000, t0 = performance.now(), wall = t0 + ms
const say = (o: object) => { console.log(JSON.stringify({task: file, ms: Math.round(performance.now() - t0), stage: 'answer', answer: 'itpdirs', ...o})); process.exit(0) }
const models = JSON.parse(readFileSync(modelsFile, 'utf8')) as Record<string, string>
const text = models[file.replace(/^\/bench\//, '')]
if (!text) say({why: 'no model'})
const chc = parseChc(readFileSync(file, 'utf8')), b = build(chc), m = b.rule.machine
const key = (d: Map<number, number>): string | undefined => {
  const es = [...d.entries()].filter(([, c]) => c !== 0).sort((p, q) => p[0] - q[0])
  if (!es.length) return undefined
  const g = es.reduce((a, [, c]) => gcd(a, c), 0), s = es[0]![1] < 0 ? -1 : 1
  return JSON.stringify(es.map(([i, c]) => [i, (s * c) / g]))
}
// Spacer's: each define-fun's comparisons over its Int parameters (slot k: the k-th Int).
const spacer = new Set<string>()
for (const d of parseSx(text!).flat().filter((x): x is Sx[] => Array.isArray(x) && x[0] === 'define-fun')) {
  const params = d[2] as Sx[][], slot = new Map<string, number>()
  let n = 0
  for (const [p, sort] of params as [string, string][]) if (sort === 'Int') slot.set(p, n++)
  const lin = (s: Sx, f: number, out: Map<number, number>): boolean => {
    if (typeof s === 'string') { if (/^\d+$/.test(s)) return true; const i = slot.get(s); if (i === undefined) return false; out.set(i, (out.get(i) ?? 0) + f); return true }
    if (s[0] === '+') return s.slice(1).every(x => lin(x, f, out))
    if (s[0] === '-') return s.length === 2 ? lin(s[1]!, -f, out) : lin(s[1]!, f, out) && s.slice(2).every(x => lin(x, -f, out))
    if (s[0] === '*') { const ks = s.slice(1).map(x => (typeof x === 'string' && /^\d+$/.test(x) ? Number(x) : Array.isArray(x) && x[0] === '-' && typeof x[1] === 'string' && /^\d+$/.test(x[1]) ? -Number(x[1]) : undefined)); const rest = s.slice(1).filter((_, j) => ks[j] === undefined); return rest.length <= 1 && (rest.length === 0 || lin(rest[0]!, f * ks.reduce<number>((a, c) => a * (c ?? 1), 1), out)) }
    return false
  }
  const walk = (s: Sx): void => {
    if (!Array.isArray(s)) return
    if (['<=', '>=', '<', '>', '='].includes(s[0] as string) && s.length === 3) { const d = new Map<number, number>(); if (lin(s[1]!, 1, d) && lin(s[2]!, -1, d)) { const k = key(d); if (k) spacer.add(k) } }
    s.forEach(walk)
  }
  walk(d[4]!)
}
// Ours: the interpolants' comparisons.
const ours = new Set<string>()
const names = Object.keys(m.state), m2 = stutter(m, b.law)
const then = substC(b.law.holds, {vars: Object.fromEntries(names.map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: {}, flags: {}})
const start: C = {op: 'and', xs: Object.entries(m.state).map(([n, e]): C => ({op: '=', a: {op: 'var', name: n}, b: e}))}
const collect = (c: C, j: number): void => {
  if (c.op === 'and' || c.op === 'or') { c.xs.forEach(x => collect(x, j)); return }
  if (c.op === 'not') { collect(c.x, j); return }
  if (c.op !== '<=' && c.op !== '<' && c.op !== '=') return
  const la = linOfE(c.a), lb = linOfE(c.b)
  if (!la || !lb) return
  const l = new Map(Object.entries(plus(la, lb, -1)).filter(([n]) => n !== '1'))
  const d = new Map<number, number>()
  for (const [n, c0] of l) {
    const r = new RegExp(`^i(\\d+)(\\$neg)?~${j}$`).exec(n)
    if (!r) return
    const i = Number(r[1]), neg = !!r[2], cur = d.get(i)
    const want = neg ? -c0 : c0
    if (cur !== undefined && cur !== want) return
    if (cur === undefined && !neg && l.has(`i${i}$neg~${j}`) && l.get(`i${i}$neg~${j}`) !== -c0) return
    if (cur === undefined && neg && l.get(`i${i}~${j}`) !== -c0 && l.has(`i${i}~${j}`)) return
    d.set(i, want)
  }
  const k = key(d)
  if (k) ours.add(k)
}
let depth = 0, cuts = 0, fails = 0
counted(250, () => {
  for (let k = 2; k <= 12 && performance.now() < wall; k++) {
    const g = stepLawObligations(m2, [], {}, {name: 'itp', when: start, then, steps: k})[0]!
    const hyps = relax(g.hyps) ?? g.hyps, st = byStep(m2, hyps)
    for (let j = 1; j < k && performance.now() < wall; j++) {
      const out = interpolate(hyps.filter((_, i) => st[i]! <= j), hyps.filter((_, i) => st[i]! > j), names.map(n => `${n}~${j}`), {until: Infinity, wall})
      if ('sat' in out) { k = 99; break }
      if ('unknown' in out) { fails++; continue }
      cuts++; collect(out.itp, j)
    }
    depth = k
  }
}, true)
const beyond = [...spacer].filter(s => { const es = JSON.parse(s) as [number, number][]; return es.length > 3 || es.some(([, c]) => Math.abs(c) > 3) })
say({depth, cuts, fails, spacer: spacer.size, ours: ours.size, shared: [...spacer].filter(s => ours.has(s)).length, beyond: beyond.length, beyondOurs: beyond.filter(s => ours.has(s)).length})
