// Probes of two limits: k-step laws (the kernel takes up to 64: 32 steps prove in about 9 s and Lean checks them in
// about 13 minutes, 64 prove in about 90 s), and recurrences with many further arguments (each proven quickly on its own,
// but a rule reads the function at its arguments paired, which the kernel multiplies out: five further arguments is a
// polynomial of degree 32, past what it holds, so the limit stays four). `steps` and `args` print, for each size, the
// time to prove and the verdict; `lean <dir>` writes a Lean project of both (a rule reading a recurrence of ARGS further
// arguments, the budget's laws over KS steps) for lake build. Past a limit, lift it first.
//   bun research/perf/probe-limits.ts [steps|args]
//   ARGS=4 KS=16,24 bun research/perf/probe-limits.ts lean /tmp/lp && (cd /tmp/lp && lake build)
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type Term, min, nat, proveSteps, recur, rule, when} from '../../core/dsl.ts'
import {leanProject, toLean} from '../../lean-kernel/emit.ts'

const which = process.argv[2]
const time = <T>(f: () => T): [T, number] => { const t = performance.now(); const out = f(); return [out, Math.round(performance.now() - t)] }
const names = ['a', 'b', 'c', 'd', 'e', 'g', 'h', 'i']
// f(0, a..) = a, f(x + 1, a..) = f(x, a..) + the least further argument: at least a, and never shrinking.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Loose = any
const many = (n: number) => {
  const args = names.slice(0, n), least = (env: Record<string, Term>) => args.slice(1).reduce((acc, a) => min(acc, env[a]!), env['a']!)
  return (recur as Loose)(`many${n}`, {args, zero: (env: Record<string, Term>) => env['a'], next: (_: Term, f: Term, env: Record<string, Term>) => f.plus(least(env))},
    {'at least a': (_: Term, f: Term, env: Record<string, Term>) => f.atLeast(env['a']!)}, {'never shrinks': (_: Term, f: Term, __: Term, g: Term) => f.atMost(g)})
}
const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat, big: nat}).state({s: 0})
  .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
const within = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
const over = (k: number) => budget.stepsLaw(`${k} requests spend at most ${k}m`, k, ({s, m}, last) => last.s.atMost(s.plus(m.times(k))))

if (!which || which === 'steps') for (const k of [16, 24, 32, 48, 64]) {
  const [v, ms] = time(() => proveSteps(budget, [within], [over(k)]))
  console.log(`steps ${k}: proven ${v.proven} checked ${v.checked} ${ms} ms`)
}
if (!which || which === 'args') for (const n of [4, 5, 6, 8]) {
  const [v, ms] = time(() => { try { return many(n).verdict } catch (e) { return {error: String(e).slice(0, 200)} } })
  console.log(`args ${n}: ${JSON.stringify(v).slice(0, 300)} ${ms} ms`)
}
if (which === 'lean') {
  const n = Number(process.env.ARGS ?? 4), args = names.slice(0, n), ks = (process.env.KS ?? '16').split(',').map(Number)
  const reads: Loose = (rule('reads many') as Loose).params(Object.fromEntries(args.map(a => [a, nat]))).inputs({x: nat}).state({v: 0}).fns({many: many(n)})
    .step((env: Record<string, Loose>) => ({v: env['many'](env['x'], ...args.map(a => env[a]))}))
  const file = toLean([
    {id: 'many', machine: reads.machine, laws: [reads.law('v is 0 or at least a', (env: Record<string, Term>) => env['v']!.eq(0).or(env['v']!.atLeast(env['a']!)))]},
    {id: 'longer', machine: budget.machine, laws: [within], stepLaws: ks.map(over)},
  ], {title: 'past the limits'})
  const out = process.argv[3]!
  mkdirSync(out, {recursive: true})
  for (const [name, text] of Object.entries(leanProject(file))) writeFileSync(join(out, name), text)
  console.log(`${[...file.matchAll(/^theorem /gm)].length} theorems in ${out}`)
}
