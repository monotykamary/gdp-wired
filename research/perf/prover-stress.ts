// Where the prover falls over: families of rules, each growing one dimension (cases of a variant, flags, quantified
// conditions on a request, steps in a k-step law, reads of a function with lemmas, a priority chain), each proven at n
// = 1, 2, 4, 8... until a goal goes unknown or a proof passes the limit. What a real rule hits first.
//   bun research/perf/prover-stress.ts [--family name] [--limit ms] [--n size]
import {type Law} from '../../core/machine.ts'
import {type StepLaw, everyKey, min, nat, oneOf, proveSteps, recur, rule, upTo, variant, when} from '../../core/dsl.ts'
import {profile} from '../../kernel/prove.ts'

const range = (n: number) => Array.from({length: n}, (_, i) => i)
type Built = {rule: Parameters<typeof proveSteps>[0], laws: Law[], steps: StepLaw[]}
const families: Record<string, (n: number) => Built> = {
  // A state that is one of n cases, each with an amount; a request moves it to case op, its amount capped.
  cases: n => {
    const St = variant(Object.fromEntries(range(n).map(i => [`s${i}`, {amount: nat}])) as Record<string, {amount: typeof nat}>)
    const r = rule(`cases ${n}`).params({cap: nat}).inputs({op: upTo(n - 1), x: nat}).state({at: St.from({tag: 's0', amount: 0})})
      .step(({op, x, cap, at}) => {
        const amount = at.match(Object.fromEntries(range(n).map(i => [`s${i}`, (c: {amount: import('../../core/dsl.ts').Term}) => c.amount])) as never) as unknown as import('../../core/dsl.ts').Term
        return {at: range(n).reduceRight((acc, i) => when(op.eq(i), St.make({tag: `s${i}`, amount: min(amount.plus(x), cap)} as never), acc), at)}
      })
    return {rule: r as never, laws: [r.law('every amount is within the cap', ({at, cap}) => at.match(Object.fromEntries(range(n).map(i => [`s${i}`, (c: {amount: import('../../core/dsl.ts').Term}) => c.amount.atMost(cap)])) as never))], steps: []}
  },
  // n counters, each granted by its own flag; a law per counter.
  flags: n => {
    let r = rule(`flags ${n}`).params({cap: nat}).inputs({who: upTo(n - 1), ok: oneOf('no', 'yes')}).state(Object.fromEntries(range(n).map(i => [`c${i}`, 0])) as Record<string, number>)
    r = r.flags(env => Object.fromEntries(range(n).map(i => [`g${i}`, (env as never as Record<string, import('../../core/dsl.ts').Term>).who!.eq(i).and((env as never as {ok: import('../../core/dsl.ts').Choice<'no' | 'yes'>}).ok.is('yes'), (env as never as Record<string, import('../../core/dsl.ts').Term>)[`c${i}`]!.lt((env as never as Record<string, import('../../core/dsl.ts').Term>).cap!))])) as never) as never
    r = r.step(env => Object.fromEntries(range(n).map(i => [`c${i}`, when((env as never as Record<string, import('../../core/dsl.ts').Cond>)[`g${i}`]!, (env as never as Record<string, import('../../core/dsl.ts').Term>)[`c${i}`]!.plus(1), (env as never as Record<string, import('../../core/dsl.ts').Term>)[`c${i}`]!)])) as never) as never
    return {rule: r as never, laws: range(n).map(i => r.law(`counter ${i} within the cap`, env => (env as never as Record<string, import('../../core/dsl.ts').Term>)[`c${i}`]!.atMost((env as never as Record<string, import('../../core/dsl.ts').Term>).cap!))), steps: []}
  },
  // A request carrying n sets, each assumed to be 0/1 at every key (separate quantified conditions); a count capped.
  quantifiers: n => {
    let r = rule(`quantifiers ${n}`).params({cap: nat}).inputs({x: nat}).state({count: 0}).carries(...range(n).map(i => `S${i}`)) as never as ReturnType<typeof rule>
    for (const i of range(n)) r = r.assume(env => everyKey(k => ((env as never as Record<string, import('../../core/dsl.ts').MapRef>)[`S${i}`]!).at(k).atMost(1))) as never
    r = r.step(env => {
      const e = env as never as Record<string, import('../../core/dsl.ts').Term> & Record<string, import('../../core/dsl.ts').MapRef>
      const hit = range(n).reduce((acc, i) => acc.or((e[`S${i}`] as import('../../core/dsl.ts').MapRef).has(e.x as never)), (e.x as import('../../core/dsl.ts').Term).lt(0))
      return {count: when(hit.and((e.count as import('../../core/dsl.ts').Term).lt(e.cap as import('../../core/dsl.ts').Term)), (e.count as import('../../core/dsl.ts').Term).plus(1), e.count as import('../../core/dsl.ts').Term)}
    }) as never
    return {rule: r as never, laws: [r.law('the count is within the cap', env => (env as never as Record<string, import('../../core/dsl.ts').Term>).count!.atMost((env as never as Record<string, import('../../core/dsl.ts').Term>).cap!))], steps: []}
  },
  // A k-step law on a capped meter: k requests add at most k·m.
  steps: n => {
    const r = rule(`steps ${n}`).params({b: nat, m: nat}).inputs({c: nat}).state({s: 0}).step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
    const k = Math.min(16, n + 1)
    return {rule: r as never, laws: [], steps: [r.stepsLaw(`${k} requests add at most ${k}·m`, k, ({s, m}, after) => after.s.atMost(s.plus(m.times(k))))]}
  },
  // A function with lemmas and a law between two points, read at n keys; a law that needs only one of them.
  facts: n => {
    const g = recur('grow', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {'at least 1': (_, d) => d.atLeast(1), 'at most 64': (_, d) => d.atMost(64)}, {'never shrinks': (_, d, __, e) => d.atMost(e)})
    const r = rule(`facts ${n}`).inputs({up: oneOf('stay', 'up')}).state({level: 0, sum: 0}).fns({g})
      .step(({up, level, sum, g}) => ({level: when(up.is('up'), level.plus(1), level), sum: range(n).reduce((acc, i) => acc.plus(g(level.plus(i))), sum.times(0))}))
    return {rule: r as never, laws: [r.law(`the sum of ${n} delays is at most ${64 * n}`, ({sum}) => sum.atMost(64 * n))], steps: []}
  },
  // A price by n tiers, a priority chain of thresholds; the price within the top rate.
  chains: n => {
    const r = rule(`chains ${n}`).params({top: nat}).inputs({q: nat}).state({price: 0})
      .step(({q, top}) => ({price: range(n).reduceRight((acc, i) => when(q.lt((i + 1) * 10), min(q.times(n - i), top), acc), min(q, top) as import('../../core/dsl.ts').Term)}))
    return {rule: r as never, laws: [r.law('the price is within the top', ({price, top}) => price.atMost(top))], steps: []}
  },
}
const arg = (k: string) => (process.argv.includes(k) ? process.argv[process.argv.indexOf(k) + 1] : undefined)
const limit = Number(arg('--limit') ?? 30_000), pick = arg('--family')?.split(',')
profile.on = true
for (const [name, make] of Object.entries(families)) {
  if (pick && !pick.includes(name)) continue
  const single = arg('--n')
  for (let n = single ? Number(single) : 1; n <= (single ? Number(single) : 64); n *= 2) {
    const b = make(n), g0 = profile.goals.length, t = performance.now()
    const v = proveSteps(b.rule, b.laws, b.steps), ms = performance.now() - t
    const gs = profile.goals.slice(g0), worst = gs.sort((a, c) => c.ms - a.ms)[0]
    console.log(`${name.padEnd(12)} n=${String(n).padStart(2)}  ${ms.toFixed(0).padStart(7)} ms  ${v.proven ? 'proven ' : `UNPROVEN (${v.stuck})`}  worst ${worst ? `${worst.ms.toFixed(0)} ms ${worst.nodes} nodes ${worst.solves} solves (solver ${worst.solveMs.toFixed(0)}, rows ${worst.rowsMs.toFixed(0)}): ${worst.name}` : '-'}`)
    if (!v.proven || ms > limit) break
  }
}
