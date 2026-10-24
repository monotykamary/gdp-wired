// "From leads to to" with no rank stated, where the rank fitted to the runs (core/cycles.ts's findLeadsTo) is not the
// one: a rank made of the rule's own terms, chosen by the steps it must lower. Its components are drawn from
// - the control: a variable its kind bounds (a chart's state, a status, a flag), ranked by the steps between its
//   values (each strongly connected set of values one level, the levels in the order the steps go);
// - the distances the rule compares: for each comparison a < b or a <= b of its guards, its steps, the law and the
//   helpful requests (the request's own inputs replaced by what it sends), over the state, the params and the cells
//   they read, the distance until it changes (b ∸ a, a + 1 ∸ b and the like): a counter up to a limit, a clock up to a
//   deadline, a timestamp's distance from the time;
// - a state variable alone, and the constant 0.
// The steps are taken from runs from the start and from random states the laws allow, where `from` holds and `to`
// doesn't (the kernel's goals are about every such state, reached or not): a helpful request's in its region must
// lower the rank, and so must any other that leaves a region it was in; the rest must not raise it. Components are
// chosen in order, each one no step raises that lowers the most of those left. The rank is then the kernel's
// (proveLiveness), with the invariants inferLaws finds where its goals need some. Nothing new is trusted.
import {type C, type E, type Law, type Machine, type Rand, type Request, type State, evalC, evalE, interpret, seeded, walk} from './machine.ts'
import {type Liveness, livenessHelpful, livenessParts, substE} from '../kernel/kernel.ts'
import {clock, proveLiveness, withDeadline} from '../kernel/prove.ts'
import {allowed, watch} from './watch.ts'
import {type LeadsVerdict, showE} from './cycles.ts'
import {inferLaws} from './infer.ts'

type Env = Record<string, number>
// `rule`: the rule the machine is, for inferLaws (which draws its runs and states by the rule's kinds).
export type Draws = {params: (rand: Rand, bound: number) => Env, input: (rand: Rand, bound: number, ps: Env) => Request, state?: (rand: Rand, bound: number) => Env, rule?: Parameters<typeof inferLaws>[0]}
type Step = {ps: Env, s: State, t: State, lower: boolean}
const id = (t: unknown) => JSON.stringify(t)
const k = (value: number): E => ({op: 'const', value}), v = (name: string): E => ({op: 'var', name})
const sub = (a: E, b: E): E => ({op: 'sub', a, b}), plus1 = (a: E): E => ({op: 'add', a, b: k(1)})

// The comparisons a condition or term makes, each side a term.
function comparisons(t: unknown): [E, E][] {
  const out: [E, E][] = []
  walk(t, o => { if ((o.op === '<' || o.op === '<=' || o.op === '=') && typeof o.a === 'object' && typeof o.b === 'object') out.push([o.a as E, o.b as E]) })
  // (a side that decides a flag or a quantifier is no term of the state)
  return out.filter(p => { let plain = true; walk(p, o => { if (o.op === 'flag' || o.op === 'all') plain = false }); return plain })
}
const reads = (e: E, names: string[]): boolean => { let hit = false; walk(e, o => { if (o.op === 'var' && names.includes(o.name as string)) hit = true }); return hit }
const constant = (e: E): boolean => { let c = true; walk(e, o => { if (o.op === 'var' || o.op === 'get') c = false }); return c }

// The candidate components that don't depend on the steps: the distances, each variable alone.
function distances(m: Machine, l: Liveness): E[] {
  const helpful = livenessHelpful(l), atoms: [E, E][] = [...comparisons([m.step, m.assume, l.from, l.to, helpful.map(h => h.when)])]
  // a guard as the helpful request meets it: its inputs replaced by the terms it sends
  for (const h of helpful) {
    const s = {vars: h.request, maps: {}, flags: {}}
    for (const [a, b] of comparisons([m.step, m.assume])) atoms.push([substE(a, s), substE(b, s)])
  }
  const out = new Map<string, E>()
  const add = (e: E) => { if (!constant(e) && !reads(e, m.inputs)) out.set(id(e), e) }
  for (const [a, b] of atoms) {
    if (reads(a, m.inputs) || reads(b, m.inputs) || constant(a) && constant(b)) continue
    for (const e of [sub(b, a), sub(a, b), sub(plus1(a), b), sub(plus1(b), a)]) add(e)
  }
  for (const x of Object.keys(m.state)) add(v(x))
  return [...out.values()]
}

// A variable's values ranked by the steps between them: each strongly connected set one level, a level above every one
// a step goes to from it (Tarjan's components, then the longest path down).
function controlRank(x: string, steps: Step[]): E | undefined {
  const graph = new Map<number, Set<number>>()
  const node = (a: number) => graph.get(a) ?? (graph.set(a, new Set()), graph.get(a)!)
  for (const st of steps) { const a = st.s.scalars[x]!, b = st.t.scalars[x]!; node(b); if (a !== b) node(a).add(b) }
  if (graph.size < 2) return undefined
  const index = new Map<number, number>(), low = new Map<number, number>(), comp = new Map<number, number>(), stack: number[] = []
  let n = 0, c = 0
  const visit = (a: number): void => {
    index.set(a, n); low.set(a, n++); stack.push(a)
    for (const b of graph.get(a)!) {
      if (!index.has(b)) { visit(b); low.set(a, Math.min(low.get(a)!, low.get(b)!)) } else if (!comp.has(b)) low.set(a, Math.min(low.get(a)!, index.get(b)!))
    }
    if (low.get(a) === index.get(a)) { let b: number; do { b = stack.pop()!; comp.set(b, c) } while (b !== a); c++ }
  }
  for (const a of graph.keys()) if (!index.has(a)) visit(a)
  const level = new Map<number, number>()
  // (Tarjan numbers a component after every one it reaches: so in that order each level is known before it is needed)
  const members = Array.from({length: c}, (_, i) => [...graph.keys()].filter(a => comp.get(a) === i))
  for (const ms of members) {
    let lv = 0
    for (const a of ms) for (const b of graph.get(a)!) if (comp.get(b) !== comp.get(a)) lv = Math.max(lv, level.get(comp.get(b)!)! + 1)
    level.set(comp.get(ms[0]!)!, lv)
  }
  const values = [...graph.keys()].sort((p, q) => p - q).map(a => [a, level.get(comp.get(a)!)!] as const)
  if (values.every(([, lv]) => lv === 0)) return undefined
  return values.slice(0, -1).reduceRight<E>((rest, [a, lv]) => ({op: 'if', c: {op: '=', a: v(x), b: k(a)}, then: k(lv), else: rest}), k(values.at(-1)![1]))
}

// The variables a kind law bounds by a small constant (x < c, x <= c).
const bounded = (m: Machine, laws: Law[]): string[] => {
  const out = new Set<string>()
  for (const law of laws) if (!law.forall) walk(law.holds, o => {
    const a = o.a as E | undefined, b = o.b as E | undefined
    if ((o.op === '<' || o.op === '<=') && a?.op === 'var' && a.name in m.state && b?.op === 'const' && b.value <= 32) out.add(a.name)
  })
  return [...out]
}

export function leadsByTerms(m: Machine, laws: Law[], l: Liveness, draws: Draws, opts: {ms?: number} = {}): LeadsVerdict {
  const t0 = clock(), until = t0 + (opts.ms ?? 10_000), rand = seeded(31), run = interpret(m), helpful = livenessHelpful(l)
  const env = (ps: Env, st: State): Env => ({...ps, ...st.scalars})
  const holds = (c: C, ps: Env, st: State) => { try { return evalC(c, env(ps, st), st, m) } catch { return undefined } }
  const pending = (ps: Env, st: State) => holds(l.from, ps, st) === true && holds(l.to, ps, st) === false
  const regions = (ps: Env, st: State) => helpful.map(h => holds(h.when, ps, st) === true)
  const steps: Step[] = []
  // One step from a pending state: a helpful request in its region (its named inputs at the state, the rest drawn), or
  // any request; kept where it stays pending.
  const take = (ps: Env, st: State, bound: number, h?: number): State | undefined => {
    for (let tries = 0; tries < 20; tries++) {
      try {
        const input = draws.input(rand, bound, ps)
        if (h !== undefined) for (const [x, t] of Object.entries(helpful[h]!.request)) input[x] = evalE(t, env(ps, st), st, m)
        if (!allowed(m, run, ps, st, input)) continue
        const next = run.step(ps, st, input)
        if (pending(ps, st) && pending(ps, next)) {
          const was = regions(ps, st), now = regions(ps, next)
          steps.push({ps, s: st, t: next, lower: h !== undefined || was.some((r, i) => r && !now[i])})
        }
        return next
      } catch { /* refused: another */ }
    }
    return undefined
  }
  const pick = (ps: Env, st: State): number | undefined => { const rs = regions(ps, st).flatMap((r, i) => (r ? [i] : [])); return rs.length && rand(2) ? rs[rand(rs.length)] : undefined }
  const sampleUntil = t0 + Math.min(1500, (until - t0) / 8)
  // runs from the start
  for (const bound of [2, 4, 8]) for (let trial = 0; trial < 20 && clock() < sampleUntil; trial++) {
    let ps: Env, st: State | undefined
    try { ps = draws.params(rand, bound); if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) continue; st = run.init(ps) } catch { continue }
    for (let turn = 0; turn < 80 && st; turn++) st = pending(ps, st) ? take(ps, st, bound, pick(ps, st)) : take(ps, st, bound)
  }
  // random states the laws allow
  if (!m.history) for (let trial = 0, found = 0; trial < 4000 && found < 300 && clock() < sampleUntil; trial++) {
    const bound = 4
    let ps: Env
    try { ps = draws.params(rand, bound); if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) continue } catch { continue }
    const scalars: Env = {...Object.fromEntries(Object.keys(m.state).map(n => [n, rand(8)])), ...(draws.state?.(rand, bound) ?? {})}
    const st: State = {scalars, maps: Object.fromEntries(Object.keys(m.maps ?? {}).map(n => [n, new Map(Array.from({length: rand(3)}, () => [rand(bound + 1), rand(bound + 1)] as const))]))}
    try { if (!pending(ps, st) || !laws.every(law => watch(m, run, law, ps, bound).start(st))) continue } catch { continue }
    found++
    take(ps, st, bound, pick(ps, st))
  }
  // A goal's counterexample as a step (the kernel names a cell by its map and its key's linear form, `M[d:1,1:2]`): the
  // state, params and request it gives (0 where it gives none), stepped by the interpreter. The step a goal fails at
  // is one the rank must allow; so the ranks are chosen again with it, a few rounds.
  const fromWitness = (w: Record<string, number>, goal: string): boolean => {
    const ps = Object.fromEntries(m.params.map(p => [p, w[p] ?? 0])), maps: State['maps'] = Object.fromEntries(Object.keys(m.maps ?? {}).map(n => [n, new Map()]))
    for (const [name, x] of Object.entries(w)) {
      const at = name.indexOf('[')
      if (at < 0 || !name.endsWith(']') || !maps[name.slice(0, at)]) continue
      let key = 0
      for (const part of name.slice(at + 1, -1).split(',')) { const c = part.lastIndexOf(':'), n = part.slice(0, c); key += Number(part.slice(c + 1)) * (n === '1' ? 1 : w[n] ?? 0) }
      if (Number.isInteger(key) && key >= 0) maps[name.slice(0, at)]!.set(key, x)
    }
    const st: State = {scalars: Object.fromEntries(Object.keys(m.state).map(x => [x, w[x] ?? 0])), maps}
    const input: Request = Object.fromEntries(m.inputs.map(i => [i, w[i] ?? 0]))
    try {
      if (!pending(ps, st) || !allowed(m, run, ps, st, input)) return false
      const next = run.step(ps, st, input)
      if (!pending(ps, next)) return false
      const was = regions(ps, st), now = regions(ps, next), h = /helpful request (\d+)/.exec(goal)
      steps.push({ps, s: st, t: next, lower: !!h || was.some((r, i) => r && !now[i])})
      return true
    } catch { return false }
  }
  if (!steps.length) return {proven: false, checked: false, why: 'no step sampled from a state where it is pending'}
  // The components, then the ranks: each component the one no step raises that lowers the most steps left to lower.
  const value = (e: E, ps: Env, st: State) => { try { return evalE(e, env(ps, st), st, m) } catch { return NaN } }
  const fixed = distances(m, l), text = (rank: E[]) => `(${rank.map(showE).join(', ')})`, tried = new Set<string>()
  let last: ReturnType<typeof proveLiveness> | undefined, best: E[] | undefined
  for (let round = 0; round < 6 && until - clock() > 200; round++) {
    const cands = [...bounded(m, laws).map(x => controlRank(x, steps)).filter((e): e is E => !!e), ...fixed]
    const vals = cands.map(e => steps.map(st => [value(e, st.ps, st.s), value(e, st.ps, st.t)] as const))
    const build = (banned: Set<number>): E[] | undefined => {
      let left = steps.map((_, i) => i)
      const rank: number[] = []
      for (let turn = 0; turn < 3 && left.some(i => steps[i]!.lower); turn++) {
        let pick = -1, most = 0
        for (let c = 0; c < cands.length; c++) {
          if (banned.has(c) || rank.includes(c)) continue
          const vs = vals[c]!
          if (!left.every(i => vs[i]![1] <= vs[i]![0])) continue
          const n = left.filter(i => steps[i]!.lower && vs[i]![1] < vs[i]![0]).length
          if (n > most) (pick = c, most = n)
        }
        if (pick < 0) return undefined
        rank.push(pick)
        left = left.filter(i => !(vals[pick]![i]![1] < vals[pick]![i]![0]))
      }
      return left.some(i => steps[i]!.lower) ? undefined : (rank.length ? rank.map(c => cands[c]!) : [k(0)])
    }
    // the first rank, then those without its first component
    const ranks: E[][] = [], first = build(new Set())
    if (first) ranks.push(first)
    for (let c = 0; c < cands.length && ranks.length < 3 && first; c++) {
      if (id(cands[c]) !== id(first[0])) continue
      const r = build(new Set([c]))
      if (r && !ranks.some(x => id(x) === id(r))) ranks.push(r)
    }
    const fresh = ranks.filter(r => !tried.has(id(r)))
    if (!fresh.length) break
    let learnt = false
    for (const rank of fresh) {
      const ms = until - clock()
      if (ms < 200) break
      tried.add(id(rank)); best ??= rank
      last = withDeadline(clock() + ms / 3, () => proveLiveness(m, laws, {...l, rank}))
      if (last.proven && last.checked) return {proven: true, checked: true, rank, laws: [], found: {rank: text(rank), laws: []}}
      if (last.failed?.witness && fromWitness(last.failed.witness, last.failed.goal)) learnt = true
    }
    if (!learnt) break
  }
  if (!best) return {proven: false, checked: false, why: `no rank of the rule's terms that the ${steps.length} steps sampled allow`}
  // the first rank with the invariants its goals need
  const rank = best, lv: Liveness = {...l, rank}, ms = until - clock()
  if (ms > 300) {
    const {stay, cover, helps} = livenessParts(m, lv), inf = inferLaws(draws.rule ?? m, laws, [stay, cover, ...helps], {ms})
    const kept = inf.found.filter(f => !f.law.forall && !f.law.keys?.length), more = kept.map(f => f.law)
    if (inf.proven && more.length) {
      const again = withDeadline(until + 5000, () => proveLiveness(m, [...laws, ...more], lv))
      if (again.proven && again.checked) return {proven: true, checked: true, rank, laws: more, found: {rank: text(rank), laws: kept.map(f => f.text)}}
    }
  }
  const failed = last?.failed ? {goal: last.failed.goal, stuck: last.failed.stuck, ...(last.failed.witness ? {witness: last.failed.witness} : {})} : {}
  return {proven: false, checked: false, rank, found: {rank: text(rank), laws: []}, ...failed, why: `rank ${text(rank)} of the rule's terms, from ${steps.length} steps sampled; the kernel's goals not proven with it`}
}
