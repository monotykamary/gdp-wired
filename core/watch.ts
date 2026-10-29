// A law or a step law read off one run as it happens: the concrete side of kernel.ts's goals. The same description
// (a Law, or a StepLaw with its `steps`, `when` and `then`) is proven about every run by the kernel, searched for a
// breaking run by Handwired (research/hw/compile.ts), and read here on one run: the examples' random runs (examples/harness.ts),
// the replay of every counterexample the search finds, and the reference the Handwired search is checked against.
//
// A law holds at the start and after every step (at every key, for a law about every key). A step law over k steps holds
// at every k steps in a row the run takes: each step's `when` read with the state it starts from, its request, queries
// and flags; `then` with the state before the first step (plain names), the first request and its flags, the j-th
// request as input@j, and the state and maps after the last step (primed names).
import {type C, type E, type Law, type Machine, type Request, type State, carriedView, evalC, type interpret, numbersOf} from './machine.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {someHolds} from './exists.ts'

export type Watched = Law | StepLaw
export const isStepLaw = (w: Watched): w is StepLaw => 'then' in w
type Runtime = ReturnType<typeof interpret>
type Env = Record<string, number>
type Taken = {before: State, input: Request, after: State}

// A request's environment: the params, its inputs and queries, and the step's flags decided (as ?name).
export function requestEnv(m: Machine, run: Runtime, params: Env, st: State, input: Request): Env {
  const env: Env = {...params, ...numbersOf(input), ...run.queries(params, st, input)}, seen = carriedView(m, st, input)
  for (const [name, c] of Object.entries(m.step.flags ?? {})) env[`?${name}`] = evalC(c, env, seen, m) ? 1 : 0
  return env
}
// Whether the machine allows the request: its assumption, read with the queries and flags.
// A request whose order goes back (with a pruned history) is one the runtimes refuse.
export const allowed = (m: Machine, run: Runtime, params: Env, st: State, input: Request): boolean => {
  const order = m.history?.prune?.order
  if (order !== undefined && st.last !== undefined && (input[order] as number) < st.last) return false
  return !m.assume || evalC(m.assume, requestEnv(m, run, params, st, input), carriedView(m, st, input), m)
}

// The keys a law about every key is read at: 0 to bound + 1, and every key a map holds.
export const keysOf = (bound: number, ...states: State[]): number[] => {
  const keys = new Set<number>(Array.from({length: bound + 2}, (_, i) => i))
  for (const st of states) for (const cells of Object.values(st.maps)) for (const key of cells.keys()) keys.add(key)
  return [...keys]
}

// The values each of a law's names is read at, where its reads say (a key's sort, as kernel/prove.ts's keySorted reads
// one): a name in a map's key c·x + … (k·N + j, k·N² + j·N + i) takes, from each key the map holds, its digit there
// (the key in mixed radix by the coefficients), besides 0 to bound + 1; a name some read keys in any other way, or that
// no read keys, every key (keysOf). A composed key's value is no value of its parts (Locked[e·64 + a] at e = 70 reads a
// cell no map holds), so a law over n names was read at (keys)^n tuples a step for nothing. Untrusted: it chooses where
// a run checks a law, as before; the kernel proves it everywhere.
const linKey = (e: E): {terms: [string, number][], c: number} | undefined => {
  if (e.op === 'var') return {terms: [[e.name, 1]], c: 0}
  if (e.op === 'const') return {terms: [], c: e.value}
  if (e.op === 'mul') { const a = linKey(e.a); return a && e.k > 0 ? {terms: a.terms.map(([x, c]) => [x, c * e.k]), c: a.c * e.k} : undefined }
  if (e.op === 'add') { const a = linKey(e.a), b = linKey(e.b); return a && b ? {terms: [...a.terms, ...b.terms], c: a.c + b.c} : undefined }
  return undefined
}
function readValues(c: C, names: string[]): Map<string, {map: string, terms: [string, number][], c: number}[]> | undefined {
  const out = new Map<string, {map: string, terms: [string, number][], c: number}[]>(), wide = new Set<string>()
  const inE = (e: E): void => {
    if (e.op === 'get') {
      const l = linKey(e.key), mentioned = names.filter(x => JSON.stringify(e.key).includes(`"name":${JSON.stringify(x)}`))
      if (l && l.terms.every(([x]) => names.includes(x)) && new Set(l.terms.map(([x]) => x)).size === l.terms.length) for (const [x] of l.terms) { if (!out.has(x)) out.set(x, []); out.get(x)!.push({map: e.map, ...l}) }
      else for (const x of mentioned) wide.add(x)
      inE(e.key)
    } else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else))
    else if ('a' in e) { inE(e.a); if ('b' in e) inE(e.b) }
  }
  const inC = (x: C): void => { if (x.op === 'and' || x.op === 'or') x.xs.forEach(inC); else if (x.op === 'not') inC(x.x); else if (x.op === 'all') inC(x.c); else if ('a' in x) (inE(x.a), inE(x.b)) }
  inC(c)
  for (const x of wide) out.delete(x)
  return out.size ? out : undefined
}
const keysPer = (reads: ReturnType<typeof readValues>, names: string[], bound: number, st: State, all: () => number[]): number[][] => names.map(x => {
  const rs = reads?.get(x)
  if (!rs) return all()
  const vals = new Set<number>(Array.from({length: bound + 2}, (_, i) => i))
  for (const r of rs) {
    const terms = [...r.terms].sort((a, b) => b[1] - a[1])
    for (const key of st.maps[r.map]?.keys() ?? []) {
      let rest = key - r.c
      if (rest < 0) continue
      for (const [y, c] of terms) { const d = Math.floor(rest / c); rest -= d * c; if (y === x) vals.add(d) }
    }
  }
  return [...vals]
})

// Watches one law or step law along one run: `start` with the state at the start, `step` after each step the run takes
// (the state before, the request, the state after). Each says whether the law still holds.
export function watch(m: Machine, run: Runtime, w: Watched, params: Env, bound: number) {
  // At every tuple of the keys (each name's own: keysPer), one key per name, in one environment set in place.
  const names = w.forall ? [w.forall, ...(w.keys ?? [])] : [], reads = names.length ? readValues(isStepLaw(w) ? w.then : w.holds, names) : undefined
  const atKeys = (keys: number[][], env: Env, f: (env: Env) => boolean): boolean => {
    const go = (i: number): boolean => {
      if (i === names.length) return f(env)
      for (const key of keys[i]!) { env[names[i]!] = key; if (!go(i + 1)) return false }
      return true
    }
    return go(0)
  }
  if (!isStepLaw(w)) {
    // A law with "there exists" (core/exists.ts): broken only where no value can be a witness, as far as that is decided
    // (one natural or integer read linearly); undecided, it is kept.
    const at = (env: Env, st: State) => (w.some?.length ? someHolds(w.holds, w.some, {...env}, st, m)?.holds ?? true : evalC(w.holds, env, st, m))
    const holds = (st: State) => atKeys(keysPer(reads, names, bound, st, () => keysOf(bound, st)), {...params}, env => at(env, st))
    return {start: holds, step: (_before: State, _input: Request, after: State) => holds(after)}
  }
  const k = w.steps ?? 1, whens = w.when === undefined ? [] : Array.isArray(w.when) ? w.when : [w.when]
  // `then` reads a primed map's cells and initial value as its own map's.
  const primedMaps: Machine = {...m, maps: {...m.maps, ...Object.fromEntries(Object.entries(m.maps ?? {}).map(([n, init]) => [`${n}'`, init]))}}
  const window: Taken[] = []
  return {
    start: (_st: State) => true,
    step: (before: State, input: Request, after: State) => {
      window.push({before, input, after})
      if (window.length > k) window.shift()
      if (window.length < k) return true
      const envs = window.map(t => requestEnv(m, run, params, t.before, t.input))
      if (whens.some((c, j) => !evalC(c, envs[j]!, carriedView(m, window[j]!.before, window[j]!.input), m))) return true
      const env: Env = {...envs[0]!}
      window.slice(1).forEach((t, j) => { for (const i of m.inputs) env[`${i}@${j + 2}`] = envs[j + 1]![i]! })
      // The first state with the first request's maps; each later request's maps as map@j; the last state primed.
      let first = carriedView(m, window[0]!.before, window[0]!.input)
      window.slice(1).forEach((t, j) => { first = carriedView(m, first, t.input, map => `${map}@${j + 2}`) })
      const both: State = {
        scalars: {...first.scalars, ...Object.fromEntries(Object.entries(after.scalars).map(([n, v]) => [`${n}'`, v]))},
        maps: {...first.maps, ...Object.fromEntries(Object.entries(after.maps).map(([n, cells]) => [`${n}'`, cells]))},
        defaults: {...first.defaults, ...Object.fromEntries(Object.entries(after.defaults ?? {}).map(([n, d]) => [`${n}'`, d]))},
      }
      return atKeys(keysPer(reads, names, bound, both, () => keysOf(bound, first, after)), {...env}, e => evalC(w.then, e, both, primedMaps))
    },
  }
}
