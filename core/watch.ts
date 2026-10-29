// A law or a step law read off one run as it happens: the concrete side of kernel.ts's goals. The same description
// (a Law, or a StepLaw with its `steps`, `when` and `then`) is proven about every run by the kernel, searched for a
// breaking run by Handwired (research/hw/compile.ts), and read here on one run: the examples' random runs (examples/harness.ts),
// the replay of every counterexample the search finds, and the reference the Handwired search is checked against.
//
// A law holds at the start and after every step (at every key, for a law about every key). A step law over k steps holds
// at every k steps in a row the run takes: each step's `when` read with the state it starts from, its request, queries
// and flags; `then` with the state before the first step (plain names), the first request and its flags, the j-th
// request as input@j, and the state and maps after the last step (primed names).
import {type C, type E, type Law, type Machine, type Request, type State, carriedView, evalC, type interpret, numbersOf, walk} from './machine.ts'
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

// A key c·x + … + d as its coefficients by name ('1': d), where each name `ok` takes (core/infer.ts's pairings too).
export const linKey = (e: E, ok: (v: string) => boolean, k: number, out: Map<string, number>): boolean => (e.op === 'const' ? (out.set('1', (out.get('1') ?? 0) + k * e.value), true) : e.op === 'var' ? ok(e.name) && (out.set(e.name, (out.get(e.name) ?? 0) + k), true) : e.op === 'add' ? linKey(e.a, ok, k, out) && linKey(e.b, ok, k, out) : e.op === 'mul' ? linKey(e.a, ok, k * e.k, out) : false)
// The keys each of a law's names is read at: a name keyed in a map's reads (M[x], M[k·N + j], M[k·N² + j·N + i]) only
// linearly takes, of each key the map holds, its digit there (the key in mixed radix by the coefficients), and 0 to
// bound + 1; a name keyed otherwise, or nowhere, every key (keysOf). A composed key is no value of its parts, and a law
// about n names was read at (keys)^n tuples a step. Untrusted: where a run checks a law.
function keysPer(c: C, names: string[]): (bound: number, st: State, all: () => number[]) => number[][] {
  const reads = new Map<string, {map: string, l: [string, number][], d: number}[]>(), wide = new Set<string>()
  walk(c, o => {
    if (o.op !== 'get') return
    const l = new Map<string, number>(), key = JSON.stringify(o.key)
    if (linKey(o.key as E, x => names.includes(x), 1, l)) { const d = l.get('1') ?? 0; l.delete('1'); const t = [...l].sort((a, b) => b[1] - a[1]); for (const [x] of t) reads.set(x, [...(reads.get(x) ?? []), {map: o.map as string, l: t, d}]) }
    else for (const x of names) if (key.includes(`"name":${JSON.stringify(x)}`)) wide.add(x)
  })
  return (bound, st, all) => names.map(x => {
    const rs = reads.get(x)
    if (!rs || wide.has(x)) return all()
    const vals = new Set(Array.from({length: bound + 2}, (_, i) => i))
    for (const r of rs) for (const key of st.maps[r.map]?.keys() ?? []) {
      let rest = key - r.d
      if (rest >= 0) for (const [y, c] of r.l) { const v = Math.floor(rest / c); rest -= v * c; if (y === x) vals.add(v) }
    }
    return [...vals]
  })
}

// The tuples every watch has read a law at (core/dsl.ts's refuteByRuns counts its budget in them).
export const watchWork = {n: 0}
// Watches one law or step law along one run: `start` with the state at the start, `step` after each step the run takes
// (the state before, the request, the state after). Each says whether the law still holds.
export function watch(m: Machine, run: Runtime, w: Watched, params: Env, bound: number) {
  // At every tuple of the keys (each name's own: keysPer), one key per name, in one environment set in place.
  const names = w.forall ? [w.forall, ...(w.keys ?? [])] : [], per = keysPer(isStepLaw(w) ? w.then : w.holds, names)
  const atKeys = (keys: number[][], env: Env, f: (env: Env) => boolean): boolean => {
    const go = (i: number): boolean => {
      if (i === names.length) { watchWork.n++; return f(env) }
      for (const key of keys[i]!) { env[names[i]!] = key; if (!go(i + 1)) return false }
      return true
    }
    return go(0)
  }
  if (!isStepLaw(w)) {
    // A law with "there exists" (core/exists.ts): broken only where no value can be a witness, as far as that is decided
    // (one natural or integer read linearly); undecided, it is kept.
    const at = (env: Env, st: State) => (w.some?.length ? someHolds(w.holds, w.some, {...env}, st, m)?.holds ?? true : evalC(w.holds, env, st, m))
    const holds = (st: State) => atKeys(per(bound, st, () => keysOf(bound, st)), {...params}, env => at(env, st))
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
      return atKeys(per(bound, both, () => keysOf(bound, first, after)), {...env}, e => evalC(w.then, e, both, primedMaps))
    },
  }
}
