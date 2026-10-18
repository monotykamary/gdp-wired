// A law or a step law read off one run as it happens: the concrete side of kernel.ts's goals. The same description
// (a Law, or a StepLaw with its `steps`, `when` and `then`) is proven about every run by the kernel, searched for a
// breaking run by Handwired (research/hw/compile.ts), and read here on one run: the examples' random runs (examples/harness.ts),
// the replay of every counterexample the search finds, and the reference the Handwired search is checked against.
//
// A law holds at the start and after every step (at every key, for a law about every key). A step law over k steps holds
// at every k steps in a row the run takes: each step's `when` read with the state it starts from, its request, queries
// and flags; `then` with the state before the first step (plain names), the first request and its flags, the j-th
// request as input@j, and the state and maps after the last step (primed names).
import {type Law, type Machine, type Request, type State, carriedView, evalC, type interpret, numbersOf} from './machine.ts'
import type {StepLaw} from '../kernel/kernel.ts'

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

// Watches one law or step law along one run: `start` with the state at the start, `step` after each step the run takes
// (the state before, the request, the state after). Each says whether the law still holds.
export function watch(m: Machine, run: Runtime, w: Watched, params: Env, bound: number) {
  // At every tuple of the keys, one key per name.
  const atKeys = (forall: string | undefined, keys: number[], f: (env: Env) => boolean, more: string[] = []): boolean => {
    const names = forall ? [forall, ...more] : []
    const go = (i: number, env: Env): boolean => (i === names.length ? f(env) : keys.every(key => go(i + 1, {...env, [names[i]!]: key})))
    return go(0, {})
  }
  if (!isStepLaw(w)) {
    const holds = (st: State) => atKeys(w.forall, keysOf(bound, st), extra => evalC(w.holds, {...params, ...extra}, st, m), w.keys)
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
      return atKeys(w.forall, keysOf(bound, first, after), extra => evalC(w.then, {...env, ...extra}, both, primedMaps), w.keys)
    },
  }
}
