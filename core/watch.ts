// A law or a step law read off one run as it happens: the concrete side of kernel.ts's goals. The same description
// (a Law, or a StepLaw with its `steps`, `when` and `then`) is proven about every run by the kernel, searched for a
// breaking run by Handwired (hw/compile.ts), and read here on one run: the examples' random runs (examples/harness.ts),
// the replay of every counterexample the search finds, and the reference the Handwired search is checked against.
//
// A law holds at the start and after every step (at every key, for a law about every key). A step law over k steps holds
// at every k steps in a row the run takes: each step's `when` read with the state it starts from, its request, queries
// and flags; `then` with the state before the first step (plain names), the first request and its flags, the j-th
// request as input@j, and the state and maps after the last step (primed names).
import {type Law, type Machine, type State, evalC, type interpret} from './machine.ts'
import type {StepLaw} from '../kernel/kernel.ts'

export type Watched = Law | StepLaw
export const isStepLaw = (w: Watched): w is StepLaw => 'then' in w
type Runtime = ReturnType<typeof interpret>
type Env = Record<string, number>
type Taken = {before: State, input: Env, after: State}

// A request's environment: the params, its inputs and queries, and the step's flags decided (as ?name).
export function requestEnv(m: Machine, run: Runtime, params: Env, st: State, input: Env): Env {
  const env: Env = {...params, ...input, ...run.queries(params, st, input)}
  for (const [name, c] of Object.entries(m.step.flags ?? {})) env[`?${name}`] = evalC(c, env, st, m) ? 1 : 0
  return env
}
// Whether the machine allows the request: its assumption, read with the queries and flags.
// A request whose order goes back (with a pruned history) is one the runtimes refuse.
export const allowed = (m: Machine, run: Runtime, params: Env, st: State, input: Env): boolean => {
  const order = m.history?.prune?.order
  if (order !== undefined && st.last !== undefined && input[order]! < st.last) return false
  return !m.assume || evalC(m.assume, requestEnv(m, run, params, st, input), st, m)
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
  const atKeys = (forall: string | undefined, keys: number[], f: (env: Env) => boolean) => (forall ? keys.every(key => f({[forall]: key})) : f({}))
  if (!isStepLaw(w)) {
    const holds = (st: State) => atKeys(w.forall, keysOf(bound, st), extra => evalC(w.holds, {...params, ...extra}, st, m))
    return {start: holds, step: (_before: State, _input: Env, after: State) => holds(after)}
  }
  const k = w.steps ?? 1, whens = w.when === undefined ? [] : Array.isArray(w.when) ? w.when : [w.when]
  // `then` reads a primed map's cells and initial value as its own map's.
  const primedMaps: Machine = {...m, maps: {...m.maps, ...Object.fromEntries(Object.entries(m.maps ?? {}).map(([n, init]) => [`${n}'`, init]))}}
  const window: Taken[] = []
  return {
    start: (_st: State) => true,
    step: (before: State, input: Env, after: State) => {
      window.push({before, input, after})
      if (window.length > k) window.shift()
      if (window.length < k) return true
      const envs = window.map(t => requestEnv(m, run, params, t.before, t.input))
      if (whens.some((c, j) => !evalC(c, envs[j]!, window[j]!.before, m))) return true
      const env: Env = {...envs[0]!}
      window.slice(1).forEach((t, j) => { for (const i of m.inputs) env[`${i}@${j + 2}`] = envs[j + 1]![i]! })
      const first = window[0]!.before
      const both: State = {
        scalars: {...first.scalars, ...Object.fromEntries(Object.entries(after.scalars).map(([n, v]) => [`${n}'`, v]))},
        maps: {...first.maps, ...Object.fromEntries(Object.entries(after.maps).map(([n, cells]) => [`${n}'`, cells]))},
      }
      return atKeys(w.forall, keysOf(bound, first, after), extra => evalC(w.then, {...env, ...extra}, both, primedMaps))
    },
  }
}
