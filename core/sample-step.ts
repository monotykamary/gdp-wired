// Hot random walks reuse the existing persistent compiled step. No request,
// random draw, sample order or work counter is skipped. Cold/unsupported machines
// keep the interpreter. A refused request returns undefined; other errors retain
// the interpreter's exception behavior (the sampler ends that trial).
import {type Machine, type Request, type State, carriedView, compileC, fastStep, interpret, numbersOf} from './machine.ts'
import {allowed} from './watch.ts'
type Env = Record<string, number>
export function sampleStep(m: Machine, run = interpret(m)): (params: Env, st: State, input: Request) => State | undefined {
  let calls = 0, step = run.step
  let accepts = (params: Env, st: State, input: Request) => allowed(m, run, params, st, input)
  return (params, st, input) => {
    if (++calls === 1000) {
      const fast = fastStep(m)
      if (fast) {
        step = fast
        const flags = Object.entries(m.step.flags ?? {}).map(([name, c]) => [name, compileC(c, m)] as const)
        const assume = m.assume && compileC(m.assume, m)
        accepts = !assume ? () => true : (params, st, input) => {
          const env = {...params, ...numbersOf(input), ...run.queries(params, st, input)}
          const view = carriedView(m, st, input, undefined, params)
          for (const [name, f] of flags) env[`?${name}`] = f(env, view) ? 1 : 0
          return assume(env, view)
        }
      }
    }
    return accepts(params, st, input) ? step(params, st, input) : undefined
  }
}
