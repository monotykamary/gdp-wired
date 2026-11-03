// Display a concurrent source witness without losing fiber identities or operation boundaries.
// Kept separate from the TypeScript reader so other CLI frontends do not acquire its optional dependency.
import {interpret} from './machine.ts'
import type {Extraction} from './extract.ts'
import type * as dsl from './dsl.ts'

export function fiberRun(x: Extraction, run: {params: Record<string, number>, trace: Record<string, unknown>[]}, renderCall?: (q: Record<string, unknown>) => string): string[] {
  const fibers = x.fibers ?? [], r = x.rule as never as {machine: dsl.Rule['machine'], parts: {inputs: [string, dsl.Kind<unknown>][]}, encodeParams: (p: unknown) => Record<string, number>}
  const go = interpret(r.machine), ps = r.encodeParams(run.params), method = new Map(r.parts.inputs).get('method') as {decode: (n: string, v: unknown) => string} | undefined
  let st = go.init(ps)
  return run.trace.map(q => {
    const f = Number(q.fiber), pc = st.maps.__gdp_pc?.get(f) ?? 0, m = method ? method.decode('method', q) : x.model?.events[0]?.call ?? 'step'
    st = go.step(ps, st, q as never)
    if (pc === 0) {
      const sp = fibers.find(s2 => s2.name === m), args = (x.names ?? []).filter(n => n.role === 'input' && n.method === m && n.rule in q).map(n => `${n.code.split('.').pop()} = ${String(q[n.rule])}`)
      return `fiber ${f}: ${renderCall ? renderCall(q) : `${m}(${args.join(', ')})`}${sp ? `, its step 1 of ${sp.steps}` : ''}`
    }
    const sp = fibers.find(s2 => pc > s2.base && pc <= s2.base + s2.steps)!
    return `fiber ${f}: ${sp.name}, its step ${pc - sp.base} of ${sp.steps}`
  })
}
