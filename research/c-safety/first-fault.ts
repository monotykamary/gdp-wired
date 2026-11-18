// Research specification, not a C reader. The caller supplies an ordered trace
// schema with guards over defined prefixes. The monitor cannot verify coverage
// or that the source preserves this order.
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {all, any, bool, type Cond, lit, rule, when} from '../../core/dsl.ts'
import {leanProject, toLean} from '../../lean-kernel/emit.ts'

export function firstFault(sites: readonly {previous: Cond, reached: Cond, bad: Cond}[]) {
  let live = all(...sites.map(s => s.previous.not()))
  const next = sites.map(s => {
    const hit = all(live, s.reached, s.bad)
    live = live.and(hit.not())
    return s.previous.or(hit)
  })
  return {next, live}
}

export function safeArrayModel() {
  const r = rule('guarded two-slot cursor').inputs({read: bool}).state({i: 0, alarm: bool.from(false)})
    .step(({i, alarm, read}) => {
      const {next, live} = firstFault([{previous: alarm, reached: read, bad: i.atLeast(2)}])
      return {i: when(live.and(read), when(i.eq(0), 1, 0), i), alarm: next[0]!}
    })
  const law = r.law('the cursor is in range and no access faults', ({i, alarm}) => i.lt(2).and(alarm.not()))
  return {r, law}
}

export function orderedModel() {
  const r = rule('two ordered abstract operations').inputs({event: bool, branch: bool, u: bool, v: bool, refused: bool})
    .state({a: bool.from(false), b: bool.from(false), data: 0, result: 0})
    .step(({a, b, event, branch, u, v, data, result, refused}) => {
      const {next, live} = firstFault([{previous: a, reached: event, bad: u}, {previous: b, reached: event.and(branch), bad: v}])
      const commit = all(live, event, refused.not())
      return {a: next[0]!, b: next[1]!, data: when(commit, lit(1).minus(data), data), result: when(commit, 0, result)}
    })
  const order = r.stepLaw('only the first reached fault fires, independently of later refusal', (x, y) => {
    const clear = any(x.a, x.b).not(), a = x.event.and(x.u), b = all(x.event, x.u.not(), x.branch, x.v)
    return clear.implies(y.a.iff(a).and(y.b.iff(b)))
  })
  const absorb = r.stepLaw('an alarm cannot clear and faulted turns frame both slots', (x, y) => all(
    x.a.implies(y.a), x.b.implies(y.b), any(y.a, y.b).implies(all(y.data.eq(x.data), y.result.eq(x.result))),
    any(x.a, x.b).implies(all(y.a.iff(x.a), y.b.iff(x.b))),
  ))
  return {r, order, absorb}
}

if (import.meta.main) {
  const dir = process.argv[2]
  if (!dir) throw new Error('supply an output project directory')
  const {r, law} = safeArrayModel()
  const text = toLean([{id: 'c_safe_bounds', machine: r.machine, laws: [law]}], {native: false})
  if (!text.includes('theorem c_safe_bounds_laws')) throw new Error('the cursor law was not exported')
  mkdirSync(dir, {recursive: true})
  for (const [file, body] of Object.entries(leanProject(text))) writeFileSync(join(dir, file), body)
}
