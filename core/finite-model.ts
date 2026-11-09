// A model is not a counterexample until its completed finite machine state
// satisfies the entire current family and an enabled real step breaks the law.
// This is a falsifier only: an unsupported or failed completion proves nothing.
import {type Law, type Machine, type Request, type State, interpret} from './machine.ts'
import {finiteEvaluator} from './finite-houdini.ts'
import {keyValue} from '../kernel/prove.ts'
import {checkWall, WallExpired} from './wall.ts'
export type FiniteModel = {genuine: true, params: Record<string, number>, pre: State, request: Request, post: State} | {genuine: false, reason: string}
export function finiteModelChecker(m: Machine) {
  const run = interpret(m)
  return (family: Law[], law: Law, model: Record<string, number>, stop: () => boolean = () => false): FiniteModel => {
    checkWall('finite model completion')
    const unknown = (reason: string): FiniteModel => ({genuine: false, reason})
    if (stop()) return unknown('attempt exhausted')
    if (m.history || m.leasts) return unknown('unsupported state environment')
    const params = Object.fromEntries(m.params.map(k => [k, model[k] ?? 0]))
    const pre: State = {scalars: Object.fromEntries(Object.keys(m.state).map(k => [k, model[k] ?? 0])), maps: Object.fromEntries(Object.keys(m.maps ?? {}).map(k => [k, new Map<number, number>()])), defaults: Object.fromEntries(Object.keys(m.maps ?? {}).map(k => [k, 0]))}
    const request: Request = Object.fromEntries(m.inputs.map(k => [k, model[k] ?? 0]))
    for (const key of m.inputMaps ?? []) request[key] = new Map<number, number>()
    const natural = (x: number) => Number.isSafeInteger(x) && x >= 0
    if (![...Object.values(params), ...Object.values(pre.scalars), ...Object.values(request).filter((v): v is number => typeof v === 'number')].every(natural)) return unknown('non-natural assignment')
    for (const [name, value] of Object.entries(model)) {
      const bracket = name.indexOf('['), map = name.slice(0, bracket)
      if (bracket < 0 || !name.endsWith(']')) continue
      const cells = pre.maps[map] ?? (request[map] instanceof Map ? request[map] as Map<number, number> : undefined)
      if (!cells) continue // Derived counts and post-state cells are recomputed, never trusted.
      const key = keyValue(name, model)
      if (key === undefined || !natural(key) || !natural(value)) return unknown('unreadable finite cell')
      if (cells.has(key) && cells.get(key) !== value) return unknown('inconsistent finite aliases')
      cells.set(key, value)
    }
    const evaluate = finiteEvaluator(m, stop)
    try {
      if (m.pre && evaluate({name: 'finite parameter precondition', holds: m.pre}, params, pre) !== true) return unknown('parameter precondition')
      for (const member of new Set([...family, law])) if (evaluate(member, params, pre) !== true) return unknown('predecessor does not satisfy the whole family')
      if (stop()) return unknown('attempt exhausted')
      const post = run.step(params, pre, request)
      if (evaluate(law, params, post) !== false) return unknown('no established post-state violation')
      return {genuine: true, params, pre, request, post}
    } catch (error) {
      if (error instanceof WallExpired) throw error
      return unknown('unsupported evaluation or refused request')
    }
  }
}
