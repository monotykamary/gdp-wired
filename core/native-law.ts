// A second interpretation of law syntax, over real JS observations, not DSL/IR values.
// Sharing the parser does not share arithmetic, choice encodings, absence or comparisons.
import type {X, LawOpts} from './laws.ts'
import {type NativeObservation, nativeSame} from './source-check.ts'
import type {NativeReading} from './native-observations.ts'
const NONE = Symbol('language None')
const truthy = (value: unknown): boolean => value !== NONE && Boolean(value)
const object = (x: unknown): x is Record<string, unknown> => x !== null && (typeof x === 'object' || typeof x === 'function')
const tag = (x: unknown, name: string) => Object.prototype.toString.call(x) === `[object ${name}]`
const unsupported = (what: string): never => { throw new Error(`native law cannot interpret ${what}`) }
const number = (x: unknown): number => x as number // Type assertion only: JS, including NaN/coercion, does the operation.
const equal = (a: unknown, b: unknown): boolean => a === NONE ? b === null || b === undefined || b === NONE : b === NONE ? a === null || a === undefined : nativeSame(a, b)
const keys = (x: unknown): unknown[] => tag(x, 'Map') || tag(x, 'Set') ? [...(x as Map<unknown, unknown>).keys()] : Array.isArray(x) ? x : object(x) ? Object.keys(x) : unsupported('quantification over a non-container')
const has = (container: unknown, key: unknown): boolean => tag(container, 'Map') || tag(container, 'Set') ? (container as Map<unknown, unknown>).has(key) : Array.isArray(container) ? container.some(value => nativeSame(value, key)) : object(container) ? Object.hasOwn(container, String(key)) : unsupported('membership in a non-container')
const get = (container: unknown, key: unknown): unknown => tag(container, 'Map') ? (container as Map<unknown, unknown>).get(key) : object(container) || typeof container === 'string' ? (container as Record<string, unknown>)[String(key)] : undefined
function businessDays(a: unknown, b: unknown, opts: LawOpts): number {
  if (typeof a !== 'number' || typeof b !== 'number' || !Number.isFinite(a) || !Number.isFinite(b)) return NaN
  if (!opts.calendar || !opts.clock) return unsupported('business days without a calendar and clock')
  const cal = opts.calendar, match = /^([+-])(\d{2}):(\d{2})$/.exec((cal.utc_offset ?? '+00:00').trim())
  if (!match) return unsupported('calendar offset')
  const unit = 86400 * opts.clock, offset = (match[1] === '-' ? -1 : 1) * (Number(match[2]) * 3600 + Number(match[3]) * 60) * opts.clock
  const start = Math.floor((a + offset) / unit), end = Math.floor((b + offset) / unit)
  const weekend = new Set((cal.weekend ?? ['sat', 'sun']).map(s => s.trim().slice(0, 3).toLowerCase())), names = ['sun', 'mon', 'tue', 'wed', 'thu', 'fri', 'sat']
  const work = (d: number) => !weekend.has(names[((d + 4) % 7 + 7) % 7]!)
  const lo = Math.min(start, end), hi = Math.max(start, end), weeks = Math.floor((hi - lo) / 7)
  let count = weeks * (7 - weekend.size)
  for (let d = lo + weeks * 7 + 1; d <= hi; d++) if (work(d)) count++
  for (const date of new Set(cal.holidays ?? [])) {
    const d = Date.parse(`${date.trim()}T00:00:00Z`) / 86400000
    if (d > lo && d <= hi && work(d)) count--
  }
  return end >= start ? count : -count
}
export function nativeLaw(expression: X, opts: LawOpts, parse: (text: string) => X, constants: Record<string, number | string | boolean> = {}, knownNames: ReadonlySet<string> = new Set(), readings: readonly NativeReading[] = []): (observation: NativeObservation) => boolean {
  return observation => {
    const locals = new Map<string, unknown>()
    const scalarKey = (key: unknown) => { if (observation.nativeEquality === 'scalar' && object(key)) unsupported('foreign container equality or object keys') }
    const same = (a: unknown, b: unknown) => { scalarKey(a); scalarKey(b); return equal(a, b) }
    const at = (container: unknown, key: unknown) => { scalarKey(key); return get(container, key) }
    const contains = (container: unknown, key: unknown) => { scalarKey(key); return has(container, key) }
    const observedReading = (e: X & {k: 'path'}, state: unknown): {value: unknown, consumed: number} | undefined => {
      const fields = [e.head]
      for (const segment of e.segs) { if (!('f' in segment)) break; fields.push(segment.f) }
      const ordinary = Object.hasOwn(observation.bindings, e.head) || object(state) && e.head in state || Object.hasOwn(observation.params, e.head)
      const matches = readings.flatMap(reading => {
        if (reading.method && reading.method !== observation.method) return []
        const parts = reading.code.split('.')
        let consumed: number
        if (parts.every((part, i) => fields[i] === part)) consumed = parts.length - 1
        else if (parts.at(-1) === e.head) consumed = 0
        else return []
        const next = e.segs[consumed], called = next && 'call' in next
        if (ordinary && !called || reading.kind === 'clock' && called) return []
        if (called && next.args) return unsupported('specific arguments on an observed one-value-per-step answer')
        return [{reading, consumed: consumed + (called ? 1 : 0)}]
      }).sort((a, b) => b.consumed - a.consumed)
      if (!matches.length) return undefined
      const selected = matches[0]!
      if (matches.some(other => other.consumed === selected.consumed && (other.reading.key !== selected.reading.key || other.reading.kind !== selected.reading.kind)))
        return unsupported(`ambiguous observed answer ${e.head}`)
      const reading = selected.reading
      if (reading.kind === 'clock') {
        if (reading.key !== 'now' || observation.observed?.clock === undefined) return unsupported('unobserved native clock read')
        return {value: observation.observed.clock, consumed: selected.consumed}
      }
      const expected = reading.kind === 'raises' ? `${reading.key}.raises` : reading.key
      if (reading.code !== expected) return unsupported('native answer binding does not identify its original call')
      const call = observation.observed?.calls[reading.key]
      if (!call) return unsupported(`unobserved native call ${reading.key}`)
      if (reading.kind === 'raises') return {value: call.kind === 'raised' ? call.raised : null, consumed: selected.consumed}
      if (call.kind !== 'returned') return unsupported(`native call ${reading.key} raised instead of returning`)
      return {value: call.value, consumed: selected.consumed}
    }
    const evaluate = (e: X, old = false): unknown => {
      switch (e.k) {
        case 'num': case 'bool': return e.v
        case 'str': return e.holes ? e.parts!.reduce((s, part, i) => s + part + (i < e.holes!.length ? String(evaluate(e.holes![i]!, old)) : ''), '') : e.v
        case 'null': return e.absence === 'undefined' ? undefined : e.absence === 'null' ? null : NONE
        case 'dur': return e.v * (opts.clock ?? unsupported('a duration without a clock'))
        case 'bdur': return unsupported('business days outside an elapsed-time comparison')
        case 'old': return evaluate(e.x, true)
        case 'un': return e.op === 'not' ? !truthy(evaluate(e.x, old)) : -number(evaluate(e.x, old))
        case 'forall': {
          const domain = evaluate(e.over, old), previous = locals.get(e.v), existed = locals.has(e.v)
          try { return keys(domain).every(k => { locals.set(e.v, k); return truthy(evaluate(e.body, old)) }) }
          finally { if (existed) locals.set(e.v, previous); else locals.delete(e.v) }
        }
        case 'fn': {
          const xs = e.xs.map(x => evaluate(x, old))
          if (e.f === 'abs') return Math.abs(number(xs[0]))
          if (e.f === 'min') return Math.min(...xs.map(number))
          if (e.f === 'max') return Math.max(...xs.map(number))
          if (e.f === 'sum') {
            if (xs.length !== 1) return unsupported('sum with several arguments')
            const values: unknown[] = tag(xs[0], 'Map') ? [...(xs[0] as Map<unknown, unknown>).values()] : Array.isArray(xs[0]) ? xs[0] : object(xs[0]) ? Object.values(xs[0]) : unsupported('sum over a non-container')
            return values.reduce<number>((sum, value) => sum + number(value), 0)
          }
          return unsupported(`function ${e.f}`)
        }
        case 'path': {
          const state = old ? observation.before : observation.after
          const reading = observedReading(e, state)
          let value: unknown
          if (reading) value = reading.value
          else if (['this', 'self'].includes(e.head)) value = state
          else if (e.head === 'before') value = observation.before
          else if (e.head.startsWith('@') && object(state)) value = state[e.head.slice(1)]
          else if (locals.has(e.head)) value = locals.get(e.head)
          else if (Object.hasOwn(observation.bindings, e.head)) value = observation.bindings[e.head]
          else if (e.head === 'result') {
            if (old) return unsupported('old(result), which is not native source state')
            value = !e.segs.length && observation.legacyResult ? get(observation.result, 'value') : observation.result
          } else if (e.head === 'failed') value = observation.legacyResult ? get(observation.result, 'failed') : observation.failed
          else if (e.head === 'method') value = observation.method
          else if (object(state) && e.head in state) value = state[e.head]
          else if (Object.hasOwn(observation.params, e.head)) value = observation.params[e.head]
          else if (Object.hasOwn(observation.inputs, e.head)) value = observation.inputs[e.head]
          else if (e.head === observation.method && 'call' in (e.segs[0] ?? {})) value = observation.result
          else if (Object.hasOwn(constants, e.head)) value = constants[e.head]
          else if (knownNames.has(e.head)) return unsupported(`native value of ${e.head} is unavailable`)
          else if (!e.segs.length) value = e.head // A bare enum label; buildLaw already checked its domain.
          else return unsupported(`name ${e.head}`)
          for (let i = reading?.consumed ?? 0; i < e.segs.length; i++) {
            const s = e.segs[i]!
            if ('f' in s) {
              const next = e.segs[i + 1]
              if (next && 'call' in next && ((tag(value, 'Map') && ['get', 'has'].includes(s.f)) || (tag(value, 'Set') && s.f === 'has'))) {
                const key = next.args ? evaluate(parse(next.args), old) : undefined
                value = s.f === 'get' ? at(value, key) : contains(value, key); i++
              } else if (s.f === 'size' && (tag(value, 'Map') || tag(value, 'Set'))) value = (value as Map<unknown, unknown>).size
              else value = at(value, s.f)
            }
            else if ('i' in s) value = at(value, evaluate(s.i, old))
            else if (i === 0 && e.head === observation.method) {
              const expected = s.args ? s.args.split(',').map(a => evaluate(parse(a), old)) : []
              if (expected.length && (expected.length !== observation.args.length || expected.some((v, k) => !same(v, observation.args[k])))) return unsupported('a method call with different arguments')
            } else return unsupported('an unobserved method call')
          }
          return value
        }
        case 'bin': {
          if (e.op === '&&') return truthy(evaluate(e.a, old)) && truthy(evaluate(e.b, old))
          if (e.op === '||') return truthy(evaluate(e.a, old)) || truthy(evaluate(e.b, old))
          if (e.op === '=>') return !truthy(evaluate(e.a, old)) || truthy(evaluate(e.b, old))
          const calendarOperand = (x: X): unknown => x.k === 'bdur' ? x.v : x.k === 'bin' && x.op === '-' ? businessDays(evaluate(x.b, old), evaluate(x.a, old), opts) : unsupported('business-day operand')
          const calendar = e.a.k === 'bdur' || e.b.k === 'bdur'
          const a = calendar ? calendarOperand(e.a) : evaluate(e.a, old), b = calendar ? calendarOperand(e.b) : evaluate(e.b, old)
          switch (e.op) {
            case '==': return same(a, b)
            case '!=': return !same(a, b)
            case '<': return number(a) < number(b)
            case '<=': return number(a) <= number(b)
            case '>': return number(a) > number(b)
            case '>=': return number(a) >= number(b)
            case '+': return number(a) + number(b)
            case '-': return number(a) - number(b)
            case '*': return number(a) * number(b)
            case '/': return number(a) / number(b)
            case '//': return Math.floor(number(a) / number(b))
            case '%': return number(a) % number(b)
            case '&': return number(a) & number(b)
            case '|': return number(a) | number(b)
            case 'in': return contains(b, a)
            default: return unsupported(`operator ${e.op}`)
          }
        }
      }
    }
    return truthy(evaluate(expression))
  }
}
