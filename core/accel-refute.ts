// Checked accelerated refutation: finds counterexamples containing repeated steps
// ("repeat request S k times") whose closed-form affine effect Phi(j) = base + delta * j
// is proved by induction on j in [0, k) using the unmodified kernel (kernel/kernel.ts's
// check) and replayed concretely for all prefix and suffix steps under the rule's exact
// semantics. Never populates Verdict.run (concrete Request[]); callers report it as
// REFUTED (accelerated).
import {
  type C, type E, type Law, type Machine, type Request, type State,
  all, arithmetic, evalC, hasFinite, interpret, isArithmetic, n, not, numbersOf, same, seeded, x,
} from './machine.ts'
import {
  type Goal, type Path, type Tree, check, scope, substC, substE, truth,
} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
import {allowed} from './watch.ts'
import {checkWatchdog} from './search-watchdog.ts'
import {isSourceBound} from './source-check.ts'

export type ClosedFormVar = {base: number, delta: number}

export type AcceleratedStepSegment = {
  kind: 'step'
  request: Record<string, number>
  shown?: Record<string, unknown>
}

export type AcceleratedRepeatSegment = {
  kind: 'repeat'
  request: Record<string, number>
  shown?: Record<string, unknown>
  count: number
  startState: Record<string, number>
  endState: Record<string, number>
  closedForm: Record<string, ClosedFormVar>
  jVar: string
  allowGoal: Goal
  allowTree: Tree
  stepGoal: Goal
  stepTree: Tree
  checked: boolean
}

export type AcceleratedSegment = AcceleratedStepSegment | AcceleratedRepeatSegment

export type AcceleratedRun = {
  checked: boolean
  params: Record<string, number>
  shownParams?: Record<string, unknown>
  segments: AcceleratedSegment[]
  totalSteps: number
  law: string
  finalState: Record<string, number>
  witness: Record<string, number>
}

export type AccelRefuteOptions = {
  ms: number
  wall?: number // Absolute performance.now() deadline, independent of counted work.
  shownRequest?: (req: Request) => Record<string, unknown>
  shownParams?: (params: Record<string, number>) => Record<string, unknown>
  randomParams?: (rand: (k: number) => number, bound: number) => Record<string, number>
  randomInput?: (rand: (k: number) => number, bound: number, ps: Record<string, number>) => Request
}

const MAX_REPEAT = 1_000_000_000_000 // 10^12 (well above 2^32, well within safe integer arithmetic)
const ZERO: E = n(0)
const FALSE_C: C = {op: '<', a: ZERO, b: ZERO}

const debug = () => process.env.GDP_ACCEL_REFUTE_LOG === '1'
const log = (msg: string) => { if (debug()) process.stderr.write(`[accel-refute] ${msg}\n`) }

// Data-only admission before JSON comparison or interpreting a machine.
// Source and binder metadata remain on the exact objects; no user code runs
// via accessors, proxy traps, prototypes or serialization hooks.
function passiveData(values: unknown[]): boolean {
  const isProxy = typeof process === 'object' ? process.getBuiltinModule?.('node:util')?.types.isProxy : undefined
  if (!isProxy || Object.getPrototypeOf(Array.prototype) !== Object.prototype ||
      Object.hasOwn(Object.prototype, 'toJSON') || Object.hasOwn(Array.prototype, 'toJSON')) return false
  const seen = new WeakSet<object>(), active = new WeakSet<object>()
  let nodes = 0
  const visit = (value: unknown, depth: number): boolean => {
    if (value === null || value === undefined || typeof value === 'boolean' || typeof value === 'string') return true
    if (typeof value === 'number') return Number.isFinite(value)
    if (typeof value !== 'object' || isProxy(value) || active.has(value) || depth > 512) return false
    if (seen.has(value)) return true
    if (++nodes > 500_000) return false
    const array = Array.isArray(value), proto: unknown = Object.getPrototypeOf(value)
    if (proto !== null && proto !== (array ? Array.prototype : Object.prototype)) return false
    active.add(value)
    const keys = Reflect.ownKeys(value)
    let elements = 0
    for (const key of keys) {
      const d = Object.getOwnPropertyDescriptor(value, key)!
      if (!Object.hasOwn(d, 'value') || key === 'toJSON') return false
      if (array && key === 'length') continue
      if (!d.enumerable || array && key !== String(elements++)) return false
      if (!visit(d.value, depth + 1)) return false
    }
    if (array && elements !== value.length) return false
    active.delete(value); seen.add(value)
    return true
  }
  return values.every(value => visit(value, 0))
}

function canonicalArithmetic(m: Machine): boolean {
  const names = Object.keys(m.fns ?? {})
  if (names.some(f => !isArithmetic(f))) return false
  const divisors = names.map(f => Number(f.slice(4)))
  if (divisors.some(k => !Number.isSafeInteger(k) || k < 1)) return false
  const builtins = arithmetic(divisors)
  return exactKeys(builtins.fns, names) && names.every(f => jsonEqual(builtins.fns[f], m.fns![f])) &&
    jsonEqual(builtins.facts, m.facts ?? [])
}

export function accelRefuteFits(m: Machine, laws: Law[]): boolean {
  if (!passiveData([m, laws]) || isSourceBound(m, laws) || hasFinite([m, laws]) || !canonicalArithmetic(m)) return false
  if (Object.keys(m.maps ?? {}).length || m.history || m.inputMaps?.length) return false
  if (m.counts && Object.keys(m.counts).length) return false
  if (m.sums && Object.keys(m.sums).length) return false
  if (m.leasts && Object.keys(m.leasts).length) return false
  if (m.primitiveFailure) return false
  if (Object.values(m.step.flags ?? {}).some(f => f.op === 'all')) return false
  if (!laws.length || laws.some(l => l.forall || l.keys?.length || l.some?.length || l.finite)) return false
  return true
}

function freshVar(base: string, m: Machine): string {
  const taken = JSON.stringify(m)
  if (!taken.includes(JSON.stringify(base))) return base
  for (let i = 1; ; i++) {
    const cand = `${base}_${i}`
    if (!taken.includes(JSON.stringify(cand))) return cand
  }
}

function inlinePlainFlags(m: Machine): Record<string, C> {
  const out: Record<string, C> = Object.create(null)
  for (const [name, c] of Object.entries(m.step.flags ?? {})) {
    if (c.op === 'all') throw new Error(`quantified flag ${name} not supported in accelerated refutation`)
    out[name] = substC(c, {vars: {}, maps: {}, flags: out})
  }
  return out
}

function phiTerm(jVar: string, {base, delta}: ClosedFormVar, offset: 0 | 1): E {
  const c = base + offset * delta
  if (delta === 0) return n(c)
  if (delta > 0) {
    const mul: E = delta === 1 ? x(jVar) : {op: 'mul', k: delta, a: x(jVar)}
    return c === 0 ? mul : {op: 'add', a: n(c), b: mul}
  }
  const dec = -delta
  const mul: E = dec === 1 ? x(jVar) : {op: 'mul', k: dec, a: x(jVar)}
  return {op: 'sub', a: n(c), b: mul}
}

export function buildRepeatGoals(
  m: Machine,
  params: Record<string, number>,
  req: Record<string, number>,
  count: number,
  closedForm: Record<string, ClosedFormVar>,
  jVar: string,
): {allowGoal: Goal, stepGoal: Goal} {
  const flags = inlinePlainFlags(m)
  const varsAtJ: Record<string, E> = Object.create(null)
  for (const p of m.params) varsAtJ[p] = n(params[p] ?? 0)
  for (const inp of m.inputs) varsAtJ[inp] = n(req[inp] ?? 0)
  for (const sv of Object.keys(m.state)) varsAtJ[sv] = phiTerm(jVar, closedForm[sv]!, 0)
  const flagsAtJ: Record<string, C> = Object.create(null)
  for (const [fname, fc] of Object.entries(flags)) {
    flagsAtJ[fname] = substC(fc, {vars: varsAtJ, maps: {}, flags: {}})
  }
  const sub = {vars: varsAtJ, maps: {}, flags: flagsAtJ}
  const bound: C = {op: '<', a: x(jVar), b: n(count)}

  // Collect any active arithmetic function reads (div$k / mod$k) along branches not statically false,
  // and instantiate their machine facts so goals stay provable even when a repeating step divides.
  const emptyPath: Path = new Map()
  const collectActiveFacts = (root: E | C, seen: Set<string>, out: C[]) => {
    if (!m.facts?.length) return
    const visitE = (e: E) => {
      switch (e.op) {
        case 'var': case 'const': return
        case 'mul': visitE(e.a); return
        case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
          visitE(e.a); visitE(e.b); return
        case 'proj': visitE(e.a); return
        case 'if': {
          visitC(e.c)
          const t = truth(e.c, emptyPath)
          if (t !== false) visitE(e.then)
          if (t !== true) visitE(e.else)
          return
        }
        case 'get': {
          visitE(e.key)
          if (isArithmetic(e.map)) {
            const kStr = `${e.map}:${JSON.stringify(e.key)}`
            if (!seen.has(kStr)) {
              seen.add(kStr)
              const d = Number(e.map.slice(e.map.indexOf('$') + 1))
              for (const f of m.facts!) {
                if (f.forall && f.name.startsWith(`mod$${d}:`)) {
                  out.push(substC(f.holds, {vars: {[f.forall]: e.key}, maps: {}, flags: {}}))
                }
              }
            }
          }
          return
        }
      }
    }
    const visitC = (c: C) => {
      switch (c.op) {
        case 'not': visitC(c.x); return
        case 'and': case 'or': for (const ch of c.xs) visitC(ch); return
        case '<=': case '<': case '=': visitE(c.a); visitE(c.b); return
        case 'all': case 'flag': return
      }
    }
    if ('a' in root || 'xs' in root || root.op === 'not' || root.op === 'flag' || root.op === 'all') visitC(root as C)
    else visitE(root as E)
  }

  const allowFacts: C[] = []
  const assumeAtJ = m.assume ? substC(m.assume, sub) : undefined
  if (assumeAtJ) collectActiveFacts(assumeAtJ, new Set(), allowFacts)
  const allowGoal: Goal = {
    name: `accelerated repeat allow (k=${count})`,
    hyps: assumeAtJ ? [bound, ...allowFacts, not(assumeAtJ)] : [FALSE_C],
  }

  const stepEqs: C[] = []
  const stepFacts: C[] = []
  const seenStepFacts = new Set<string>()
  for (const sv of Object.keys(m.state)) {
    const rhs = m.step.state?.[sv] ?? x(sv)
    const lhs = substE(rhs, sub)
    collectActiveFacts(lhs, seenStepFacts, stepFacts)
    const want = phiTerm(jVar, closedForm[sv]!, 1)
    stepEqs.push(same(lhs, want))
  }
  const stepGoal: Goal = {
    name: `accelerated repeat step (k=${count})`,
    hyps: [bound, ...stepFacts, not(stepEqs.length === 1 ? stepEqs[0]! : all(...stepEqs))],
  }
  return {allowGoal, stepGoal}
}

// Prefix/suffix steps use the interpreter; the skipped steps must likewise stay in
// its safe-natural range. These conservative upper bounds use exact arithmetic,
// and examine both branches, even if only one is reachable.
function repeatStaysExact(m: Machine, params: Record<string, number>, seg: AcceleratedRepeatSegment): boolean {
  const limit = BigInt(Number.MAX_SAFE_INTEGER)
  const safe = (x: bigint): bigint => {
    if (x < 0n || x > limit) throw new RangeError('accelerated repeat exceeds exact interpreter range')
    return x
  }
  const hi = (a: bigint, b: bigint) => a > b ? a : b
  const lo = (a: bigint, b: bigint) => a < b ? a : b
  const env = new Map<string, bigint>(Object.entries({...params, ...seg.request}).map(([k, v]) => [k, BigInt(v)]))
  for (const [key, {base, delta}] of Object.entries(seg.closedForm)) {
    env.set(key, safe(hi(BigInt(base), BigInt(base) + BigInt(delta) * BigInt(seg.count - 1))))
  }
  const bound = (e: E): bigint => {
    switch (e.op) {
      case 'const': return safe(BigInt(e.value))
      case 'var': return env.get(e.name)!
      case 'add': return safe(bound(e.a) + bound(e.b))
      case 'sub': { const a = bound(e.a); bound(e.b); return a }
      case 'mul': return safe(BigInt(e.k) * bound(e.a))
      case 'prod': return safe(bound(e.a) * bound(e.b))
      case 'min': return lo(bound(e.a), bound(e.b))
      case 'max': return hi(bound(e.a), bound(e.b))
      case 'if': visit(e.c); return hi(bound(e.then), bound(e.else))
      case 'get': {
        const key = bound(e.key), d = BigInt(e.map.slice(4))
        return e.map.startsWith('div$') ? key / d : lo(key, d - 1n)
      }
      case 'proj': case 'tup': throw new RangeError('accelerated exact-range check does not support tuple terms')
    }
  }
  const visit = (c: C): void => {
    switch (c.op) {
      case 'and': case 'or': c.xs.forEach(visit); return
      case 'not': visit(c.x); return
      case 'flag': return
      case 'all': throw new RangeError('accelerated exact-range check does not support quantified conditions')
      case '<': case '<=': case '=': bound(c.a); bound(c.b)
    }
  }
  try {
    Object.values(m.step.flags ?? {}).forEach(visit)
    if (m.assume) visit(m.assume)
    Object.values(m.step.state ?? {}).forEach(bound)
    return true
  } catch { return false }
}

const jsonEqual = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b)
const exactKeys = (record: Record<string, unknown>, keys: string[]) => Object.keys(record).length === keys.length && keys.every(k => Object.hasOwn(record, k))

// Independent verifier: rebuilds goals instead of accepting supplied hypotheses.
// Euclidean facts are safe only for the built-in arithmetic functions, not for
// custom code or arbitrary facts whose names happen to match a divisor.
export function checkAcceleratedRun(m: Machine, laws: Law[], acc: AcceleratedRun): boolean {
  try { return verifyAcceleratedRun(m, laws, acc) } catch { return false }
}

function verifyAcceleratedRun(m: Machine, laws: Law[], acc: AcceleratedRun): boolean {
  if (!passiveData([acc]) || acc.checked !== true || !accelRefuteFits(m, laws) || !acc.segments.some(s => s.kind === 'repeat')) return false
  scope(m, laws)
  const stateKeys = Object.keys(m.state)
  if (!exactKeys(acc.params, m.params) || !exactKeys(acc.finalState, stateKeys)) return false
  const it = interpret(m)
  for (const p of m.params) {
    const val = acc.params[p]
    if (typeof val !== 'number' || !Number.isInteger(val) || val < 0 || !Number.isSafeInteger(val)) return false
  }
  if (m.pre && !evalC(m.pre, acc.params, {scalars: {}, maps: {}}, m)) return false
  let st: State
  try { st = it.init(acc.params) } catch { return false }
  let totalSteps = 0
  let lastBefore: State | undefined
  let lastReq: Record<string, number> | undefined

  for (const seg of acc.segments) {
    if (!exactKeys(seg.request, m.inputs)) return false
    for (const inp of m.inputs) {
      const val = seg.request[inp]
      if (typeof val !== 'number' || !Number.isInteger(val) || val < 0 || !Number.isSafeInteger(val)) return false
    }
    if (seg.kind === 'step') {
      if (!allowed(m, it, acc.params, st, seg.request)) return false
      lastBefore = st
      lastReq = seg.request
      try { st = it.step(acc.params, st, seg.request) } catch { return false }
      totalSteps += 1
    } else if (seg.kind === 'repeat') {
      if (seg.checked !== true || !Number.isSafeInteger(seg.count) || seg.count < 2 || seg.count > MAX_REPEAT) return false
      if (typeof seg.jVar !== 'string' || !seg.jVar || JSON.stringify(m).includes(JSON.stringify(seg.jVar))) return false
      if (![seg.startState, seg.endState, seg.closedForm].every(record => exactKeys(record, stateKeys))) return false
      const endScalars: Record<string, number> = {}, prevScalars: Record<string, number> = {}
      for (const sv of stateKeys) {
        const cf = seg.closedForm[sv]!
        if (!Number.isSafeInteger(cf.base) || cf.base < 0 || !Number.isSafeInteger(cf.delta)) return false
        if (cf.base !== st.scalars[sv] || cf.base !== seg.startState[sv]) return false
        const endVal = BigInt(cf.base) + BigInt(cf.delta) * BigInt(seg.count)
        const prevVal = endVal - BigInt(cf.delta)
        if (endVal < 0n || endVal > BigInt(Number.MAX_SAFE_INTEGER) || seg.endState[sv] !== Number(endVal)) return false
        if (prevVal < 0n || prevVal > BigInt(Number.MAX_SAFE_INTEGER)) return false
        endScalars[sv] = Number(endVal)
        prevScalars[sv] = Number(prevVal)
      }
      if (!repeatStaysExact(m, acc.params, seg)) return false
      const {allowGoal, stepGoal} = buildRepeatGoals(m, acc.params, seg.request, seg.count, seg.closedForm, seg.jVar)
      if (!jsonEqual(allowGoal, seg.allowGoal) || !check(allowGoal, seg.allowTree)) return false
      if (!jsonEqual(stepGoal, seg.stepGoal) || !check(stepGoal, seg.stepTree)) return false
      lastBefore = {scalars: prevScalars, maps: {}}
      lastReq = seg.request
      st = {scalars: endScalars, maps: {}}
      totalSteps += seg.count
    } else return false
  }
  if (!Number.isSafeInteger(totalSteps) || totalSteps !== acc.totalSteps) return false
  if (stateKeys.some(sv => st.scalars[sv] !== acc.finalState[sv])) return false
  const broken = laws.find(l => l.name === acc.law)
  if (!broken || evalC(broken.holds, acc.params, st, m) || !lastBefore || !lastReq) return false
  const witness = {...acc.params, ...lastBefore.scalars, ...lastReq}
  return exactKeys(acc.witness, Object.keys(witness)) && Object.entries(witness).every(([k, v]) => acc.witness[k] === v)
}

// --- Breakpoint extraction for affine trajectory Phi(j) = base + delta * j ------------------

type Aff = {c0: number, c1: number} // c0 + c1 * j

function flipPoint(op: '<=' | '<' | '=', a: Aff, b: Aff): number | undefined {
  const d0 = a.c0 - b.c0, d1 = a.c1 - b.c1
  if (d1 === 0) return undefined
  if (op === '<=') {
    // d0 + d1 * j <= 0
    if (d0 <= 0 && d1 > 0) {
      // true at 0, flips to false at first j where d0 + d1*j >= 1
      return Math.floor((-d0) / d1) + 1
    }
    if (d0 > 0 && d1 < 0) {
      // false at 0, flips to true at first j where d0 + d1*j <= 0
      return Math.ceil(d0 / (-d1))
    }
    return undefined
  }
  if (op === '<') {
    // d0 + 1 + d1 * j <= 0
    return flipPoint('<=', {c0: a.c0 + 1, c1: a.c1}, b)
  }
  // op === '='
  if (d0 === 0) return 1
  if ((d0 > 0 && d1 < 0) || (d0 < 0 && d1 > 0)) {
    const num = -d0
    if (num % d1 === 0) {
      const q = num / d1
      if (q > 0 && Number.isSafeInteger(q)) return q
    }
  }
  return undefined
}

function evalAtZero(op: '<=' | '<' | '=', a: Aff, b: Aff): boolean {
  return op === '<=' ? a.c0 <= b.c0 : op === '<' ? a.c0 < b.c0 : a.c0 === b.c0
}

function extractBreakpoints(
  m: Machine,
  laws: Law[],
  params: Record<string, number>,
  req: Record<string, number>,
  closedForm: Record<string, ClosedFormVar>,
): {guardBreaks: number[], lawBreaks: number[], maxNonNeg: number} {
  const flags = inlinePlainFlags(m)
  const guardBreaks = new Set<number>()
  const lawBreaks = new Set<number>()
  let maxNonNeg = MAX_REPEAT
  for (const cf of Object.values(closedForm)) {
    if (cf.delta < 0) {
      maxNonNeg = Math.min(maxNonNeg, Math.floor(cf.base / (-cf.delta)))
    }
  }

  const record = (target: Set<number>, j: number | undefined) => {
    if (j !== undefined && Number.isInteger(j) && j >= 1 && j <= MAX_REPEAT) target.add(j)
  }

  const evalAffE = (e: E, target: Set<number>): Aff | undefined => {
    switch (e.op) {
      case 'const': return {c0: e.value, c1: 0}
      case 'var': {
        if (Object.hasOwn(closedForm, e.name)) return {c0: closedForm[e.name]!.base, c1: closedForm[e.name]!.delta}
        if (Object.hasOwn(req, e.name)) return {c0: req[e.name]!, c1: 0}
        if (Object.hasOwn(params, e.name)) return {c0: params[e.name]!, c1: 0}
        return {c0: 0, c1: 0}
      }
      case 'add': {
        const a = evalAffE(e.a, target), b = evalAffE(e.b, target)
        return a && b ? {c0: a.c0 + b.c0, c1: a.c1 + b.c1} : undefined
      }
      case 'mul': {
        const a = evalAffE(e.a, target)
        return a ? {c0: e.k * a.c0, c1: e.k * a.c1} : undefined
      }
      case 'sub': {
        const a = evalAffE(e.a, target), b = evalAffE(e.b, target)
        if (!a || !b) return undefined
        record(target, flipPoint('<', a, b))
        return a.c0 >= b.c0 ? {c0: a.c0 - b.c0, c1: a.c1 - b.c1} : {c0: 0, c1: 0}
      }
      case 'min': case 'max': {
        const a = evalAffE(e.a, target), b = evalAffE(e.b, target)
        if (!a || !b) return undefined
        record(target, flipPoint('<=', a, b))
        const pickA = e.op === 'min' ? a.c0 <= b.c0 : a.c0 >= b.c0
        return pickA ? a : b
      }
      case 'if': {
        const t0 = evalAffC(e.c, target)
        if (t0 === undefined) return undefined
        return evalAffE(t0 ? e.then : e.else, target)
      }
      case 'get': {
        const arg = evalAffE(e.key, target)
        if (!arg) return undefined
        if (arg.c1 === 0 && isArithmetic(e.map)) {
          const d = Number(e.map.slice(e.map.indexOf('$') + 1))
          const val = e.map.startsWith('div$') ? Math.floor(arg.c0 / d) : arg.c0 % d
          return {c0: val, c1: 0}
        }
        return undefined
      }
      case 'prod': case 'proj': case 'tup': return undefined
    }
  }

  const evalAffC = (c: C, target: Set<number>): boolean | undefined => {
    switch (c.op) {
      case 'flag': return evalAffC(flags[c.name]!, target)
      case 'not': { const t = evalAffC(c.x, target); return t === undefined ? undefined : !t }
      case 'and': {
        let res: boolean | undefined = true
        for (const ch of c.xs) {
          const t = evalAffC(ch, target)
          if (t === false) res = false
          else if (t === undefined && res === true) res = undefined
        }
        return res
      }
      case 'or': {
        let res: boolean | undefined = false
        for (const ch of c.xs) {
          const t = evalAffC(ch, target)
          if (t === true) res = true
          else if (t === undefined && res === false) res = undefined
        }
        return res
      }
      case '<=': case '<': case '=': {
        const a = evalAffE(c.a, target), b = evalAffE(c.b, target)
        if (!a || !b) return undefined
        record(target, flipPoint(c.op, a, b))
        return evalAtZero(c.op, a, b)
      }
      case 'all': return undefined
    }
  }

  if (m.assume) evalAffC(m.assume, guardBreaks)
  for (const sv of Object.keys(m.state)) {
    const rhs = m.step.state?.[sv]
    if (rhs) evalAffE(rhs, guardBreaks)
  }
  for (const l of laws) evalAffC(l.holds, lawBreaks)

  return {
    guardBreaks: [...guardBreaks].sort((a, b) => a - b),
    lawBreaks: [...lawBreaks].sort((a, b) => a - b),
    maxNonNeg,
  }
}

// --- Candidate action & parameter enumeration (purely from AST + sampling) ------------------

function topConjuncts(c: C, out: C[] = []): C[] {
  if (c.op === 'and') { for (const x2 of c.xs) topConjuncts(x2, out); return out }
  out.push(c)
  return out
}

function candidateActions(
  m: Machine,
  params: Record<string, number>,
  st: State,
  it: ReturnType<typeof interpret>,
  rand: (k: number) => number,
  opts: AccelRefuteOptions,
): Record<string, number>[] {
  const bounds = new Map<string, number>()
  if (m.assume) {
    for (const c of topConjuncts(m.assume)) {
      if ((c.op === '<' || c.op === '<=') && c.a.op === 'var' && c.b.op === 'const' && m.inputs.includes(c.a.name)) {
        const hi = c.op === '<' ? c.b.value : c.b.value + 1
        bounds.set(c.a.name, Math.min(bounds.get(c.a.name) ?? Infinity, hi))
      }
    }
  }
  const finite = m.inputs.filter(i => (bounds.get(i) ?? Infinity) <= 16)
  const free = m.inputs.filter(i => !finite.includes(i))
  let combos: Record<string, number>[] = [{}]
  for (const inp of finite) {
    const hi = bounds.get(inp)!
    if (combos.length * hi > 128) break
    combos = combos.flatMap(ch => Array.from({length: hi}, (_, v) => ({...ch, [inp]: v})))
  }
  const raw: Record<string, number>[] = []
  // For each finite combination, try free inputs at 0, and also one variant with non-$neg free inputs at 1.
  for (const ch of combos) {
    const z: Record<string, number> = {...ch}
    for (const inp of m.inputs) if (!(inp in z)) z[inp] = 0
    raw.push(z)
  }
  if (free.length && combos.length <= 32) {
    for (const ch of combos) {
      const one: Record<string, number> = {...ch}
      for (const inp of m.inputs) if (!(inp in one)) one[inp] = inp.endsWith('$neg') ? 0 : 1
      raw.push(one)
    }
  }
  // Also add random allowed inputs to cover unbounded numeric guards (e.g. clocks or thresholds).
  if (opts.randomInput) {
    for (let t = 0; t < 24; t++) {
      const rInp = opts.randomInput(rand, t < 12 ? 4 : 32, params)
      raw.push(numbersOf(rInp))
    }
  }
  // Filter to allowed actions and deduplicate by observed 2-step state effect, preferring actions
  // with smaller inputs / fewer arithmetic function calls on the active step branch.
  const out: Record<string, number>[] = []
  const byEffect = new Map<string, {req: Record<string, number>, cost: number}>()
  const stateKeys = Object.keys(m.state)
  const sig = (s: State) => stateKeys.map(k2 => s.scalars[k2] ?? 0).join(',')
  const flags = inlinePlainFlags(m), emptyPath: Path = new Map()
  const activeFnCost = (req: Record<string, number>): number => {
    if (!m.facts?.length) return 0
    const vars: Record<string, E> = Object.create(null)
    for (const p of m.params) vars[p] = n(params[p] ?? 0)
    for (const inp of m.inputs) vars[inp] = n(req[inp] ?? 0)
    for (const sv of stateKeys) vars[sv] = n(st.scalars[sv] ?? 0)
    const fl: Record<string, C> = Object.create(null)
    for (const [fn, fc] of Object.entries(flags)) fl[fn] = substC(fc, {vars, maps: {}, flags: {}})
    const sub = {vars, maps: {}, flags: fl}
    let cost = 0
    const countE = (e: E) => {
      switch (e.op) {
        case 'var': case 'const': return
        case 'mul': countE(e.a); return
        case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup': countE(e.a); countE(e.b); return
        case 'proj': countE(e.a); return
        case 'get': countE(e.key); if (isArithmetic(e.map)) cost++; return
        case 'if': { const t = truth(e.c, emptyPath); if (t !== false) countE(e.then); if (t !== true) countE(e.else); return }
      }
    }
    for (const rhs of Object.values(m.step.state ?? {})) countE(substE(rhs, sub))
    return cost
  }
  for (const req of raw) {
    try {
      if (!allowed(m, it, params, st, req)) continue
      const s1 = it.step(params, st, req)
      const s1Sig = sig(s1)
      let s2Sig = 'blocked'
      if (allowed(m, it, params, s1, req)) {
        const s2 = it.step(params, s1, req)
        s2Sig = sig(s2)
      }
      const effectKey = `${s1Sig}|${s2Sig}`
      const cost = activeFnCost(req) * 1000 + Object.values(req).reduce((a, b) => a + b, 0)
      const prev = byEffect.get(effectKey)
      if (!prev || cost < prev.cost) byEffect.set(effectKey, {req, cost})
    } catch { /* skip inadmissible */ }
  }
  for (const entry of byEffect.values()) out.push(entry.req)
  return out
}

function candidateParams(
  m: Machine,
  rand: (k: number) => number,
  opts: AccelRefuteOptions,
): Record<string, number>[] {
  if (!m.params.length) return [{}]
  const raw: Record<string, number>[] = []
  raw.push(Object.fromEntries(m.params.map(p => [p, 0])))
  raw.push(Object.fromEntries(m.params.map(p => [p, p.endsWith('$neg') ? 0 : 1])))
  if (opts.randomParams) {
    for (let t = 0; t < 16; t++) raw.push(opts.randomParams(rand, t < 8 ? 4 : 64))
  }
  const seen = new Set<string>(), out: Record<string, number>[] = []
  for (const p of raw) {
    const kStr = m.params.map(nm => p[nm] ?? 0).join(',')
    if (seen.has(kStr)) continue
    seen.add(kStr)
    if (!m.pre || evalC(m.pre, p, {scalars: {}, maps: {}}, m)) out.push(p)
  }
  return out
}

function fitAffine(m: Machine, params: Record<string, number>, st0: State, req: Record<string, number>, it: ReturnType<typeof interpret>): Record<string, ClosedFormVar> | undefined {
  const states: State[] = [st0]
  let cur = st0
  for (let i = 0; i < 4; i++) {
    if (!allowed(m, it, params, cur, req)) return undefined
    try { cur = it.step(params, cur, req) } catch { return undefined }
    states.push(cur)
  }
  const cf: Record<string, ClosedFormVar> = {}
  let moving = false
  for (const sv of Object.keys(m.state)) {
    const v0 = states[0]!.scalars[sv] ?? 0
    const d = (states[1]!.scalars[sv] ?? 0) - v0
    for (let i = 2; i < states.length; i++) {
      if ((states[i]!.scalars[sv] ?? 0) !== v0 + i * d) return undefined
    }
    if (d !== 0) moving = true
    cf[sv] = {base: v0, delta: d}
  }
  return moving ? cf : undefined
}

function certifyRepeat(
  m: Machine,
  params: Record<string, number>,
  req: Record<string, number>,
  count: number,
  closedForm: Record<string, ClosedFormVar>,
  jVar: string,
  until: number,
  opts: AccelRefuteOptions,
): AcceleratedRepeatSegment | undefined {
  if (!Number.isInteger(count) || count < 2 || count > MAX_REPEAT) return undefined
  const startState: Record<string, number> = {}
  const endState: Record<string, number> = {}
  for (const sv of Object.keys(m.state)) {
    const cf = closedForm[sv]!
    const endVal = cf.base + cf.delta * count
    const prevVal = cf.base + cf.delta * (count - 1)
    if (!Number.isSafeInteger(endVal) || endVal < 0 || !Number.isSafeInteger(prevVal) || prevVal < 0) return undefined
    startState[sv] = cf.base
    endState[sv] = endVal
  }
  const {allowGoal, stepGoal} = buildRepeatGoals(m, params, req, count, closedForm, jVar)
  const budgetMs = Math.min(400, Math.max(0, until - clock()))
  if (budgetMs <= 0) return undefined
  const allowRes = grow(allowGoal, new Map(), {nodes: 0, until: clock() + budgetMs})
  if (!('tree' in allowRes) || !check(allowGoal, allowRes.tree)) return undefined
  const stepBudget = Math.min(600, Math.max(0, until - clock()))
  if (stepBudget <= 0) return undefined
  const stepRes = grow(stepGoal, new Map(), {nodes: 0, until: clock() + stepBudget})
  if (!('tree' in stepRes) || !check(stepGoal, stepRes.tree)) return undefined
  return {
    kind: 'repeat',
    request: req,
    ...(opts.shownRequest ? {shown: opts.shownRequest(req)} : {}),
    count,
    startState,
    endState,
    closedForm,
    jVar,
    allowGoal,
    allowTree: allowRes.tree,
    stepGoal,
    stepTree: stepRes.tree,
    checked: true,
  }
}

export function findAcceleratedRefutation(
  m: Machine,
  laws: Law[],
  opts: AccelRefuteOptions,
): AcceleratedRun | undefined {
  if (!accelRefuteFits(m, laws)) return undefined
  const until = clock() + opts.ms
  const wallEnd = opts.wall ?? Infinity
  const past = () => { checkWatchdog('accelerated refutation'); return clock() >= until || performance.now() >= wallEnd }
  const it = interpret(m), rand = seeded(37)
  const jVar = freshVar('accel$j', m)
  const paramList = candidateParams(m, rand, opts)

  type Node = {
    params: Record<string, number>
    st: State
    segments: AcceleratedSegment[]
    totalSteps: number
    hasRepeat: boolean
    depth: number
  }

  const finalize = (
    params: Record<string, number>,
    segments: AcceleratedSegment[],
    totalSteps: number,
    broken: Law,
    finalSt: State,
    beforeSt: State,
    lastReq: Record<string, number>,
  ): AcceleratedRun | undefined => {
    const acc: AcceleratedRun = {
      checked: true,
      params,
      ...(opts.shownParams ? {shownParams: opts.shownParams(params)} : {}),
      segments,
      totalSteps,
      law: broken.name,
      finalState: {...finalSt.scalars},
      witness: {...params, ...beforeSt.scalars, ...lastReq},
    }
    return checkAcceleratedRun(m, laws, acc) ? acc : undefined
  }

  for (const params of paramList) {
    if (past()) break
    let initSt: State
    try { initSt = it.init(params) } catch { continue }
    if (laws.some(l => !evalC(l.holds, params, initSt, m))) continue // 0-step break handled by concrete runs

    const queue: Node[] = [{params, st: initSt, segments: [], totalSteps: 0, hasRepeat: false, depth: 0}]
    const visited = new Set<string>([JSON.stringify(initSt.scalars)])

    while (queue.length && !past()) {
      const node = queue.shift()!
      const actions = candidateActions(m, params, node.st, it, rand, opts)

      // 1. If we already took at least one accelerated segment, check 1-step concrete suffix breaks first!
      if (node.hasRepeat) {
        for (const req of actions) {
          if (past()) break
          try {
            if (!allowed(m, it, params, node.st, req)) continue
            const next = it.step(params, node.st, req)
            const broken = laws.find(l => !evalC(l.holds, params, next, m))
            if (broken) {
              const stepSeg: AcceleratedStepSegment = {kind: 'step', request: req, ...(opts.shownRequest ? {shown: opts.shownRequest(req)} : {})}
              const done = finalize(params, [...node.segments, stepSeg], node.totalSteps + 1, broken, next, node.st, req)
              if (done) {
                log(`FOUND checked accelerated refutation: law="${broken.name}", totalSteps=${done.totalSteps}, segments=${done.segments.length}`)
                return done
              }
            }
          } catch { /* skip */ }
        }
      }

      if (node.depth >= 2) continue

      // 2. Try accelerating each affine-moving action from node.st!
      for (const req of actions) {
        if (past()) break
        const cf = fitAffine(m, params, node.st, req, it)
        if (!cf) continue
        const {guardBreaks, lawBreaks, maxNonNeg} = extractBreakpoints(m, laws, params, req, cf)
        const minGuard = guardBreaks.length ? Math.min(guardBreaks[0]!, maxNonNeg) : maxNonNeg
        const kCandidates: number[] = []
        // Law-breaking count inside the linear regime first (direct violation, 0 suffix steps needed!).
        for (const jb of lawBreaks) {
          if (jb >= 2 && jb <= minGuard && !kCandidates.includes(jb)) kCandidates.push(jb)
        }
        // Guard-crossing thresholds (to reach wraparound / mode switches / saturation boundaries!).
        if (minGuard >= 2 && minGuard < MAX_REPEAT) {
          if (!kCandidates.includes(minGuard)) kCandidates.push(minGuard)
          if (minGuard - 1 >= 2 && !kCandidates.includes(minGuard - 1)) kCandidates.push(minGuard - 1)
        }
        for (const count of kCandidates.slice(0, 3)) {
          if (past()) break
          // Fast-path pre-check before certifying in kernel: compute endState Phi(count) and check
          // whether Phi(count) itself or 1-2 concrete steps from Phi(count) break a law (or reach a new mode)!
          const endScalars: Record<string, number> = {}
          let validEnd = true
          for (const sv of Object.keys(m.state)) {
            const c = cf[sv]!, v = c.base + c.delta * count
            if (!Number.isSafeInteger(v) || v < 0) { validEnd = false; break }
            endScalars[sv] = v
          }
          if (!validEnd) continue
          const endSt: State = {scalars: endScalars, maps: {}}

          // Case A: Phi(count) directly breaks a law!
          const directBroken = laws.find(l => !evalC(l.holds, params, endSt, m))
          if (directBroken) {
            const repSeg = certifyRepeat(m, params, req, count, cf, jVar, until, opts)
            if (repSeg) {
              const prevScalars = Object.fromEntries(Object.keys(m.state).map(sv => [sv, cf[sv]!.base + cf[sv]!.delta * (count - 1)]))
              const done = finalize(params, [...node.segments, repSeg], node.totalSteps + count, directBroken, endSt, {scalars: prevScalars, maps: {}}, req)
              if (done) {
                log(`FOUND direct accelerated refutation: law="${directBroken.name}", k=${count}`)
                return done
              }
            }
          }

          // Case B: Taking the SAME action `req` (or any other allowed action) concretely from Phi(count) crosses the threshold & breaks a law!
          const suffixActions = [req, ...actions.filter(a => a !== req)]
          let repSeg: AcceleratedRepeatSegment | undefined
          for (const sReq of suffixActions) {
            if (past()) break
            try {
              if (!allowed(m, it, params, endSt, sReq)) continue
              const after = it.step(params, endSt, sReq)
              const broken = laws.find(l => !evalC(l.holds, params, after, m))
              if (broken) {
                repSeg ??= certifyRepeat(m, params, req, count, cf, jVar, until, opts)
                if (!repSeg) break
                const stepSeg: AcceleratedStepSegment = {kind: 'step', request: sReq, ...(opts.shownRequest ? {shown: opts.shownRequest(sReq)} : {})}
                const done = finalize(params, [...node.segments, repSeg, stepSeg], node.totalSteps + count + 1, broken, after, endSt, sReq)
                if (done) {
                  log(`FOUND threshold-crossing accelerated refutation: law="${broken.name}", repeat=${count} + 1 step = ${done.totalSteps}`)
                  return done
                }
              } else if (node.depth === 0 && sReq === req) {
                // Enqueue the post-threshold state for a second wave (multi-phase deep bugs!).
                const afterKey = JSON.stringify(after.scalars)
                if (!visited.has(afterKey) && queue.length < 16) {
                  repSeg ??= certifyRepeat(m, params, req, count, cf, jVar, until, opts)
                  if (repSeg) {
                    visited.add(afterKey)
                    const stepSeg: AcceleratedStepSegment = {kind: 'step', request: sReq, ...(opts.shownRequest ? {shown: opts.shownRequest(sReq)} : {})}
                    queue.push({params, st: after, segments: [...node.segments, repSeg, stepSeg], totalSteps: node.totalSteps + count + 1, hasRepeat: true, depth: node.depth + 1})
                  }
                }
              }
            } catch { /* skip */ }
          }
        }
      }

      // 3. Also explore 1-step concrete prefixes from init (e.g. initialize/open a mode before accelerating!).
      if (node.depth === 0 && !node.hasRepeat) {
        for (const req of actions.slice(0, 8)) {
          if (past()) break
          try {
            if (!allowed(m, it, params, node.st, req)) continue
            const next = it.step(params, node.st, req)
            const kStr = JSON.stringify(next.scalars)
            if (visited.has(kStr) || queue.length >= 16) continue
            visited.add(kStr)
            const stepSeg: AcceleratedStepSegment = {kind: 'step', request: req, ...(opts.shownRequest ? {shown: opts.shownRequest(req)} : {})}
            queue.push({params, st: next, segments: [...node.segments, stepSeg], totalSteps: node.totalSteps + 1, hasRepeat: false, depth: node.depth + 1})
          } catch { /* skip */ }
        }
      }
    }
  }
  return undefined
}

export function formatAcceleratedSummary(acc: AcceleratedRun): string {
  const parts = acc.segments.map(s => {
    const req = JSON.stringify(s.shown ?? s.request)
    return s.kind === 'repeat' ? `repeat(${req}, ${s.count})` : `step(${req})`
  })
  return `k = ${acc.totalSteps} [${parts.join(' ; ')}]`
}
