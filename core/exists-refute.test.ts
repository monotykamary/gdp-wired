// Independent compiled-rule refutation oracle and fail-visible existential watch tests.
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, type Request, type State, carriedView, compileC, compileE, cpair, cunpair, fastStep, interpret, numbersOf, walk} from './machine.ts'
import {type Rule, all, bool, exists, fn, forall, nat, oneOf, proveRule, rule, sizedSort, when, yes} from './dsl.ts'
import {someHolds} from './exists.ts'
import {WatchUndecided, watch, watchUndecided} from './watch.ts'

type Env = Record<string, number>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = Rule<any, any, any, any, any, any, any, any>

function namesInNode(node: E | C): Set<string> {
  const out = new Set<string>()
  walk(node, o => { if (o.op === 'var' && typeof o.name === 'string') out.add(o.name) })
  return out
}

const flattenOr = (c: C): C[] => (c.op === 'or' ? c.xs.flatMap(flattenOr) : [c])
const flattenAnd = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(flattenAnd) : [c])

function evalFiniteBounds(disjunct: C, boundVars: string[], baseEnv: Env, view: State, m: Machine): [string, number, number][] | undefined {
  const bset = new Set(boundVars)
  const hi = new Map<string, number>(), lo = new Map<string, number>()
  const evalBound = (e: E): number | undefined => {
    for (const n of namesInNode(e)) if (bset.has(n)) return undefined
    try { return compileE(e, m)(baseEnv, view) } catch { return undefined }
  }
  for (const c of flattenAnd(disjunct)) {
    if (c.op === '<' && c.a.op === 'var' && bset.has(c.a.name)) {
      const v = evalBound(c.b)
      if (v !== undefined) hi.set(c.a.name, Math.min(hi.get(c.a.name) ?? Infinity, v - 1))
    } else if (c.op === '<=' && c.a.op === 'var' && bset.has(c.a.name)) {
      const v = evalBound(c.b)
      if (v !== undefined) hi.set(c.a.name, Math.min(hi.get(c.a.name) ?? Infinity, v))
    } else if (c.op === '=') {
      if (c.a.op === 'var' && bset.has(c.a.name)) {
        const v = evalBound(c.b)
        if (v !== undefined) { lo.set(c.a.name, Math.max(lo.get(c.a.name) ?? 0, v)); hi.set(c.a.name, Math.min(hi.get(c.a.name) ?? Infinity, v)) }
      } else if (c.b.op === 'var' && bset.has(c.b.name)) {
        const v = evalBound(c.a)
        if (v !== undefined) { lo.set(c.b.name, Math.max(lo.get(c.b.name) ?? 0, v)); hi.set(c.b.name, Math.min(hi.get(c.b.name) ?? Infinity, v)) }
      }
    }
  }
  const ranges: [string, number, number][] = []
  for (const v of boundVars) {
    if (!hi.has(v)) return undefined
    ranges.push([v, lo.get(v) ?? 0, hi.get(v)!])
  }
  return ranges
}

function disjunctStatus(disjunct: C, someVars: string[], baseEnv: Env, view: State, m: Machine): 'holds' | 'false' | 'undecided' {
  const used = namesInNode(disjunct)
  const vars = someVars.filter(v => used.has(v))
  const checkFn = compileC(disjunct, m)
  if (vars.length === 0) return checkFn(baseEnv, view) ? 'holds' : 'false'
  const ranges = evalFiniteBounds(disjunct, vars, baseEnv, view, m)
  if (!ranges) return 'undecided'
  let total = 1
  for (const [, a, b] of ranges) {
    if (b < a) return 'false'
    total *= (b - a + 1)
    if (total > 2_000_000) return 'undecided'
  }
  const env: Env = {...baseEnv}
  const go = (i: number): boolean => {
    if (i === ranges.length) return checkFn(env, view)
    const [name, a, b] = ranges[i]!
    for (let x = a; x <= b; x++) { env[name] = x; if (go(i + 1)) return true }
    return false
  }
  return go(0) ? 'holds' : 'false'
}

function candidateKeys(params: Env, st: State): number[] {
  const maxParam = Math.max(4, ...Object.values(params))
  const ks = new Set<number>()
  for (let i = 0; i <= maxParam + 1; i++) ks.add(i)
  for (const val of Object.values(st.scalars)) if (Number.isSafeInteger(val) && val >= 0) ks.add(val)
  const addKey = (k: number, depth: number) => {
    ks.add(k)
    if (depth > 0 && k > 0) { const [a, b] = cunpair(k); addKey(a, depth - 1); addKey(b, depth - 1) }
  }
  for (const cells of Object.values(st.maps)) for (const k of cells.keys()) addKey(k, 3)
  return [...ks].sort((a, b) => a - b)
}

function forallDoms(law: Law, keys: string[], params: Env, st: State, view: State, m: Machine): number[][] {
  const neg = flattenOr(law.holds).find(d => d.op === 'not')
  const kset = new Set(keys), hi = new Map<string, number>()
  if (neg && neg.op === 'not') {
    for (const c of flattenAnd(neg.x)) {
      if ((c.op === '<' || c.op === '<=') && c.a.op === 'var' && kset.has(c.a.name)) {
        if (![...namesInNode(c.b)].some(u => kset.has(u))) {
          try {
            const v = compileE(c.b, m)({...params, ...st.scalars}, view)
            hi.set(c.a.name, Math.min(hi.get(c.a.name) ?? Infinity, c.op === '<' ? v - 1 : v))
          } catch { /* fallback */ }
        }
      }
    }
  }
  const fallback = candidateKeys(params, st)
  return keys.map(k => (hi.has(k) ? Array.from({length: Math.max(0, hi.get(k)! + 1)}, (_, i) => i) : fallback))
}

function compiledLawViolated(m: Machine, law: Law, params: Env, st: State): {violated: boolean, cex?: Env} {
  const emptyCarried: Request = Object.fromEntries((m.inputMaps ?? []).map(c => [c, new Map()]))
  const view = carriedView(m, st, emptyCarried, undefined, params)
  const keys = law.forall ? [law.forall, ...(law.keys ?? [])] : []
  const doms = forallDoms(law, keys, params, st, view, m)
  const env: Env = {...params, ...st.scalars}
  const plainCheck = !law.some?.length ? compileC(law.holds, m) : undefined
  const disjuncts = law.some?.length ? flattenOr(law.holds) : undefined
  const go = (i: number): Env | undefined => {
    if (i === keys.length) {
      if (!law.some?.length) return !plainCheck!(env, view) ? {...env} : undefined
      let anyUndecided = false
      for (const d of disjuncts!) {
        const s = disjunctStatus(d, law.some, env, view, m)
        if (s === 'holds') return undefined
        if (s === 'undecided') anyUndecided = true
      }
      return anyUndecided ? undefined : {...env}
    }
    const name = keys[i]!
    for (const v of doms[i]!) { env[name] = v; const hit = go(i + 1); if (hit) return hit }
    return undefined
  }
  const cex = go(0)
  return cex ? {violated: true, cex} : {violated: false}
}

// Re-runs a candidate refutation trace on rule.compiled() (with interpret fallback only when compileJs explicitly
// refuses tuple-each/all) and checks laws using compileC + exact finite existential domains, completely independent
// of someHolds, watch, and replayRefutation.
export function verifyRefutationCompiled(r: AnyRule, laws: Law[], params: Env, trace: Record<string, unknown>[]): {confirmed: boolean, step?: number, law?: string, reason?: string, stepEngine: string} {
  const m = r.machine
  if (m.pre && !compileC(m.pre, m)(params, {scalars: {}, maps: {}})) return {confirmed: false, reason: 'pre failed', stepEngine: 'none'}
  const hasCounts = !!Object.keys(m.counts ?? {}).length
  let stepEngine = 'compiled'
  let initFn: (p: Env) => State, stepFn: (p: Env, s: State, req: Request) => State
  if (!hasCounts) {
    try {
      const gen = r.compiled()
      initFn = p => gen.init(p)
      stepFn = (p, s, req) => gen.step(p, s, req)
    } catch (e) {
      if (!String((e as Error).message).includes('compileJs takes no tuple key at every key')) {
        return {confirmed: false, reason: String((e as Error).message), stepEngine: 'error'}
      }
      stepEngine = 'interpret-tuple-fallback'
      const it = interpret(m)
      initFn = p => it.init(p)
      stepFn = (p, s, req) => {
        if (m.assume) {
          const env: Env = {...p, ...numbersOf(req), ...it.queries(p, s, req)}, seen = carriedView(m, s, req, undefined, p)
          for (const [fnName, fc] of Object.entries(m.step.flags ?? {})) env[`?${fnName}`] = compileC(fc, m)(env, seen) ? 1 : 0
          if (!compileC(m.assume, m)(env, seen)) throw new RangeError('assume failed')
        }
        return it.step(p, s, req)
      }
    }
  } else {
    const fs = fastStep(m), it = interpret(m)
    initFn = p => it.init(p)
    stepEngine = fs ? 'fastStep-compiled' : 'interpret-counts-fallback'
    stepFn = fs ? (p, s, req) => fs(p, s, req) : (p, s, req) => it.step(p, s, req)
  }
  let st = initFn(params)
  for (const law of laws) if (compiledLawViolated(m, law, params, st).violated) return {confirmed: true, step: 0, law: law.name, stepEngine}
  for (let i = 0; i < trace.length; i++) {
    const raw = trace[i]!
    const req: Request = Object.fromEntries(Object.entries(raw).map(([k, val]) => [
      k, typeof val === 'number' ? val : val instanceof Map ? val : new Map(Object.entries(val as Record<string, number>).map(([a, b]) => [Number(a), Number(b)])),
    ]))
    try { st = stepFn(params, st, req) } catch (e) { return {confirmed: false, reason: `step ${i} refused: ${(e as Error).message}`, stepEngine} }
    for (const law of laws) if (compiledLawViolated(m, law, params, st).violated) return {confirmed: true, step: i + 1, law: law.name, stepEngine}
  }
  return {confirmed: false, reason: 'no law violated on compiled replay', stepEngine}
}

const makeMiniClientServer = (broken: boolean) => rule('mini client server')
  .params({nodes: nat, reqs: nat, resps: nat})
  .sorts('Node', 'Req', 'Resp')
  .relations({Match: ['Req', 'Resp'], RequestSent: ['Node', 'Req'], ResponseSent: ['Node', 'Resp'], ResponseReceived: ['Node', 'Resp']})
  .inputs({op: oneOf('match', 'start', 'req', 'resp', 'recv'), n: nat, r: nat, p: nat})
  .assume(({n, r, p, nodes, reqs, resps}) => all(sizedSort('Node', nodes).has(n), sizedSort('Req', reqs).has(r), sizedSort('Resp', resps).has(p)))
  .state({started: 0})
  .flags(({op, n, r, p, started, RequestSent, ResponseSent, Match}) => ({
    matches: op.is('match').and(started.eq(0)),
    starts: op.is('start').and(started.eq(0)),
    sendsReq: op.is('req').and(started.eq(1)),
    sendsResp: op.is('resp').and(started.eq(1), RequestSent.has(n, r), broken ? yes : Match.has(r, p)),
    recvs: op.is('recv').and(started.eq(1), ResponseSent.has(n, p)),
  }))
  .step(({n, r, p, started, matches, starts, sendsReq, sendsResp, recvs, Match, RequestSent, ResponseSent, ResponseReceived}) => ({
    started: when(starts, 1, started),
    Match: Match.add([r, p], matches),
    RequestSent: RequestSent.add([n, r], sendsReq),
    ResponseSent: ResponseSent.add([n, p], sendsResp),
    ResponseReceived: ResponseReceived.add([n, p], recvs),
  }))

const miniCsLaw = (r: ReturnType<typeof makeMiniClientServer>) => r.law('matched response', ({nodes, reqs, resps, RequestSent, Match, ResponseReceived}) =>
  forall((n, p) => all(sizedSort('Node', nodes).has(n), sizedSort('Resp', resps).has(p), ResponseReceived.has(n, p)).implies(
    exists(x => sizedSort('Req', reqs).has(x).and(RequestSent.has(n, x), Match.has(x, p))))))

test('compiled oracle confirms genuine tuple-existential refutation and rejects bogus or intact traces', () => {
  const broken = makeMiniClientServer(true), lawB = miniCsLaw(broken)
  const params = {nodes: 2, reqs: 2, resps: 2}
  const goodTrace = [
    {op: 1, n: 0, r: 0, p: 0}, // start
    {op: 2, n: 0, r: 0, p: 0}, // req(0, 0)
    {op: 3, n: 0, r: 0, p: 0}, // resp(0, 0, 0) without Match(0, 0)
    {op: 4, n: 0, r: 0, p: 0}, // recv(0, 0) -> ResponseReceived(0, 0) without Match
  ]
  const ok = verifyRefutationCompiled(broken, [lawB], params, goodTrace)
  expect(ok.confirmed).toBe(true)
  expect(ok.stepEngine).toBe('compiled')
  expect(ok.step).toBe(4)

  // Intact rule: same trace produces no ResponseSent / ResponseReceived, so oracle rejects it.
  const intact = makeMiniClientServer(false), lawI = miniCsLaw(intact)
  expect(verifyRefutationCompiled(intact, [lawI], params, goodTrace).confirmed).toBe(false)

  // Out-of-sort input fails assume on compiled().step, so oracle rejects it.
  const badInput = [{op: 1, n: 9, r: 0, p: 0}]
  expect(verifyRefutationCompiled(broken, [lawB], params, badInput).confirmed).toBe(false)
})

test('watch fails visibly with WatchUndecided instead of silently coercing unevaluable someHolds to true', () => {
  // Unbounded multi-variable existential is unevaluable by someHolds (returns undefined).
  const r = rule('unbounded multi exists').inputs({v: nat}).state({x: 6}).step(({v, x}) => ({x: when(v.eq(1), x.plus(1), x)}))
  const law = r.law('impossible unbounded pair', ({x}) => exists(a => exists(b => a.gt(b).and(b.gt(a), a.gt(x)))))
  const m = r.machine, it = interpret(m), st = it.init({})
  const before = watchUndecided.n
  expect(() => watch(m, it, law, {}, 4).start(st)).toThrow(WatchUndecided)
  expect(watchUndecided.n).toBe(before + 1)

  // proveRule does not falsely refute on an unevaluable existential law (stays unproven/no run).
  const v = proveRule(r, [law], {search: false})
  expect(v.proven).toBe(false)
  expect(v.run).toBeUndefined()
  void bool
})

test('someHolds: exact on tuple-key, multi-var disjoint branches, unbounded tuple keys, non-zero defaults, and fn safety', () => {
  // 1. Tuple-key 1-var bounded existential (client_server_ae shape).
  const cs = makeMiniClientServer(true), csLaw = miniCsLaw(cs), cm = cs.machine
  const stHit: State = {
    scalars: {started: 1},
    maps: {
      Match: new Map([[cpair(3, 1), 1]]),
      RequestSent: new Map([[cpair(0, 3), 1]]),
      ResponseSent: new Map([[cpair(0, 1), 1]]),
      ResponseReceived: new Map([[cpair(0, 1), 1]]),
    },
  }
  const stMiss: State = {
    scalars: {started: 1},
    maps: {
      Match: new Map([[cpair(2, 1), 1]]),
      RequestSent: new Map([[cpair(0, 3), 1]]),
      ResponseSent: new Map([[cpair(0, 1), 1]]),
      ResponseReceived: new Map([[cpair(0, 1), 1]]),
    },
  }
  const fk0 = csLaw.forall!, fk1 = csLaw.keys![0]!
  expect(someHolds(csLaw.holds, csLaw.some!, {nodes: 4, reqs: 5, resps: 4, [fk0]: 0, [fk1]: 1}, stHit, cm, true)).toMatchObject({holds: true, witness: {[csLaw.some![0]!]: 3}})
  expect(someHolds(csLaw.holds, csLaw.some!, {nodes: 4, reqs: 5, resps: 4, [fk0]: 0, [fk1]: 1}, stMiss, cm, true)).toEqual({holds: false})

  // 2. Multi-var disjoint-branch nested tuple existential (sharded_kv_no_lost_keys shape).
  const kv = rule('mini kv')
    .params({nodes: nat, keys: nat, values: nat})
    .sorts('Node', 'Key', 'Value')
    .state({started: 0})
    .relations({Owner: ['Key', 'Node'], TransferMsg: ['Node', 'Key', 'Value']})
  const kvLaw = kv.law('no lost', ({nodes, keys, values, started, Owner, TransferMsg}) =>
    forall(k => k.lt(keys).and(started.eq(1)).implies(
      exists(x => x.lt(nodes).and(Owner.has(k, x))).or(
        exists(n => exists(j => exists(val => all(n.lt(nodes), j.lt(keys), val.lt(values), TransferMsg.has(n, j, val)))))))))
  const km = kv.machine, kKey = kvLaw.forall!
  const stEmpty: State = {scalars: {started: 1}, maps: {Owner: new Map(), TransferMsg: new Map()}}
  const stOwned: State = {scalars: {started: 1}, maps: {Owner: new Map([[cpair(1, 2), 1]]), TransferMsg: new Map()}}
  const stXfer: State = {scalars: {started: 1}, maps: {Owner: new Map(), TransferMsg: new Map([[cpair(2, cpair(0, 1)), 1]])}}
  expect(someHolds(kvLaw.holds, kvLaw.some!, {nodes: 3, keys: 2, values: 2, [kKey]: 1}, stEmpty, km, true)).toEqual({holds: false})
  expect(someHolds(kvLaw.holds, kvLaw.some!, {nodes: 3, keys: 2, values: 2, [kKey]: 1}, stOwned, km, true)?.holds).toBe(true)
  expect(someHolds(kvLaw.holds, kvLaw.some!, {nodes: 3, keys: 2, values: 2, [kKey]: 1}, stXfer, km, true)?.holds).toBe(true)

  // 3. Unbounded 1-var tuple key existential (piecewise-constant via cunpair) + non-zero default safety.
  const rm = rule('rel default').sorts('A', 'B').maps({M: 1}).relations({R: ['A', 'B']}).machine
  const tupRead = (mp: string, a: E, b: E): E => ({op: 'get', map: mp, key: {op: 'tup', a, b}})
  const unbTrue: C = {op: '=', a: tupRead('R', {op: 'const', value: 7}, {op: 'var', name: 'w'}), b: {op: 'const', value: 5}}
  expect(someHolds(unbTrue, ['w'], {}, {scalars: {}, maps: {M: new Map(), R: new Map([[cpair(7, 42), 5]])}}, rm)).toMatchObject({holds: true, witness: {w: 42}})
  expect(someHolds(unbTrue, ['w'], {}, {scalars: {}, maps: {M: new Map(), R: new Map([[cpair(7, 42), 4]])}}, rm)).toEqual({holds: false})
  // Non-zero default (M defaults to 1): ∃w. M[w] >= 1 holds even with empty stored cells!
  const nonZeroDef: C = {op: '<=', a: {op: 'const', value: 1}, b: {op: 'get', map: 'M', key: {op: 'var', name: 'w'}}}
  expect(someHolds(nonZeroDef, ['w'], {}, {scalars: {}, maps: {M: new Map(), R: new Map()}}, rm)?.holds).toBe(true)

  // 4. Uninterpreted fn map is NOT treated as piecewise-constant stored map (must NOT falsely return holds: false).
  const f = fn(1, (x: number) => (x === 999 ? 1 : 0))
  const fm = rule('fn rule').fns({f}).state({z: 0}).machine
  const fnQuery: C = {op: '=', a: {op: 'get', map: 'f', key: {op: 'var', name: 'w'}}, b: {op: 'const', value: 1}}
  expect(someHolds(fnQuery, ['w'], {}, {scalars: {z: 0}, maps: {}}, fm)).toBeUndefined()
})

test('proveRule refutes broken tuple-existential rule (confirmed by compiled oracle) and proves intact control', () => {
  const broken = makeMiniClientServer(true), lawB = miniCsLaw(broken)
  const ref = proveRule(broken, [lawB], {search: {ms: 10_000}})
  expect(ref.proven).toBe(false)
  expect(ref.run).toBeDefined()
  const chk = verifyRefutationCompiled(broken, [lawB], ref.run!.params, ref.run!.trace)
  expect(chk.confirmed).toBe(true)
  expect(chk.stepEngine).toBe('compiled')

  const intact = makeMiniClientServer(false), lawI = miniCsLaw(intact)
  const ok = proveRule(intact, [lawI], {search: {ms: 15_000}})
  expect(ok.proven).toBe(true)
  expect(ok.checked).toBe(true)
  expect(ok.run).toBeUndefined()
}, 30_000)
