// A finite relative-CTI filter, never a proof. Unsupported evaluations are
// unknown; only an actual enabled step from a state satisfying the WHOLE
// current family may remove a non-caller. The checked prover sees survivors.
import {type C, type E, type Law, type Machine, type Request, type State, carriedView, compileC, compileE, fastStep, interpret, seeded, walk} from './machine.ts'
import {checkWall, WallExpired} from './wall.ts'
type Env = Record<string, number>
type Samples = {p: Env, sts: State[]}[]
type Truth = boolean | undefined
const variables = (t: unknown): Set<string> => { const out = new Set<string>(); walk(t, o => { if (o.op === 'var') out.add(o.name as string) }); return out }
const conjuncts = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(conjuncts) : [c]
// Universal binders need a complete finite cover, not merely 0..sampleSize.
// Guards provide finite upper bounds (including auxiliary half-count witnesses).
// Otherwise permit only direct finite-map reads and equality between binders:
// the explicit cells plus one distinct fresh key per binder cover every case.
export function finiteEvaluator(m: Machine): (law: Law, p: Env, st: State) => Truth {
  const plans = new WeakMap<Law, ReturnType<typeof plan>>()
  const cache = new WeakMap<State, {params: Env, view: State, values: Map<Law, Truth>}>()
  function plan(law: Law) {
    const keys = [...new Set([law.forall, ...law.keys ?? []].filter((k): k is string => !!k))]
    const guards = law.holds.op === 'or' ? law.holds.xs.flatMap(c => c.op === 'not' ? conjuncts(c.x) : []) : law.holds.op === 'not' ? conjuncts(law.holds.x) : []
    const gs = guards.map(c => ({vars: [...variables(c)], test: compileC(c, m)}))
    const cover = keys.map(key => {
      let safe = true
      const maps = new Set<string>()
      const expression = (e: E): void => {
        if (!variables(e).has(key)) return
        if (e.op === 'get' && e.key.op === 'var' && e.key.name === key && e.map in (m.maps ?? {})) { maps.add(e.map); return }
        safe = false
      }
      const condition = (c: C): void => {
        if (c.op === 'and' || c.op === 'or') c.xs.forEach(condition)
        else if (c.op === 'not') condition(c.x)
        else if (c.op === 'all' || c.op === 'flag') safe = false
        else if (!(c.op === '=' && c.a.op === 'var' && c.b.op === 'var' && keys.includes(c.a.name) && keys.includes(c.b.name))) { expression(c.a); expression(c.b) }
      }
      condition(law.holds)
      // Separate the target binder from its affine remainder, without turning
      // natural truncated subtraction into integer subtraction.
      const affine = (e: E): {k: number, rest: ReturnType<typeof compileE>} | undefined => {
        if (!variables(e).has(key)) return {k: 0, rest: compileE(e, m)}
        if (e.op === 'var') return {k: 1, rest: () => 0}
        if (e.op === 'mul') { const a = affine(e.a); return a && {k: e.k * a.k, rest: (p, s) => e.k * a.rest(p, s)} }
        if (e.op === 'add') { const a = affine(e.a), b = affine(e.b); return a && b && {k: a.k + b.k, rest: (p, s) => a.rest(p, s) + b.rest(p, s)} }
        return undefined
      }
      const upper = guards.flatMap(c => {
        if (c.op !== '<' && c.op !== '<=' && c.op !== '=') return []
        const a = affine(c.a), b = affine(c.b)
        if (!a || !b || a.k === b.k || (a.k < b.k && c.op !== '=')) return []
        return [{vars: [...variables(c)].filter(v => v !== key), test: (p: Env, s: State) => Math.floor((b.rest(p, s) - a.rest(p, s) - (c.op === '<' ? 1 : 0)) / (a.k - b.k))}]
      })
      return {key, safe, maps: [...maps], upper}
    })
    let nested = false; walk(law.holds, o => { if (o.op === 'all') nested = true })
    return {keys, cover, guards: gs, test: compileC(law.holds, m), supported: !nested && !law.some?.length && !keys.some(k => k in m.state || m.params.includes(k)) && ![...variables(law.holds)].some(k => m.inputs.includes(k) && !keys.includes(k))}
  }
  return (law, p, st) => {
    checkWall('finite law')
    let entry = cache.get(st)
    if (!entry || entry.params !== p) { entry = {params: p, view: carriedView(m, st, Object.fromEntries((m.inputMaps ?? []).map(k => [k, new Map()])), undefined, p), values: new Map()}; cache.set(st, entry) }
    if (entry.values.has(law)) return entry.values.get(law)
    let shape = plans.get(law); if (!shape) { shape = plan(law); plans.set(law, shape) }
    if (!shape.supported) return undefined
    const env: Env = {...p, ...st.scalars}, view = entry.view
    let visited = 0
    const go = (left: typeof shape.cover): Truth => {
      if ((visited++ & 255) === 0) checkWall('finite law bindings')
      if (visited > 1_000_000) return undefined
      if (!left.length) return shape.test(env, view)
      for (const g of shape.guards) if (g.vars.every(k => k in env) && !g.test(env, view)) return true
      const choices = left.map(c => {
        const bounds: number[] = []
        for (const f of c.upper) if (f.vars.every(k => k in env)) { const b = f.test(env, view); if (Number.isSafeInteger(b)) bounds.push(b) }
        return {c, bounds}
      }).sort((a, b) => Number(b.bounds.length > 0) - Number(a.bounds.length > 0))
      for (const {c, bounds} of choices) {
        let values: number[]
        if (bounds.length) { const hi = Math.min(...bounds); if (hi > 1_000_000) continue; values = Array.from({length: Math.max(0, hi + 1)}, (_, i) => i) }
        else if (c.safe) { const cells = new Set([0, ...shape!.keys.flatMap(k => k in env ? [env[k]!] : []), ...shape!.cover.flatMap(c => c.maps.flatMap(mp => [...st.maps[mp]?.keys() ?? []]))]); const hi = Math.max(...cells); for (let i = 1; i <= shape!.keys.length; i++) cells.add(hi + i); values = [...cells] }
        else continue
        const next = left.filter(other => other !== c)
        let unknown = false
        for (const value of values) { env[c.key] = value; const truth = go(next); delete env[c.key]; if (truth === false) return false; if (truth === undefined) unknown = true }
        return unknown ? undefined : true
      }
      return undefined
    }
    let truth: Truth
    try { truth = go(shape.cover) } catch (e) { if (e instanceof WallExpired) throw e; truth = undefined }
    entry.values.set(law, truth)
    return truth
  }
}
export type FiniteDrop = {round: number, law: Law, params: Env, pre: State, request: Request, post: State}
export const finiteDump: {onStart?: (value: {machine: Machine, caller: Law[], candidates: Law[]}) => void, onDrop?: (drop: FiniteDrop) => void} = {}
export type FiniteOptions = {randomStates?: number, requests?: number, seed?: number, onDrop?: (drop: FiniteDrop) => void, onRound?: (row: {round: number, alive: number, dropped: number, randomStates: number, steps: number}) => void}
export function finiteHoudini(source: Machine, m: Machine, caller: Law[], candidates: Law[], samples: Samples, options: FiniteOptions = {}): Law[] {
  finiteDump.onStart?.({machine: m, caller, candidates})
  const evaluate = finiteEvaluator(m), rng = seeded(options.seed ?? 17), run = interpret(source), step = fastStep(source) ?? run.step
  const base = samples.flatMap(({p, sts}) => sts.map(st => ({p, st})))
  if (!base.length) return candidates
  const scalars = Object.keys(source.state), maps = Object.keys(source.maps ?? {}), requested = options.randomStates ?? 2000
  const values = new Map(maps.map(mp => [mp, [...new Set([source.maps![mp]!, ...base.flatMap(({st}) => [...st.maps[mp]?.values() ?? []])])].sort((a, b) => a - b)]))
  const keyPools = new Map(maps.map(mp => [mp, [...new Set(base.flatMap(({st}) => [...st.maps[mp] ?? []].filter(([, v]) => v !== (st.defaults?.[mp] ?? source.maps![mp])).map(([k]) => k)))]]))
  const scalarValues = new Map(scalars.map(name => [name, [...new Set(base.map(({st}) => st.scalars[name]!))]]))
  const numericInputs = source.inputs.map(name => ({name, bound: Math.max(3, ...conjuncts(source.assume ?? {op: 'and', xs: []}).flatMap(c => (c.op === '<' || c.op === '<=') && c.a.op === 'var' && c.a.name === name && c.b.op === 'const' && c.b.value <= 8 ? [c.b.value + Number(c.op === '<=')] : []))}))
  const sameState = (a: State, b: State): boolean => a.history === b.history && a.last === b.last && scalars.every(k => a.scalars[k] === b.scalars[k]) && maps.every(mp => {
    const av = a.maps[mp], bv = b.maps[mp], ad = a.defaults?.[mp] ?? source.maps![mp]!, bd = b.defaults?.[mp] ?? source.maps![mp]!
    return ad === bd && (av === bv || ([...av ?? []].every(([k, v]) => v === (bv?.get(k) ?? bd)) && [...bv ?? []].every(([k, v]) => v === (av?.get(k) ?? ad))))
  })
  const protectedLaws = new Set(caller)
  let alive = [...candidates]
  for (let round = 0; ; round++) {
    const family = [...caller, ...alive], removed = new Set<Law>()
    let accepted = 0, steps = 0
    const lawful = (p: Env, st: State) => family.every(law => evaluate(law, p, st) === true)
    const visit = (p: Env, pre: State): boolean => {
      if (!lawful(p, pre)) return false
      const bound = Math.max(3, ...Object.values(p))
      for (let trial = 0; trial < (options.requests ?? 25); trial++) {
        checkWall('finite transitions')
        const request: Request = Object.fromEntries(numericInputs.map(({name, bound: b}) => [name, rng(b)]))
        for (const mp of source.inputMaps ?? []) request[mp] = new Map(Array.from({length: bound}, (_, i) => [i, 1] as [number, number]).filter(() => rng(2)))
        let post: State
        try { post = step(p, pre, request) } catch (e) { if (e instanceof WallExpired) throw e; continue }
        steps++
        // Laws are state-only. An enabled semantic no-op preserves the already
        // checked family, even if the interpreter allocated fresh map objects.
        if (sameState(pre, post)) continue
        for (const law of alive) if (!protectedLaws.has(law) && !removed.has(law) && evaluate(law, p, post) === false) { removed.add(law); const drop = {round, law, params: p, pre, request, post}; options.onDrop?.(drop); finiteDump.onDrop?.(drop) }
      }
      return true
    }
    for (const {p, st} of base) visit(p, st)
    for (let tries = 0; accepted < requested && tries < Math.max(requested * 8, requested); tries++) {
      checkWall('finite neighbors')
      const {p, st: old} = base[rng(base.length)]!, st: State = {...old, scalars: {...old.scalars}, maps: {...old.maps}}
      const bound = Math.max(3, ...Object.values(p))
      if (rng(2)) {
        // Independent finite configurations, not only near-reachable states:
        // relative CTIs often require several fields/rows to differ together.
        for (const name of scalars) { const vs = scalarValues.get(name)!; st.scalars[name] = vs[rng(vs.length)]! }
        for (const mp of maps) {
          const vs = values.get(mp)!.slice(0, bound), cells = new Map(old.maps[mp])
          for (const key of keyPools.get(mp)!) cells.set(key, vs[rng(vs.length)]!)
          st.maps[mp] = cells
        }
      } else for (let i = 0, n = 1 + rng(2); i < n; i++) {
        if (maps.length && (!scalars.length || rng(2) === 0)) {
          const mp = maps[rng(maps.length)]!, keys = [...old.maps[mp]?.keys() ?? []], key = keys.length ? keys[rng(keys.length)]! : 0, vs = values.get(mp)!, value = vs.length ? vs[rng(vs.length)]! : 0
          st.maps[mp] = new Map(st.maps[mp]); st.maps[mp]!.set(key, value)
        } else if (scalars.length) { const name = scalars[rng(scalars.length)]!; st.scalars[name] = Math.max(0, st.scalars[name]! + rng(3) - 1) }
      }
      if (visit(p, st)) accepted++
    }
    options.onRound?.({round, alive: alive.length, dropped: removed.size, randomStates: accepted, steps})
    if (!removed.size) return alive
    alive = alive.filter(law => !removed.has(law))
  }
}
