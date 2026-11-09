// A finite relative-CTI filter, never a proof. Unsupported evaluations are
// unknown; only an actual enabled step from a state satisfying the WHOLE
// current family may remove a non-caller. The checked prover sees survivors.
import {type C, type E, type Law, type Machine, type Request, type State, carriedView, compileC, compileE, fastStep, interpret, seeded, walk} from './machine.ts'
import {checkWall, searchWall, WallExpired} from './wall.ts'
import {boundaryState, lawFrontiers} from './finite-frontiers.ts'
import {wallAt, withWall} from '../kernel/prove.ts'
import {type TinyFiniteOptions, type TinyFiniteStatistics, tinyFiniteCandidates} from './finite-tiny.ts'
type Env = Record<string, number>
type Samples = {p: Env, sts: State[]}[]
type Truth = boolean | undefined
const variables = (t: unknown): Set<string> => { const out = new Set<string>(); walk(t, o => { if (o.op === 'var') out.add(o.name as string) }); return out }
const conjuncts = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(conjuncts) : [c]
// Universal binders need a complete finite cover, not merely 0..sampleSize.
// Guards provide finite upper bounds (including auxiliary half-count witnesses).
// Otherwise permit only direct finite-map reads and equality between binders:
// the explicit cells plus one distinct fresh key per binder cover every case.
export function finiteEvaluator(m: Machine, stop: () => boolean = () => false): (law: Law, p: Env, st: State) => Truth {
  const checkpoint = () => { checkWall('finite derived count'); if (stop()) throw new Error('finite evaluation stopped') }
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
    if (stop()) return undefined
    let entry = cache.get(st)
    if (!entry || entry.params !== p) { entry = {params: p, view: carriedView(m, st, Object.fromEntries((m.inputMaps ?? []).map(k => [k, new Map()])), undefined, p, checkpoint), values: new Map()}; cache.set(st, entry) }
    if (entry.values.has(law)) return entry.values.get(law)
    let shape = plans.get(law); if (!shape) { shape = plan(law); plans.set(law, shape) }
    if (!shape.supported) return undefined
    const env: Env = {...p, ...st.scalars}, view = entry.view
    let visited = 0
    const go = (left: typeof shape.cover): Truth => {
      if ((visited++ & 255) === 0) { checkWall('finite law bindings'); if (stop()) return undefined }
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
export type FiniteOptions = {randomStates?: number, requests?: number, seed?: number, targeted?: boolean, wallMs?: number, onFinish?: (row: {timedOut: boolean, ms: number, dropped: number}) => void, onDrop?: (drop: FiniteDrop) => void, onRound?: (row: {round: number, alive: number, dropped: number, randomStates: number, steps: number}) => void}
export function finiteHoudini(source: Machine, m: Machine, caller: Law[], candidates: Law[], samples: Samples, options: FiniteOptions = {}): Law[] {
  const start = performance.now(), end = Math.min(wallAt(), searchWall(Math.max(0, options.wallMs ?? 2_000)))
  let survivors = candidates.slice(), timedOut = false
  try {
    return withWall(end, () => finiteHoudiniWithin(source, m, caller, candidates, samples, {...options, onDrop: drop => {
      survivors = survivors.filter(law => law !== drop.law)
      options.onDrop?.(drop)
    }}))
  } catch (error) {
    if (!(error instanceof WallExpired)) throw error
    // An enclosing deadline must still cancel the caller. Only expiration of
    // this local sampling allowance returns the already-certified survivors.
    checkWall('finite sampling completion')
    timedOut = true
    return survivors
  } finally { options.onFinish?.({timedOut, ms: performance.now() - start, dropped: candidates.length - survivors.length}) }
}
// What a law reads: its scalars and maps, a count map read as the scalars and maps of its body and bound. A law
// reading nothing a step changed keeps its truth across that step (the pre-state satisfied it), so it is not evaluated
// on the post-state: the same drops, fewer evaluations.
function lawReads(m: Machine, law: Law): {scalars: Set<string>, maps: Set<string>} {
  const scalars = new Set<string>(), maps = new Set<string>(), seen = new Set<string>()
  const visit = (t: unknown) => walk(t, o => {
    if (o.op === 'var' && (o.name as string) in m.state) scalars.add(o.name as string)
    if (o.op === 'get') {
      const map = o.map as string
      if (m.counts?.[map]) { if (!seen.has(map)) { seen.add(map); visit([m.counts[map]!.below, m.counts[map]!.body]) } }
      else maps.add(map)
    }
  })
  visit(law.holds)
  return {scalars, maps}
}
// Experimental tiny-instance proposal backend. Every drop crosses the same
// independent whole-family/source-interpreter boundary as sampled Houdini.
// It is not wired into production generation until its bounded pilot passes.
export function finiteTinyHoudini(source: Machine, m: Machine, caller: Law[], candidates: Law[], params: Env[], options: FiniteOptions & TinyFiniteOptions & {rounds?: number, onTiny?: (round: number, stats: TinyFiniteStatistics) => void} = {}): Law[] {
  const start = performance.now(), end = Math.min(wallAt(), searchWall(Math.max(0, options.wallMs ?? 2_000)))
  let survivors = candidates.slice(), timedOut = false
  try {
    return withWall(end, () => {
      if (source.history || m.history || Object.keys(source.leasts ?? {}).length || Object.keys(m.leasts ?? {}).length || Object.keys(source.sums ?? {}).length || Object.keys(m.sums ?? {}).length) return survivors
      finiteDump.onStart?.({machine: m, caller, candidates})
      const evaluate = finiteEvaluator(m), run = interpret(source), protectedLaws = new Set(caller)
      const declarations: Law[] = [...(m.pre ? [{name: 'finite parameter precondition', holds: m.pre}] : []), ...m.facts ?? []]
      const rounds = options.rounds === undefined ? Infinity : Math.max(0, Math.floor(options.rounds))
      for (let round = 0; round < rounds; round++) {
        checkWall('tiny Houdini round')
        const active = [...caller, ...survivors], family = [...declarations, ...active], removed = new Set<Law>()
        for (const p of params) {
          checkWall('tiny Houdini instance')
          const stats = tinyFiniteCandidates(source, m, active, p, (pre, request) => {
            checkWall('tiny Houdini certification')
            // The screen's constraints and reported post-laws are not trusted.
            if (!family.every(law => evaluate(law, p, pre) === true)) return false
            let post: State
            try { post = run.step(p, pre, request) } catch (e) { if (e instanceof WallExpired) throw e; return false }
            let accepted = false
            for (const law of survivors) {
              if (protectedLaws.has(law) || removed.has(law) || evaluate(law, p, post) !== false) continue
              removed.add(law); accepted = true
              // Preserve a fully certified drop if the rest of the pass expires.
              survivors = survivors.filter(other => other !== law)
              const drop = {round, law, params: p, pre, request, post}
              options.onDrop?.(drop); finiteDump.onDrop?.(drop)
            }
            return accepted
          }, options)
          // The proposer reports partial statistics when its wall expires. It
          // cannot suppress either this local cap or an earlier enclosing wall.
          checkWall('tiny Houdini completion')
          options.onTiny?.(round, stats)
        }
        if (!removed.size) return survivors
      }
      return survivors
    })
  } catch (e) {
    if (!(e instanceof WallExpired)) throw e
    checkWall('tiny Houdini outer completion')
    timedOut = true
    return survivors
  } finally { options.onFinish?.({timedOut, ms: performance.now() - start, dropped: candidates.length - survivors.length}) }
}

function finiteHoudiniWithin(source: Machine, m: Machine, caller: Law[], candidates: Law[], samples: Samples, options: FiniteOptions): Law[] {
  finiteDump.onStart?.({machine: m, caller, candidates})
  // Derived sum-state consistency is not reconstructed by this finite backend.
  if (Object.keys(m.sums ?? {}).length) return candidates
  const declarations: Law[] = [...(m.pre ? [{name: 'finite parameter precondition', holds: m.pre}] : []), ...m.facts ?? []]
  const evaluate = finiteEvaluator(m), rng = seeded(options.seed ?? 17), run = interpret(source), step = fastStep(source) ?? run.step
  const base = samples.flatMap(({p, sts}) => sts.map(st => ({p, st})))
  if (!base.length) return candidates
  const scalars = Object.keys(source.state), maps = Object.keys(source.maps ?? {}), requested = options.randomStates ?? 2000
  const readsOf = new Map<Law, ReturnType<typeof lawReads>>()
  const reads = (law: Law) => { let r = readsOf.get(law); if (!r) readsOf.set(law, (r = lawReads(m, law))); return r }
  const cellsDiffer = (mp: string, a: State, b: State): boolean => {
    const av = a.maps[mp], bv = b.maps[mp], ad = a.defaults?.[mp] ?? source.maps![mp]!, bd = b.defaults?.[mp] ?? source.maps![mp]!
    if (ad !== bd) return true
    if (av === bv) return false
    for (const [k, v] of av ?? []) if (v !== (bv?.get(k) ?? bd)) return true
    for (const [k, v] of bv ?? []) if (v !== (av?.get(k) ?? ad)) return true
    return false
  }
  // The law a state failed first, so a later round re-reads only the states a since-dropped law had rejected.
  const failures = new Map<Law, number>()
  const order = (family: Law[]) => [...family].sort((a, b) => (failures.get(b) ?? 0) - (failures.get(a) ?? 0))
  const values = new Map(maps.map(mp => [mp, [...new Set([source.maps![mp]!, ...base.flatMap(({st}) => [...st.maps[mp]?.values() ?? []])])].sort((a, b) => a - b)]))
  const keyPools = new Map(maps.map(mp => [mp, [...new Set(base.flatMap(({st}) => [...st.maps[mp] ?? []].filter(([, v]) => v !== (st.defaults?.[mp] ?? source.maps![mp])).map(([k]) => k)))]]))
  const scalarValues = new Map(scalars.map(name => [name, [...new Set(base.map(({st}) => st.scalars[name]!))]]))
  const numericInputs = source.inputs.map(name => ({name, bound: Math.max(3, ...conjuncts(source.assume ?? {op: 'and', xs: []}).flatMap(c => (c.op === '<' || c.op === '<=') && c.a.op === 'var' && c.a.name === name && c.b.op === 'const' && c.b.value <= 8 ? [c.b.value + Number(c.op === '<=')] : []))}))
  const sameState = (a: State, b: State): boolean => a.history === b.history && a.last === b.last && scalars.every(k => a.scalars[k] === b.scalars[k]) && maps.every(mp => {
    const av = a.maps[mp], bv = b.maps[mp], ad = a.defaults?.[mp] ?? source.maps![mp]!, bd = b.defaults?.[mp] ?? source.maps![mp]!
    return ad === bd && (av === bv || ([...av ?? []].every(([k, v]) => v === (bv?.get(k) ?? bd)) && [...bv ?? []].every(([k, v]) => v === (av?.get(k) ?? ad))))
  })
  const protectedLaws = new Set(caller), dropped = new Set<Law>()
  let alive = [...candidates]
  // A state a round rejected, with the law that rejected it: once that law is dropped the state may be lawful.
  let rejected: {p: Env, st: State, by: Law}[] = []
  for (let round = 0; ; round++) {
    const family = order([...declarations, ...caller, ...alive]), removed = new Set<Law>()
    let accepted = 0, steps = 0
    const rejecting = (p: Env, st: State): Law | undefined => { for (const law of family) if (evaluate(law, p, st) !== true) { failures.set(law, (failures.get(law) ?? 0) + 1); return law } return undefined }
    const visit = (p: Env, pre: State): boolean => {
      const by = rejecting(p, pre)
      if (by) { rejected.push({p, st: pre, by}); return false }
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
        const changedScalars = scalars.filter(k => pre.scalars[k] !== post.scalars[k]), changedMaps = maps.filter(mp => cellsDiffer(mp, pre, post))
        for (const law of alive) {
          if (protectedLaws.has(law) || removed.has(law)) continue
          const r = reads(law)
          if (!changedScalars.some(k => r.scalars.has(k)) && !changedMaps.some(mp => r.maps.has(mp))) continue
          if (evaluate(law, p, post) === false) { removed.add(law); const drop = {round, law, params: p, pre, request, post}; options.onDrop?.(drop); finiteDump.onDrop?.(drop) }
        }
      }
      return true
    }
    // A later round re-reads only the states a since-dropped law had rejected: every other rejected state still fails
    // a law that is still in the family, and every visited state was read against every law then alive.
    if (round > 0) {
      const revived = rejected.filter(r => dropped.has(r.by))
      rejected = rejected.filter(r => !dropped.has(r.by))
      for (const {p, st} of revived) if (visit(p, st)) accepted++
      options.onRound?.({round, alive: alive.length, dropped: removed.size, randomStates: accepted, steps})
      if (!removed.size) return alive
      for (const law of removed) dropped.add(law)
      alive = alive.filter(law => !removed.has(law))
      continue
    }
    // Use each law's own atoms before spending the random budget: a cube's
    // one-sided boundary, a guard enabled, or a bounded field at its limit.
    const frontiers = options.targeted === false ? [] : alive.flatMap(law => lawFrontiers(law).map(conditions => ({law, conditions})))
    for (let i = 0; frontiers.length && i < Math.min(requested, frontiers.length * 8); i++) {
      checkWall('finite frontiers')
      const {p, st: old} = base[rng(base.length)]!, {law, conditions} = frontiers[i % frontiers.length]!
      const bound = Math.max(1, ...Object.values(p)), keys = Object.fromEntries([law.forall, ...law.keys ?? []].filter((k): k is string => !!k).map(k => [k, rng(bound)]))
      const st = boundaryState(source, m, conditions, p, old, keys)
      if (st) visit(p, st)
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
    for (const law of removed) dropped.add(law)
    alive = alive.filter(law => !removed.has(law))
  }
}
