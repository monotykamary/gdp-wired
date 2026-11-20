// Untrusted unguarded per-key invariant seeds: when a universally quantified law has the shape
//   ∀ k. guard(k) ⇒ (P₁(k) ∧ P₂(k) ∧ ...)
// where a conjunct P_i(k) is an atomic comparison relating at least two distinct maps at k and
// reading none of the guard's state variables or maps, the guard often acts as a latch (e.g.
// recording a majority or leader) that starts false so the induction hypothesis is silent at the
// step the latch flips. Lifting P_i(k) to an unguarded candidate ∀ k. P_i(k), filtering it on
// short reachable runs, and handing surviving seeds to ordinary kernel-checked proveLaws closes
// such laws without modifying the kernel or adding ghost state.
import {
  type C, type Law, type Machine, type Rand, type State,
  evalC, interpret, seeded, walk,
} from './machine.ts'
import {allowed, watch} from './watch.ts'
import {checkWorkEndpoint} from './wall.ts'

export type UnguardDraws = {
  params: (rand: Rand, bound: number) => Record<string, number>
  input: (rand: Rand, bound: number, params: Record<string, number>) => Record<string, number | ReadonlyMap<number, number>>
}

const flatAnd = (c: C): C[] => (c.op === 'and' ? c.xs.flatMap(flatAnd) : [c])
const flatOr = (c: C): C[] => (c.op === 'or' ? c.xs.flatMap(flatOr) : [c])

function namesIn(t: unknown): Set<string> {
  const out = new Set<string>()
  walk(t, o => { if (o.op === 'var' && typeof o.name === 'string') out.add(o.name) })
  return out
}

function mapsIn(t: unknown): Set<string> {
  const out = new Set<string>()
  walk(t, o => { if (o.op === 'get' && typeof o.map === 'string') out.add(o.map) })
  return out
}

function unwrapImplies(c: C): {guards: C[], body: C} {
  const guards: C[] = []
  let cur = c
  while (cur.op === 'or') {
    const parts = flatOr(cur)
    const negs = parts.filter((p): p is Extract<C, {op: 'not'}> => p.op === 'not')
    const pos = parts.filter(p => p.op !== 'not')
    if (pos.length !== 1 || !negs.length) break
    for (const g of negs) guards.push(g.x)
    cur = pos[0]!
  }
  return {guards, body: cur}
}

// Propose unguarded per-key multi-map accounting helpers purely from the syntax of `(m, law)`.
export function proposeUnguardedSeeds(m: Machine, law: Law): Law[] {
  if (!law.forall || law.keys?.length || law.some?.length || law.ex || law.finite !== undefined) return []
  if (m.history || m.primitiveFailure || Object.keys(m.counts ?? {}).length) return []
  const k = law.forall
  const {guards, body} = unwrapImplies(law.holds)
  if (!guards.length) return []

  const stateVars = new Set(Object.keys(m.state))
  const guardStateVars = new Set(guards.flatMap(g => [...namesIn(g)]).filter(v => stateVars.has(v)))
  const guardMaps = new Set(guards.flatMap(g => [...mapsIn(g)]))
  const cjs = flatAnd(body)
  // Require a scalar state latch, or a map latch gating a multi-conjunct body.
  if (!guardStateVars.size && !(guardMaps.size && cjs.length >= 2)) return []

  const used = JSON.stringify([m, law])
  let stem = 'ung$'
  while (used.includes(stem)) stem += 'u'

  const out: Law[] = []
  const seen = new Set<string>()
  for (let i = 0; i < cjs.length && out.length < 8; i++) {
    const cj = cjs[i]!
    if (cj.op !== '=' && cj.op !== '<=' && cj.op !== '<') continue
    const cjMaps = mapsIn(cj)
    // Require at least two distinct base maps (ignoring signed-integer `$neg` twin splits).
    const baseMaps = new Set([...cjMaps].map(mp => mp.replace(/\$neg$/, '')))
    if (baseMaps.size < 2) continue
    const cjVars = namesIn(cj)
    if (!cjVars.has(k)) continue
    if ([...guardStateVars].some(v => cjVars.has(v))) continue
    if ([...guardMaps].some(mp => cjMaps.has(mp))) continue
    const sig = JSON.stringify(cj)
    if (seen.has(sig)) continue
    seen.add(sig)
    out.push({name: `${stem}${i}`, forall: k, holds: cj})
  }
  return out
}

// Fast untrusted sample filter: drop candidates refuted on short reachable runs (~1 ms).
export function filterUnguardedSeeds(m: Machine, cands: Law[], draws: UnguardDraws): Law[] {
  if (!cands.length) return []
  checkWorkEndpoint('unguarded seed filter')
  let runtime: ReturnType<typeof interpret>
  try { runtime = interpret(m) } catch { return [] }

  const bound = 4
  const rand = seeded(59)
  const states: {ps: Record<string, number>, st: State}[] = []
  for (let trial = 0; trial < 20; trial++) {
    checkWorkEndpoint('unguarded seed trial')
    let ps: Record<string, number>, st: State
    try {
      ps = draws.params(rand, bound)
      if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) continue
      st = runtime.init(ps)
    } catch { continue }
    states.push({ps, st})
    for (let d = 0, tries = 0; d < 12 && tries < 36; tries++) {
      checkWorkEndpoint('unguarded seed step')
      try {
        const input = draws.input(rand, bound, ps)
        if (!allowed(m, runtime, ps, st, input)) continue
        st = runtime.step(ps, st, input)
        states.push({ps, st})
        d++
      } catch { /* refused */ }
    }
  }

  return cands.filter(h => states.every(({ps, st}) => {
    checkWorkEndpoint('unguarded seed check')
    try { return watch(m, runtime, h, ps, bound).start(st) } catch { return false }
  }))
}
