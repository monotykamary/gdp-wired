// Lean twin: Kern.GroupedSums.grouped_sum_sound (`lean-kernel/GroupedSums.lean`).
// Parameter-indexed sums over a map's keys (`ParamSumMachine`) combined with fresh
// observer-key elimination (`sreach_rebind` + `observer_elim`), with zero ghost maps.
import {type C, type E, type Law, type Machine, atMost, n, not, same, walkOnce, x} from '../core/machine.ts'
import {type Goal, type Instances, type Tree, boundOf, check, checkLaws, mapArities, obligations, own, substC, substE, sumParts, witnessesOf} from './kernel.ts'

export type GroupedSumDecl = {
  key: string
  term: E
  params: string[]
  covers?: E[]
}

export type GroupedSumCertificate = {
  kind: 'grouped-sum'
  observer: string
  group: E
  sums: Record<string, GroupedSumDecl>
  laws: Law[]
  proof: {instances: Record<string, Instances>, trees: Record<string, Tree>}
}

const ZERO: E = n(0)
const TRUE_C: C = atMost(ZERO, ZERO)
const text = (v: unknown) => JSON.stringify(v)
const eq = (a: unknown, b: unknown) => text(a) === text(b)
const safeNat = (v: unknown): v is number => typeof v === 'number' && Number.isSafeInteger(v) && v >= 0
const plainId = (name: unknown): name is string =>
  typeof name === 'string' && name.length > 0 && name !== '1' && !/[*[\],:#?~'⟦⟧⟨⟩|]/.test(name)
const nullRecord = <V>(entries: readonly [string, V][]): Record<string, V> =>
  Object.assign(Object.create(null) as Record<string, V>, Object.fromEntries(entries))

const dTerm = (G: (t: E) => E, cs: E[]): E =>
  cs.length ? {op: 'add', a: G(cs[0]!), b: dTerm(t => ({op: 'if', c: same(t, cs[0]!), then: ZERO, else: G(t)}), cs.slice(1))} : ZERO

function paramSumTermOk(e: E, key: string, params: readonly string[]): boolean {
  switch (e.op) {
    case 'var': return params.includes(e.name)
    case 'const': return true
    case 'get': return e.key.op === 'var' && e.key.name === key
    case 'mul': return paramSumTermOk(e.a, key, params)
    case 'if': return paramSumCondOk(e.c, key, params) && paramSumTermOk(e.then, key, params) && paramSumTermOk(e.else, key, params)
    case 'add': case 'sub': case 'min': case 'max': case 'prod':
      return paramSumTermOk(e.a, key, params) && paramSumTermOk(e.b, key, params)
    case 'tup': case 'proj': return false
    default: return false
  }
}

function paramSumCondOk(c: C, key: string, params: readonly string[]): boolean {
  if (c.op === 'flag' || c.op === 'all') return false
  if (c.op === 'not') return paramSumCondOk(c.x, key, params)
  if (c.op === 'and' || c.op === 'or') return c.xs.every(y => paramSumCondOk(y, key, params))
  return paramSumTermOk(c.a, key, params) && paramSumTermOk(c.b, key, params)
}

function hasVar(root: unknown, name: string): boolean {
  let found = false
  walkOnce(root, o => {
    const t = o as {op?: string, name?: unknown}
    if (t.op === 'var' && t.name === name) found = true
  })
  return found
}

function hasFlagOrAll(root: unknown): boolean {
  let found = false
  walkOnce(root, o => {
    const t = o as {op?: string}
    if (t.op === 'flag' || t.op === 'all') found = true
  })
  return found
}

function mapsIn(root: unknown): string[] {
  const out = new Set<string>()
  walkOnce(root, o => {
    const t = o as {op?: string, map?: unknown}
    if (t.op === 'get' && typeof t.map === 'string') out.add(t.map)
  })
  return [...out]
}

function comparedKeys(t: E | C, key: string, out: Map<string, E>): void {
  if (t.op === '=' && t.a.op === 'var' && t.a.name === key && !hasVar(t.b, key)) out.set(text(t.b), t.b)
  else if (t.op === '=' && t.b.op === 'var' && t.b.name === key && !hasVar(t.a, key)) out.set(text(t.a), t.a)
  for (const v of Object.values(t)) {
    if (v && typeof v === 'object') (Array.isArray(v) ? v : [v]).forEach(y => comparedKeys(y as E | C, key, out))
  }
}

export function defaultGroupedCovers(m: Machine, term: E): E[] {
  const out = new Map<string, E>()
  for (const map of mapsIn(term)) {
    const w = own(m.step.maps ?? {}, map)
    if (!w) continue
    if ('each' in w) comparedKeys(w.value, w.each, out)
    else out.set(text(w.key), w.key)
  }
  return [...out.values()]
}

const pcellLaws = (laws: Law[], read: string[], X: E, ps: readonly string[]): C[] =>
  laws.flatMap(l => (l.forall && !l.keys?.length && !ps.includes(l.forall) && paramSumCondOk(l.holds, l.forall, ps)
    && mapsIn(l.holds).every(mp => read.includes(mp))
    ? [substC(l.holds, {vars: {[l.forall]: X}, maps: {}, flags: {}})] : []))

export type CheckedGroupedSumDecl = {
  name: string
  key: string
  params: string[]
  term: E
  covers: E[]
  flag: string
  x: string
  read: string[]
}

export function groupedSumTheory(source: Machine, law: Law, cert: GroupedSumCertificate) {
  if (!cert || cert.kind !== 'grouped-sum' || !plainId(cert.observer) || !cert.group || typeof cert.group !== 'object') return
  if (!cert.sums || typeof cert.sums !== 'object' || Array.isArray(cert.sums)) return
  const sumEntries = Object.entries(cert.sums)
  if (!sumEntries.length || !Array.isArray(cert.laws) || !cert.laws.length) return
  if (!cert.proof || typeof cert.proof !== 'object'
      || !cert.proof.instances || typeof cert.proof.instances !== 'object' || Array.isArray(cert.proof.instances)
      || !cert.proof.trees || typeof cert.proof.trees !== 'object' || Array.isArray(cert.proof.trees)) return
  if (source.history || source.primitiveFailure || Object.keys(source.counts ?? {}).length
      || Object.keys(source.sums ?? {}).length || Object.keys(source.leasts ?? {}).length
      || Object.keys(source.fns ?? {}).length || source.facts?.length) return
  if (law.keys?.length || law.some?.length || law.ex || law.finite !== undefined) return
  if (cert.laws.some(l => l.some?.length || l.ex || l.finite !== undefined)) return

  // Reject non-safe naturals and word-division intrinsics (which require WordSReach).
  let unsupported = false
  walkOnce([source, law, cert.group, cert.sums, cert.laws, cert.proof.instances], o => {
    const t = o as {op?: string, map?: unknown, value?: unknown, k?: unknown}
    if (t.op === 'get' && typeof t.map === 'string' && t.map.startsWith('worddiv$')) unsupported = true
    if (t.op === 'const' && !safeNat(t.value)) unsupported = true
    if (t.op === 'mul' && !safeNat(t.k)) unsupported = true
  })
  if (unsupported || !Object.values(source.maps ?? {}).every(safeNat)) return

  // Existing scope + naturalness checks establish disjoint params/inputs/state/maps/inputMaps/flags/binders,
  // ensuring names absent from sourceNames never occur anywhere in source.
  obligations(source, [law])
  if (Object.values(mapArities(source, [law])).some(a => a !== 1)) return

  const obs = cert.observer
  const flags = source.step.flags ?? {}
  const sourceNames = new Set<string>([
    ...source.params, ...source.inputs, ...Object.keys(source.state),
    ...Object.keys(source.maps ?? {}), ...(source.inputMaps ?? []),
    ...Object.keys(flags), ...Object.keys(flags).map(f => `?${f}`),
    ...Object.entries(flags).flatMap(([f, c]) => (c.op === 'all' ? [...witnessesOf(f, c), ...boundOf(c)] : [])),
    ...Object.values(source.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : [])),
  ])

  // observerOk source obs, hkey (law.forall !== obs), hgrp (!occE obs grp), hlo (!occC obs law.holds), and flag-free group term.
  if (sourceNames.has(obs) || law.forall === obs || hasVar(cert.group, obs) || hasVar(law.holds, obs) || hasFlagOrAll(cert.group)) return

  const sameFlags: Record<string, C> = nullRecord(Object.keys(flags).map(f => [f, {op: 'flag', name: f} as C]))
  const inlinedFlags: Record<string, C> = Object.create(null)
  for (const [f, c] of Object.entries(flags)) {
    inlinedFlags[f] = c.op === 'all' ? same(x(`?${f}`), n(1)) : substC(c, {vars: {}, maps: {}, flags: inlinedFlags})
  }
  const leanSubst = {
    vars: {},
    maps: {},
    flags: nullRecord(Object.entries(inlinedFlags).map(([f, c]): [string, C] => [
      f, flags[f]!.op === 'all' ? c : same({op: 'if', c, then: n(1), else: ZERO}, n(1)),
    ])),
  }

  // Reserve all sum-owned names disjoint from sourceNames, obs, and each other (sghostOk).
  const taken = new Set<string>([...sourceNames, obs])
  const ghostVars: string[] = []
  for (const [s] of sumEntries) {
    if (!plainId(s)) return
    const {flag, x: xv} = sumParts(s)
    const owned = [s, flag, xv, `?${flag}`, `w?${flag}`]
    if (owned.some(nm => taken.has(nm))) return
    for (const nm of owned) taken.add(nm)
    ghostVars.push(s, `?${flag}`)
  }

  const steps: Record<string, E> = Object.create(null)
  const qflags: Record<string, C> = Object.create(null)
  const zeroSums: Record<string, E> = Object.create(null)
  const facts: C[] = []
  const initGoals: Goal[] = []
  const coverGoals: Goal[] = []
  const decls: CheckedGroupedSumDecl[] = []

  for (const [s, sum] of sumEntries) {
    if (!sum || typeof sum !== 'object' || !plainId(sum.key) || !sum.term || typeof sum.term !== 'object') return
    if (!Array.isArray(sum.params) || new Set(sum.params).size !== sum.params.length) return
    const {flag, x: xv} = sumParts(s)
    if (taken.has(sum.key)) return

    // paramImmutable: every p in sum.params must be obs or a declared source parameter.
    // Because taken contains sourceNames ∪ {obs} ∪ sum-owned names and sum.key ∉ taken,
    // p is automatically disjoint from inputs, state, step, flags, qVars, wVars, sums, sum.key, and xv.
    for (const p of sum.params) {
      if (p !== obs && !source.params.includes(p)) return
    }

    // gOkEP and summed map checks (scope guarantees source.maps is disjoint from inputMaps and fns).
    if (!paramSumTermOk(sum.term, sum.key, sum.params)) return
    const read = mapsIn(sum.term)
    if (!read.every(mp => Object.hasOwn(source.maps ?? {}, mp))) return

    if (sum.covers !== undefined && !Array.isArray(sum.covers)) return
    const cs = sum.covers ?? defaultGroupedCovers(source, sum.term)
    if (cs.some(c => !c || typeof c !== 'object' || hasFlagOrAll(c) || hasVar(c, sum.key) || hasVar(c, xv) || ghostVars.some(v => hasVar(c, v)))) return
    for (const mp of read) {
      const w = own(source.step.maps ?? {}, mp)
      if (w && !('each' in w) && !cs.some(c => eq(c, w.key))) return
    }

    // S @init goal (GroupedSums.psumStartGoal)
    const atStart = substE(sum.term, {
      vars: {},
      maps: nullRecord(read.map(mp => [mp, () => n(source.maps![mp]!)])),
      flags: sameFlags,
    })
    initGoals.push({name: `${s} @init`, hyps: [source.pre ?? TRUE_C, not(same(atStart, ZERO))]})

    // Plain machine definitions (GroupedSums.ParamSumMachine.plain)
    const here = (t: E): E => substE(sum.term, {vars: {[sum.key]: t}, maps: {}, flags: sameFlags})
    const post = (mp: string) => (k2: E): E => {
      const w = own(source.step.maps ?? {}, mp)
      if (!w) return {op: 'get', map: mp, key: k2}
      if ('each' in w) return substE(w.value, {vars: {[w.each]: k2}, maps: {}, flags: sameFlags})
      return {op: 'if', c: same(k2, w.key), then: w.value, else: {op: 'get', map: mp, key: k2}}
    }
    const after = (t: E): E => substE(sum.term, {vars: {[sum.key]: t}, maps: nullRecord(read.map(mp => [mp, post(mp)])), flags: sameFlags})
    const S: E = x(s)
    zeroSums[s] = ZERO
    steps[s] = {op: 'sub', a: {op: 'add', a: S, b: dTerm(after, cs)}, b: dTerm(here, cs)}
    qflags[flag] = {op: 'all', key: sum.key, c: atMost(dTerm(here, [x(sum.key), ...cs]), S)}
    facts.push({op: 'and', xs: [atMost(dTerm(here, cs), S), {op: 'flag', name: flag}]})

    // Every-write cover goals (GroupedSums.psumCoverGoal)
    const X: E = x(xv)
    for (const [mp, w] of Object.entries(source.step.maps ?? {})) {
      if (!('each' in w) || !read.includes(mp)) continue
      coverGoals.push({
        name: `${s} @cover ${mp}`,
        hyps: [
          substC(source.assume ?? TRUE_C, leanSubst),
          ...pcellLaws(cert.laws, read, X, sum.params),
          ...cs.map((c): C => not(same(X, c))),
          not(same(substE(substE(w.value, leanSubst), {vars: {[w.each]: X}, maps: {}, flags: {}}), {op: 'get', map: mp, key: X})),
        ],
      })
    }

    decls.push({name: s, key: sum.key, params: sum.params, term: sum.term, covers: cs, flag, x: xv, read})
  }

  // Verify exact guardLaw(law, obs, cert.group) is in cert.laws and avoids all sum ghosts.
  if (ghostVars.some(v => hasVar(cert.group, v))) return
  const expectedGuard: Law = {
    name: law.name,
    ...(law.forall ? {forall: law.forall} : {}),
    holds: {op: 'or', xs: [not(same(cert.group, x(obs))), law.holds]},
  }
  const guardIndex = cert.laws.findIndex(l => eq(l, expectedGuard))
  if (guardIndex < 0) return

  const assumed = facts.reduceRight<C>((acc, f) => ({op: 'and', xs: [f, acc]}), TRUE_C)
  const plain: Machine = {
    ...source,
    params: [...source.params, obs],
    state: {...source.state, ...zeroSums},
    step: {...source.step, flags: {...flags, ...qflags}, state: {...source.step.state, ...steps}},
    assume: {op: 'and', xs: [source.assume ?? TRUE_C, assumed]},
  }
  return {plain, observer: obs, group: cert.group, decls, initGoals, coverGoals, guardIndex}
}

export function checkGroupedSum(source: Machine, law: Law, cert: GroupedSumCertificate): boolean {
  try {
    const t = groupedSumTheory(source, law, cert)
    if (!t) return false
    if (!checkLaws(t.plain, cert.laws, cert.proof)) return false
    for (const g of [...t.initGoals, ...t.coverGoals]) {
      const tree = own(cert.proof.trees, g.name)
      if (!tree || !check(g, tree)) return false
    }
    return true
  } catch { return false }
}
