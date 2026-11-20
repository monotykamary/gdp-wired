// Untrusted grouped-sum candidate synthesis and proving.
// Recognizes row-grouped covering laws of the shape:
//   ∀ k. G(k) ⇒ w(k) ≤ Tot[grp(k)]   (and companion scalar clauses ∀ k. G'(k) ⇒ w'(k) ≤ X)
// synthesizes fresh observer + parameterized sum helpers, proves the plain SMachine family,
// and accepts ONLY certificates verified by the trusted checker `checkGroupedSum`.
import {type C, type E, type Law, type Machine, atMost, get, n, not, plus, same, x} from './machine.ts'
import {type GroupedSumCertificate, type GroupedSumDecl, checkGroupedSum, groupedSumTheory} from '../kernel/grouped-sum.ts'
import {type Tree, substC, substE} from '../kernel/kernel.ts'
import {clock, grow, pastWall, proveLaws, withDeadline} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'

type Lit = {c: C, neg: boolean}
const ZERO: E = n(0)
const ONE: E = n(1)
const text = (v: unknown) => JSON.stringify(v)

function clauses(c: C, neg: boolean, most: number): Lit[][] | undefined {
  switch (c.op) {
    case 'not': return clauses(c.x, !neg, most)
    case 'and': case 'or': {
      const parts = c.xs.map(y => clauses(y, neg, most))
      if (parts.some(p => !p)) return undefined
      if ((c.op === 'and') !== neg) {
        const out = (parts as Lit[][][]).flat()
        return out.length > most ? undefined : out
      }
      let out: Lit[][] = [[]]
      for (const p of parts as Lit[][][]) {
        out = out.flatMap(a => p.map(b => [...a, ...b]))
        if (out.length > most) return undefined
      }
      return out
    }
    case '<': case '<=': case '=': return [[{c, neg}]]
    case 'flag': case 'all': return undefined
  }
}

type Reads = {vars: Set<string>, maps: Set<string>, keyed: boolean, shaped: boolean}
function reads(t: E | C, key: string, r: Reads = {vars: new Set(), maps: new Set(), keyed: true, shaped: true}): Reads {
  switch (t.op) {
    case 'var': r.vars.add(t.name); break
    case 'const': break
    case 'get': r.maps.add(t.map); if (!(t.key.op === 'var' && t.key.name === key)) { r.keyed = false; reads(t.key, key, r) } break
    case 'mul': reads(t.a, key, r); break
    case 'add': case 'sub': case 'min': case 'max': case 'prod': reads(t.a, key, r); reads(t.b, key, r); break
    case 'if': reads(t.c, key, r); reads(t.then, key, r); reads(t.else, key, r); break
    case 'tup': case 'proj': r.shaped = false; break
    case '<': case '<=': case '=': reads(t.a, key, r); reads(t.b, key, r); break
    case 'and': case 'or': for (const y of t.xs) reads(y, key, r); break
    case 'not': reads(t.x, key, r); break
    case 'flag': case 'all': r.shaped = false; break
  }
  return r
}

function atMostLit(l: Lit): {lo: E, hi: E} | undefined {
  const c = l.c
  if (c.op === '<=' && !l.neg) return {lo: c.a, hi: c.b}
  if (c.op === '<' && l.neg) return {lo: c.b, hi: c.a}
  if (c.op === '<' && !l.neg && c.a.op === 'const') return {lo: n(c.a.value + 1), hi: c.b}
  if (c.op === '<=' && l.neg && c.b.op === 'const') return {lo: n(c.b.value + 1), hi: c.a}
  if (c.op === '=' && l.neg) {
    if (c.a.op === 'const' && c.a.value === 0) return {lo: ONE, hi: c.b}
    if (c.b.op === 'const' && c.b.value === 0) return {lo: ONE, hi: c.a}
  }
  return undefined
}

const litC = (l: Lit): C => (l.neg ? not(l.c) : l.c)
const notLit = (l: Lit): C => (l.neg ? l.c : not(l.c))

type GroupedClause = {
  kind: 'grouped'
  totMap: string
  group: E
  weight: E
  guards: C[]
  unless: C[]
}

type ScalarClause = {
  kind: 'scalar'
  total: E
  weight: E
  guards: C[]
  unless: C[]
}

type ParsedShapes = {
  key: string
  grouped: GroupedClause[]
  scalar: ScalarClause[]
}

function parseGroupedShapes(m: Machine, law: Law): ParsedShapes | undefined {
  const key = law.forall
  if (!key || law.keys?.length || law.some?.length || law.ex || law.finite !== undefined || law.witness) return
  if (m.history || m.primitiveFailure || Object.keys(m.counts ?? {}).length
      || Object.keys(m.sums ?? {}).length || Object.keys(m.leasts ?? {}).length || !m.maps) return
  const cs = clauses(law.holds, false, 16)
  if (!cs) return
  const stateMap = (name: string) => Object.hasOwn(m.maps!, name) && !(m.inputMaps ?? []).includes(name) && !Object.hasOwn(m.fns ?? {}, name)
  const scalarVar = (name: string) => Object.hasOwn(m.state, name)
  const cellTerm = (t: E | C) => {
    const r = reads(t, key)
    return r.shaped && r.keyed && r.maps.size > 0 && r.vars.size === 0 && [...r.maps].every(stateMap)
  }
  const freeTerm = (t: E | C) => {
    const r = reads(t, key)
    return r.shaped && !r.vars.has(key) && r.maps.size === 0
  }
  const scalarTotal = (t: E) => freeTerm(t) && [...reads(t, key).vars].some(scalarVar)
  const groupedTotal = (t: E): {totMap: string, group: E} | undefined =>
    t.op === 'get' && stateMap(t.map) && cellTerm(t.key) ? {totMap: t.map, group: t.key} : undefined

  const grouped: GroupedClause[] = []
  const scalar: ScalarClause[] = []

  for (const clause of cs) {
    const guards: C[] = [], unless: C[] = []
    let grpMatch: {totMap: string, group: E} | undefined
    let weight: E | undefined, scalTot: E | undefined
    let ok = true
    for (const l of clause) {
      if (cellTerm(l.c)) { guards.push(notLit(l)); continue }
      const le = atMostLit(l)
      if (le) {
        const gt = groupedTotal(le.hi)
        if (gt && !grpMatch && !scalTot && (cellTerm(le.lo) || (le.lo.op === 'const' && le.lo.value === 1))) {
          grpMatch = gt; weight = le.lo; continue
        }
        if (scalarTotal(le.hi) && !grpMatch && !weight && !scalTot && cellTerm(le.lo)) {
          weight = le.lo; scalTot = le.hi; continue
        }
        if (scalarTotal(le.hi) && !grpMatch && le.lo.op === 'const' && le.lo.value === 1 && (!weight || text(weight) === text(ONE))) {
          weight = ONE; scalTot = scalTot ? plus(scalTot, le.hi) : le.hi; continue
        }
      }
      if (freeTerm(l.c)) { unless.push(litC(l)); continue }
      ok = false; break
    }
    if (!ok || !weight) continue
    if (weight.op === 'const' && !guards.length) continue
    if (grpMatch) grouped.push({kind: 'grouped', totMap: grpMatch.totMap, group: grpMatch.group, weight, guards, unless})
    else if (scalTot) scalar.push({kind: 'scalar', total: scalTot, weight, guards, unless})
  }
  if (!grouped.length) return
  return {key, grouped, scalar}
}

const andAll = (xs: C[]): C => (xs.length === 1 ? xs[0]! : {op: 'and', xs})

function tryProveVariant(
  source: Machine,
  law: Law,
  observer: string,
  group: E,
  sums: Record<string, GroupedSumDecl>,
  laws: Law[],
  until: number,
): GroupedSumCertificate | undefined {
  if (clock() >= until || pastWall()) return
  const dummy: GroupedSumCertificate = {
    kind: 'grouped-sum',
    observer,
    group,
    sums,
    laws,
    proof: {instances: {}, trees: {}},
  }
  const theory = groupedSumTheory(source, law, dummy)
  if (!theory) return

  const sideTrees: Record<string, Tree> = Object.create(null)
  for (const g of theory.initGoals) {
    if (clock() >= until || pastWall()) return
    const res = grow(g, new Map(), {nodes: 0, until: Math.min(until, clock() + 500)})
    if (!('tree' in res)) return
    sideTrees[g.name] = res.tree
  }

  const out = withDeadline(until, () => proveLaws(theory.plain, laws))
  if (!out.proven || !out.checked || !out.proof || pastWall()) return

  for (const g of theory.coverGoals) {
    if (clock() >= until || pastWall()) return
    const quick = grow(g, new Map(), {nodes: 0, until: Math.min(until, clock() + 500)})
    const got = 'tree' in quick ? quick : growCdcl(g, new Map(), {nodes: 0, until})
    if (!('tree' in got)) return
    sideTrees[g.name] = got.tree
  }

  const cert: GroupedSumCertificate = {
    kind: 'grouped-sum',
    observer,
    group,
    sums,
    laws,
    proof: {instances: out.proof.instances, trees: {...out.proof.trees, ...sideTrees}},
  }
  return checkGroupedSum(source, law, cert) ? cert : undefined
}

export function searchGroupedSum(source: Machine, law: Law, ms: number): GroupedSumCertificate | undefined {
  if (!Number.isFinite(ms) || ms <= 0) return
  const parsed = parseGroupedShapes(source, law)
  if (!parsed) return
  const {key, grouped, scalar} = parsed
  const until = clock() + ms

  // Fresh prefix avoiding every identifier already present in source or law.
  const occupied = text([source, law])
  let prefix = 'gs$'
  while (occupied.includes(prefix)) prefix += 'a'
  const observer = `${prefix}obs`

  // Try each distinct group key expression found in the law (usually one).
  const distinctGroups = [...new Map(grouped.map(g => [text(g.group), g.group])).values()]
  for (const group of distinctGroups) {
    if (clock() >= until || pastWall()) return
    const matchingGrouped = grouped.filter(g => text(g.group) === text(group))
    const sums: Record<string, GroupedSumDecl> = Object.create(null)
    const boundSpecs: {name: string, sumVar: string, target: E, unless: C[]}[] = []
    const zeroHelpers: Law[] = []
    const seenSum = new Map<string, string>()
    const seenZero = new Set<string>()
    let sumIdx = 0

    const addSum = (isGrouped: boolean, guards: C[], weight: E, target: E, unless: C[]) => {
      const kName = `${prefix}k${sumIdx}`
      const subKey = {vars: {[key]: x(kName)}, maps: {}, flags: {}}
      const gConds = [
        ...guards.map(g => substC(g, subKey)),
        ...(isGrouped ? [same(substE(group, subKey), x(observer))] : []),
      ]
      const wAtK = substE(weight, subKey)
      const term: E = gConds.length ? {op: 'if', c: andAll(gConds), then: wAtK, else: ZERO} : wAtK
      const params = isGrouped ? [observer] : []
      // Deduplicate sums modulo key-binder renaming.
      const sig = text({params, term: substE(term, {vars: {[kName]: x(key)}, maps: {}, flags: {}})})
      let sName = seenSum.get(sig)
      if (!sName) {
        sName = `${prefix}s${sumIdx++}`
        seenSum.set(sig, sName)
        sums[sName] = {key: kName, term, params}
      }
      boundSpecs.push({name: `${prefix}bound_${boundSpecs.length}`, sumVar: sName, target, unless})

      // Canonical inactive-cell-zero companion law for weighted sums over a 0-initialized map.
      if (weight.op === 'get' && source.maps?.[weight.map] === 0 && guards.length) {
        const holds: C = {op: 'or', xs: [andAll(guards), same(weight, ZERO)]}
        const zSig = text(holds)
        if (!seenZero.has(zSig)) {
          seenZero.add(zSig)
          zeroHelpers.push({name: `${prefix}zero_${zeroHelpers.length}`, forall: key, holds})
        }
      }
    }

    for (const sc of scalar) addSum(false, sc.guards, sc.weight, sc.total, sc.unless)
    for (const gc of matchingGrouped) addSum(true, gc.guards, gc.weight, get(gc.totMap, x(observer)), gc.unless)

    const guardTarget: Law = {
      name: law.name,
      forall: key,
      holds: {op: 'or', xs: [not(same(group, x(observer))), law.holds]},
    }
    const makeBounds = (op: '<=' | '='): Law[] => boundSpecs.map(b => {
      const cmp: C = op === '<=' ? atMost(x(b.sumVar), b.target) : same(x(b.sumVar), b.target)
      return {name: b.name, holds: b.unless.length ? {op: 'or', xs: [...b.unless, cmp]} : cmp}
    })

    // Variant 0: minimal inequality family (e.g. NATS row 7).
    // Variant 1: inequality family + inactive-cell-zero companions (e.g. DuckDB row 16).
    // Variant 2: exact equality family + inactive-cell-zero companions.
    const variants: Law[][] = [
      [...makeBounds('<='), guardTarget],
      ...(zeroHelpers.length ? [[...zeroHelpers, ...makeBounds('<='), guardTarget]] : []),
      [...zeroHelpers, ...makeBounds('='), guardTarget],
    ]
    const sliceMs = Math.max(1000, Math.floor((until - clock()) / variants.length))
    for (const laws of variants) {
      if (clock() >= until || pastWall()) return
      const cert = tryProveVariant(source, law, observer, group, sums, laws, Math.min(until, clock() + sliceMs))
      if (cert) return cert
    }
  }
  return undefined
}
