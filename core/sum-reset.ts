// Untrusted reset-guard extraction for map sums over `each` writes.
//
// Given a machine `m` and a sum declaration `{key, term}`, inspects the outer key-independent `if`
// spine of every `each`-written map read by `term` to find a key-independent condition `R` under
// which `term` evaluates to 0 at every key (e.g. cache clears, buffer flushes, epoch wipes).
//
// This module is completely untrusted: any candidate `R` it returns must still pass the trusted
// kernel's syntactic side conditions (`resetOk`: key-independent, avoiding all summed maps) and
// its two proof obligations (`@reset` under `R`, `@cover` under `¬R`).
import {type C, type E, type Machine, type Sum} from './machine.ts'
import {sumParts} from '../kernel/kernel.ts'

const TRUE_C: C = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
const keyOf = (x: unknown): string => JSON.stringify(x)

type Reads = {vars: Set<string>, maps: Set<string>, flags: Set<string>}

function collectReads(t: E | C, out: Reads = {vars: new Set(), maps: new Set(), flags: new Set()}): Reads {
  switch (t.op) {
    case 'var': out.vars.add(t.name); break
    case 'const': break
    case 'get': out.maps.add(t.map); collectReads(t.key, out); break
    case 'flag': out.flags.add(t.name); break
    case 'all': {
      const bound = new Set([t.key, ...(t.keys ?? [])])
      const inner = collectReads(t.c)
      for (const name of inner.vars) if (!bound.has(name)) out.vars.add(name)
      for (const mp of inner.maps) out.maps.add(mp)
      for (const fl of inner.flags) out.flags.add(fl)
      break
    }
    case 'not': collectReads(t.x, out); break
    case 'and': case 'or': for (const y of t.xs) collectReads(y, out); break
    case 'mul': case 'proj': collectReads(t.a, out); break
    case 'if': collectReads(t.c, out); collectReads(t.then, out); collectReads(t.else, out); break
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
    case '<': case '<=': case '=':
      collectReads(t.a, out); collectReads(t.b, out); break
  }
  return out
}

const readsVar = (t: E | C, name: string): boolean => collectReads(t).vars.has(name)

function unquantifiedE(e: E): boolean {
  switch (e.op) {
    case 'var': case 'const': return true
    case 'get': return unquantifiedE(e.key)
    case 'mul': case 'proj': return unquantifiedE(e.a)
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
      return unquantifiedE(e.a) && unquantifiedE(e.b)
    case 'if': return unquantifiedC(e.c) && unquantifiedE(e.then) && unquantifiedE(e.else)
  }
}

function unquantifiedC(c: C): boolean {
  switch (c.op) {
    case 'all': return false
    case 'flag': return true
    case 'not': return unquantifiedC(c.x)
    case 'and': case 'or': return c.xs.every(unquantifiedC)
    case '<': case '<=': case '=': return unquantifiedE(c.a) && unquantifiedE(c.b)
  }
}

function naturalE(e: E): boolean {
  switch (e.op) {
    case 'var': return true
    case 'const': return Number.isInteger(e.value) && e.value >= 0
    case 'get': return naturalE(e.key)
    case 'mul': return Number.isInteger(e.k) && e.k >= 0 && naturalE(e.a)
    case 'proj': return naturalE(e.a)
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
      return naturalE(e.a) && naturalE(e.b)
    case 'if': return naturalC(e.c) && naturalE(e.then) && naturalE(e.else)
  }
}

function naturalC(c: C): boolean {
  switch (c.op) {
    case 'all': return false
    case 'flag': return true
    case 'not': return naturalC(c.x)
    case 'and': case 'or': return c.xs.every(naturalC)
    case '<': case '<=': case '=': return naturalE(c.a) && naturalE(c.b)
  }
}

function substFlagsE(e: E, flags: Record<string, C>): E {
  switch (e.op) {
    case 'var': case 'const': return e
    case 'get': return {...e, key: substFlagsE(e.key, flags)}
    case 'mul': case 'proj': return {...e, a: substFlagsE(e.a, flags)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup':
      return {...e, a: substFlagsE(e.a, flags), b: substFlagsE(e.b, flags)}
    case 'if': return {...e, c: substFlagsC(e.c, flags), then: substFlagsE(e.then, flags), else: substFlagsE(e.else, flags)}
  }
}

function substFlagsC(c: C, flags: Record<string, C>): C {
  switch (c.op) {
    case 'flag': return Object.hasOwn(flags, c.name) ? flags[c.name]! : c
    case 'all': return c
    case 'not': return {op: 'not', x: substFlagsC(c.x, flags)}
    case 'and': case 'or': return {op: c.op, xs: c.xs.map(x => substFlagsC(x, flags))}
    case '<': case '<=': case '=': return {...c, a: substFlagsE(c.a, flags), b: substFlagsE(c.b, flags)}
  }
}

function inlineFlagsMap(m: Machine): Record<string, C> {
  const out: Record<string, C> = Object.create(null)
  for (const [f, c] of Object.entries(m.step.flags ?? {})) {
    out[f] = c.op === 'all'
      ? {op: '=', a: {op: 'var', name: `?${f}`}, b: {op: 'const', value: 1}}
      : substFlagsC(c, out)
  }
  return out
}

const mapsInTerm = (term: E): string[] => [...collectReads(term).maps]

const negateC = (c: C): C => (c.op === 'not' ? c.x : {op: 'not', x: c})

function conjunctsOf(c: C): C[] {
  if (keyOf(c) === keyOf(TRUE_C)) return []
  return c.op === 'and' ? c.xs.flatMap(conjunctsOf) : [c]
}

function andAll(cs: C[]): C {
  const flat: C[] = []
  const seen = new Set<string>()
  for (const c of cs) {
    for (const part of conjunctsOf(c)) {
      const k = keyOf(part)
      if (!seen.has(k)) { seen.add(k); flat.push(part) }
    }
  }
  if (!flat.length) return TRUE_C
  return flat.length === 1 ? flat[0]! : {op: 'and', xs: flat}
}

function constOf(e: E, boundKey: string): number | undefined {
  switch (e.op) {
    case 'const': return Number.isInteger(e.value) && e.value >= 0 ? e.value : undefined
    case 'var': case 'get': case 'tup': case 'proj': return undefined
    case 'mul': {
      if (e.k === 0) return 0
      const a = constOf(e.a, boundKey)
      return a === undefined ? undefined : e.k * a
    }
    case 'add': {
      const a = constOf(e.a, boundKey), b = constOf(e.b, boundKey)
      return a === undefined || b === undefined ? undefined : a + b
    }
    case 'sub': {
      const a = constOf(e.a, boundKey), b = constOf(e.b, boundKey)
      if (a === 0) return 0
      return a === undefined || b === undefined ? undefined : Math.max(0, a - b)
    }
    case 'min': {
      const a = constOf(e.a, boundKey), b = constOf(e.b, boundKey)
      if (a === 0 || b === 0) return 0
      return a === undefined || b === undefined ? undefined : Math.min(a, b)
    }
    case 'max': {
      const a = constOf(e.a, boundKey), b = constOf(e.b, boundKey)
      return a === undefined || b === undefined ? undefined : Math.max(a, b)
    }
    case 'prod': {
      const a = constOf(e.a, boundKey), b = constOf(e.b, boundKey)
      if (a === 0 || b === 0) return 0
      return a === undefined || b === undefined ? undefined : a * b
    }
    case 'if': {
      if (readsVar(e.c, boundKey)) {
        const t = constOf(e.then, boundKey), f = constOf(e.else, boundKey)
        return t !== undefined && t === f ? t : undefined
      }
      const t = constOf(e.then, boundKey), f = constOf(e.else, boundKey)
      return t !== undefined && t === f ? t : undefined
    }
  }
}

type ConstBranch = {cond: C, value: number}

function evalConstCond(c: C): boolean | undefined {
  switch (c.op) {
    case '<': return c.a.op === 'const' && c.b.op === 'const' ? c.a.value < c.b.value : undefined
    case '<=': return c.a.op === 'const' && c.b.op === 'const' ? c.a.value <= c.b.value : undefined
    case '=': return c.a.op === 'const' && c.b.op === 'const' ? c.a.value === c.b.value : undefined
    case 'not': case 'and': case 'or': case 'flag': case 'all': return undefined
  }
}

// Evaluate `c` assuming every condition in `assumed` is true (short-circuiting past key-dependent
// branches whenever boolean structure determines the truth value, as `bool`'s `choose(clears, no, ...)`
// produces `(clears ∧ 0<0) ∨ (¬clears ∧ rest(k))`).
function evalCondUnder(c: C, assumed: ReadonlySet<string>, negated: ReadonlySet<string>): boolean | undefined {
  const kConst = evalConstCond(c)
  if (kConst !== undefined) return kConst
  const k = keyOf(c)
  if (assumed.has(k)) return true
  if (negated.has(k)) return false
  switch (c.op) {
    case 'not': {
      const v = evalCondUnder(c.x, assumed, negated)
      return v === undefined ? undefined : !v
    }
    case 'and': {
      let allTrue = true
      for (const x of c.xs) {
        const v = evalCondUnder(x, assumed, negated)
        if (v === false) return false
        if (v === undefined) allTrue = false
      }
      return allTrue ? true : undefined
    }
    case 'or': {
      let allFalse = true
      for (const x of c.xs) {
        const v = evalCondUnder(x, assumed, negated)
        if (v === true) return true
        if (v === undefined) allFalse = false
      }
      return allFalse ? false : undefined
    }
    case '<': case '<=': case '=': case 'flag': case 'all': return undefined
  }
}

// Collect atomic key-free guards (flags or comparisons) appearing under boolean connectives of `c`.
function keyFreeBooleanGuards(c: C, boundKey: string, out: Map<string, C>, depth = 0): void {
  if (depth > 8 || out.size >= 12) return
  if (c.op === 'not') { keyFreeBooleanGuards(c.x, boundKey, out, depth + 1); return }
  if (c.op === 'and' || c.op === 'or') {
    for (const x of c.xs) keyFreeBooleanGuards(x, boundKey, out, depth + 1)
    return
  }
  if (!readsVar(c, boundKey) && evalConstCond(c) === undefined) out.set(keyOf(c), c)
}

function extractConstBranches(e: E, boundKey: string, path: C[] = [], depth = 0): ConstBranch[] {
  if (depth > 24) return []
  const k = constOf(e, boundKey)
  if (k !== undefined) return [{cond: andAll(path), value: k}]
  if (e.op !== 'if') return []
  if (!readsVar(e.c, boundKey)) {
    const thenBranches = extractConstBranches(e.then, boundKey, [...path, e.c], depth + 1)
    const elseBranches = extractConstBranches(e.else, boundKey, [...path, negateC(e.c)], depth + 1)
    return [...thenBranches, ...elseBranches]
  }
  // Key-dependent `if` condition: only extract a key-free guard `g` that forces `e.c` to a
  // definite boolean value independently of `boundKey` (e.g. `bool`'s `choose(clears, no, ...)`).
  const atoms = new Map<string, C>()
  keyFreeBooleanGuards(e.c, boundKey, atoms)
  const out: ConstBranch[] = []
  for (const atom of atoms.values()) {
    for (const g of [atom, negateC(atom)]) {
      const assumed = new Set([keyOf(g)]), negated = new Set([keyOf(negateC(g))])
      const v = evalCondUnder(e.c, assumed, negated)
      if (v === true) out.push(...extractConstBranches(e.then, boundKey, [...path, g], depth + 1))
      else if (v === false) out.push(...extractConstBranches(e.else, boundKey, [...path, g], depth + 1))
    }
  }
  return out
}

// Evaluate a sum term at `sum.key` given constant post-step values for a subset of its maps.
// Returns a concrete natural when determined independently of all unknown maps, else undefined.
function evalTermKnown(e: E, sumKey: string, known: ReadonlyMap<string, number>): number | undefined {
  switch (e.op) {
    case 'const': return e.value
    case 'var': return undefined
    case 'get':
      return e.key.op === 'var' && e.key.name === sumKey ? known.get(e.map) : undefined
    case 'mul': {
      if (e.k === 0) return 0
      const a = evalTermKnown(e.a, sumKey, known)
      return a === undefined ? undefined : e.k * a
    }
    case 'add': {
      const a = evalTermKnown(e.a, sumKey, known), b = evalTermKnown(e.b, sumKey, known)
      return a === undefined || b === undefined ? undefined : a + b
    }
    case 'sub': {
      const a = evalTermKnown(e.a, sumKey, known)
      if (a === 0) return 0
      const b = evalTermKnown(e.b, sumKey, known)
      return a === undefined || b === undefined ? undefined : Math.max(0, a - b)
    }
    case 'min': {
      const a = evalTermKnown(e.a, sumKey, known), b = evalTermKnown(e.b, sumKey, known)
      if (a === 0 || b === 0) return 0
      return a === undefined || b === undefined ? undefined : Math.min(a, b)
    }
    case 'max': {
      const a = evalTermKnown(e.a, sumKey, known), b = evalTermKnown(e.b, sumKey, known)
      return a === undefined || b === undefined ? undefined : Math.max(a, b)
    }
    case 'prod': {
      const a = evalTermKnown(e.a, sumKey, known), b = evalTermKnown(e.b, sumKey, known)
      if (a === 0 || b === 0) return 0
      return a === undefined || b === undefined ? undefined : a * b
    }
    case 'if': {
      const c = evalCondKnown(e.c, sumKey, known)
      if (c === true) return evalTermKnown(e.then, sumKey, known)
      if (c === false) return evalTermKnown(e.else, sumKey, known)
      const t = evalTermKnown(e.then, sumKey, known), f = evalTermKnown(e.else, sumKey, known)
      return t !== undefined && t === f ? t : undefined
    }
    case 'tup': case 'proj': return undefined
  }
}

function evalCondKnown(c: C, sumKey: string, known: ReadonlyMap<string, number>): boolean | undefined {
  switch (c.op) {
    case '<': {
      const a = evalTermKnown(c.a, sumKey, known), b = evalTermKnown(c.b, sumKey, known)
      if (b === 0) return false
      return a === undefined || b === undefined ? undefined : a < b
    }
    case '<=': {
      const a = evalTermKnown(c.a, sumKey, known), b = evalTermKnown(c.b, sumKey, known)
      if (a === 0) return true
      return a === undefined || b === undefined ? undefined : a <= b
    }
    case '=': {
      const a = evalTermKnown(c.a, sumKey, known), b = evalTermKnown(c.b, sumKey, known)
      return a === undefined || b === undefined ? undefined : a === b
    }
    case 'not': {
      const v = evalCondKnown(c.x, sumKey, known)
      return v === undefined ? undefined : !v
    }
    case 'and': {
      let allTrue = true
      for (const x of c.xs) {
        const v = evalCondKnown(x, sumKey, known)
        if (v === false) return false
        if (v === undefined) allTrue = false
      }
      return allTrue ? true : undefined
    }
    case 'or': {
      let allFalse = true
      for (const x of c.xs) {
        const v = evalCondKnown(x, sumKey, known)
        if (v === true) return true
        if (v === undefined) allFalse = false
      }
      return allFalse ? false : undefined
    }
    case 'flag': case 'all': return undefined
  }
}

// Syntactic check that `premise` entails `target`: every conjunct of `target` appears in `premise`.
function entailsSyntactic(premise: C, target: C): boolean {
  const tParts = conjunctsOf(target)
  if (!tParts.length) return true
  const pSet = new Set(conjunctsOf(premise).map(keyOf))
  return tParts.every(p => pSet.has(keyOf(p)))
}

// Simplify disjunctions of guards: drop redundant `¬g` conjuncts when `g` is itself a disjunct
// (e.g. `r1 ∨ (¬r1 ∧ r2)` simplifies to `r1 ∨ r2`).
function simplifyDisjunction(guards: C[]): C {
  const uniq: C[] = []
  const seen = new Set<string>()
  for (const g of guards) {
    if (keyOf(g) === keyOf(TRUE_C)) return TRUE_C
    const k = keyOf(g)
    if (!seen.has(k)) { seen.add(k); uniq.push(g) }
  }
  const negOfSingle = new Set(uniq.map(g => keyOf(negateC(g))))
  const simplified: C[] = []
  const seen2 = new Set<string>()
  for (const g of uniq) {
    const parts = conjunctsOf(g)
    const stripped = parts.length > 1 ? parts.filter(p => !negOfSingle.has(keyOf(p))) : parts
    const next = stripped.length ? andAll(stripped) : g
    const k = keyOf(next)
    if (!seen2.has(k)) { seen2.add(k); simplified.push(next) }
  }
  return simplified.length === 1 ? simplified[0]! : {op: 'or', xs: simplified}
}

/**
 * Checks whether `guard` meets the syntactic side conditions of a sum reset guard on `m`:
 * - unquantified and natural (no negative constants or factors);
 * - references only flags declared on `m`;
 * - reads no key variable (`sum.key`, `x$S`, or any `each` write's bound key), even after flag inlining;
 * - reads only variables in scope on `m`;
 * - reads no map aggregated by `sum.term`, even through inlined plain flags.
 */
export function isAdmissibleResetGuard(m: Machine, sum: Sum, guard: C, sumName?: string): boolean {
  if (!unquantifiedC(guard) || !naturalC(guard)) return false
  const flags = m.step.flags ?? {}
  const raw = collectReads(guard)
  for (const f of raw.flags) if (!Object.hasOwn(flags, f)) return false
  const inlined = substFlagsC(guard, inlineFlagsMap(m))
  const inl = collectReads(inlined)
  const forbidden = new Set<string>([sum.key])
  if (sumName) forbidden.add(sumParts(sumName).x)
  for (const w of Object.values(m.step.maps ?? {})) if ('each' in w) forbidden.add(w.each)
  for (const v of raw.vars) if (forbidden.has(v)) return false
  for (const v of inl.vars) if (forbidden.has(v)) return false
  const qVars = new Set(Object.entries(flags).filter(([, c]) => c.op === 'all').map(([f]) => `?${f}`))
  const allowedVars = new Set([
    ...m.params,
    ...m.inputs,
    ...Object.keys(m.state).filter(n => !Object.hasOwn(m.sums ?? {}, n)),
    ...qVars,
  ])
  for (const v of inl.vars) if (!allowedVars.has(v)) return false
  const summedMaps = new Set(mapsInTerm(sum.term))
  for (const mp of inl.maps) if (summedMaps.has(mp)) return false
  return true
}

/**
 * Extracts a candidate key-independent reset guard `R` for `sum` from the `each` writes of `m`,
 * or returns `undefined` when no summed map uses an `each` write or no admissible guard drives
 * `sum.term` to 0 at every key.
 */
export function extractSumReset(m: Machine, sum: Sum, sumName?: string): C | undefined {
  const read = mapsInTerm(sum.term)
  if (!read.length) return undefined
  const eachMaps = read.filter(mp => {
    const w = m.step.maps?.[mp]
    return !!w && 'each' in w
  })
  if (!eachMaps.length) return undefined

  const perMap = new Map<string, ConstBranch[]>()
  for (const mp of eachMaps) {
    const w = m.step.maps![mp]!
    if (!('each' in w)) continue
    const branches = extractConstBranches(w.value, w.each)
      .filter(b => isAdmissibleResetGuard(m, sum, b.cond, sumName))
    perMap.set(mp, branches)
  }

  // Known post-step map values implied by a candidate guard `g`.
  const knownUnder = (g: C): Map<string, number> => {
    const known = new Map<string, number>()
    for (const [mp, branches] of perMap) {
      for (const b of branches) {
        if (entailsSyntactic(g, b.cond)) { known.set(mp, b.value); break }
      }
    }
    return known
  }

  // Gather all distinct atomic branch guards across `each`-written summed maps.
  const candidates: C[] = []
  const seenCand = new Set<string>()
  const addCand = (c: C) => {
    const k = keyOf(c)
    if (!seenCand.has(k)) { seenCand.add(k); candidates.push(c) }
  }
  for (const branches of perMap.values()) for (const b of branches) addCand(b.cond)

  const zeroGuards: C[] = []
  for (const g of candidates) {
    if (evalTermKnown(sum.term, sum.key, knownUnder(g)) === 0) zeroGuards.push(g)
  }

  // Multi-map fallback (e.g. M1[k] + M2[k] where M1 resets on r1 and M2 resets on r2):
  // test bounded conjunctions taking one branch per each-written map.
  if (!zeroGuards.length && eachMaps.length > 1) {
    const lists = eachMaps.map(mp => perMap.get(mp) ?? [])
    if (lists.every(l => l.length > 0)) {
      let combos: C[][] = [[]]
      for (const l of lists) {
        combos = combos.flatMap(prefix => l.map(b => [...prefix, b.cond])).slice(0, 16)
      }
      for (const combo of combos) {
        const g = andAll(combo)
        if (isAdmissibleResetGuard(m, sum, g, sumName) && evalTermKnown(sum.term, sum.key, knownUnder(g)) === 0) {
          zeroGuards.push(g)
        }
      }
    }
  }

  if (!zeroGuards.length) return undefined
  return simplifyDisjunction(zeroGuards)
}

/** Extracts candidate reset guards for every sum declared on `m`. */
export function sumResets(m: Machine): Record<string, C> {
  const out: Record<string, C> = Object.create(null)
  for (const [name, sum] of Object.entries(m.sums ?? {})) {
    const reset = extractSumReset(m, sum, name)
    if (reset) out[name] = reset
  }
  return out
}
