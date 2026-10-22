// Invariants nobody wrote: a law that holds but isn't inductive, proven with laws the search finds. Nothing here is
// trusted; what it finds is proven by the kernel with the rule's own laws, as laws of the same rule.
//   - runs: random runs from the start (params and requests by their kinds, the assumption met) give reachable states
//   - candidates: linear forms Σ c·v ≤ d over the state and the params (an integer as its value, its two naturals
//     together), up to three terms with small coefficients and the rule's own constants, each d the largest value the
//     runs reached (and the rule's constants just above it); the same forms where a yes/no, a choice or a small natural
//     holds one value (locked is 0 → …), and a choice's value no run reached as unreachable; and laws about every key
//     of the maps: forms over the cells at one key (and a scalar), at every key or every key but a scalar's (k = owner
//     or …), and where a cell holds one value
//   - Houdini on the runs' neighbors: a reached state moved a little that every candidate alive and every law allows,
//     stepped; a candidate its step breaks is in no inductive set of them, so it is dropped
//   - the kernel: the laws with the candidates chosen so far, proven one law at a time; when a goal is stuck at a step,
//     its witness is a counterexample to induction, so the candidate that rules it out (and the most of those seen) is
//     added; a chosen candidate that nothing supports, or that makes a proof slow, is dropped; the set proven as a whole
//     is the answer, after each chosen candidate the proof doesn't need is taken out again
import {quietly} from './cyclic.ts'
import {type C, type E, type Law, type Machine, type Request, type State, any, atMost, divisorsIn, evalC, get, interpret, machineTerms, modName, n, not, plus, same, times, withArithmetic, x} from './machine.ts'
import {type StepLaw, type Verdict, proveRule, proveSteps} from './dsl.ts'
import {allowed, watch} from './watch.ts'
import {proveLaw, proveLaws, proveStepLaws, withDeadline} from '../kernel/prove.ts'

type AnyRule = Parameters<typeof proveRule>[0]
type Env = Record<string, number>
type Rand = (k: number) => number

export type InferOptions = {
  ms?: number // the whole search's time (20 s)
  runsMs?: number // the random runs' share (500 ms)
  seen?: State[] // reachable states the caller already has (of a rule with no params), beside the runs
  constants?: number[] // more constants for the coefficients and bounds
  maxCandidates?: number // past this many, the search keeps the simplest (60,000)
  first?: Verdict // the laws' verdict alone, when the caller has it already
  progress?: (phase: string, info: Record<string, number | string>) => void // told as each phase ends
  existentials?: boolean // congruences as "there exists" (∃k. v = c·k + r), where the runs keep v's remainder (true)
  remainders?: boolean // remainders (v mod k = r, a guard where only some runs keep one) where the runs keep one (true); with false, congruences instead (`existentials`)
}
// What was found: each law as a Law (pass it with the rule's laws), how it reads, and for a rule, the builder call
// that states it (`r.law(...)`), to paste.
export type Found = {law: Law, text: string, source?: string}
export type Inferred = Verdict & {found: Found[], stats: {samples: number, candidates: number, alive: number, proofs: number, ms: number}}

// An atom: a value the forms read, the naturals it is made of with their signs (an integer is pos − neg); a cell atom
// is a map's cell at the law's key (its parts are maps).
type Atom = {name: string, parts: [string, 1 | -1][], param: boolean, int: boolean, cell: boolean}
type Guard = {atom: number, value: number} | {keyNot: number}
// `when`: a linear condition the form holds under (Σ c·v ≤ d over scalars), beside its guard; the search makes such forms
// from a counterexample to induction no candidate rules out.
// `mod`: the form is a remainder, (Σ c·v) mod k = r (d unused). `cong`: a congruence, ∃k. Σ c·v = mod·k + rest
// (core/exists.ts: proven through a witness, a ghost the kernel's counterexamples choose), k a natural or, over an
// integer, an integer; the same claim, made only where remainders are off (InferOptions.remainders).
type Form = {coef: [number, number][], d: number, cells: boolean, guard?: Guard, when?: {coef: [number, number][], d: number}, unreachable?: {atom: number, value: number}, mod?: {k: number, r: number}, cong?: {mod: number, rest: number}, size: number}

const KEY = 'key$found', AT = '@', K = '#', SOME = 'k$found'
const seeded = (seed: number): Rand => { let s = seed; return k => { s = (s * 1103515245 + 12345) % 2 ** 31; return Math.floor(s / 2 ** 31 * k) } }
const isRule = (t: AnyRule | Machine): t is AnyRule => typeof (t as AnyRule).kindsOfState === 'function'
const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b))

// The constants a machine's expressions hold, and the factors it multiplies by.
function constantsOf(m: Machine, laws: Law[]): number[] {
  const out = new Set<number>()
  const e = (t: E): void => {
    switch (t.op) {
      case 'const': out.add(t.value); break
      case 'var': break
      case 'mul': out.add(t.k); e(t.a); break
      case 'add': case 'sub': case 'min': case 'max': case 'prod': e(t.a); e(t.b); break
      case 'if': c(t.c); e(t.then); e(t.else); break
      case 'get': e(t.key); break
    }
  }
  const c = (t: C): void => {
    switch (t.op) {
      case '<': case '<=': case '=': e(t.a); e(t.b); break
      case 'and': case 'or': t.xs.forEach(c); break
      case 'not': c(t.x); break
      case 'flag': break
      case 'all': c(t.c); break
    }
  }
  Object.values(m.state).forEach(e)
  Object.values(m.step.state ?? {}).forEach(e)
  Object.values(m.step.flags ?? {}).forEach(c)
  for (const w of Object.values(m.step.maps ?? {})) { if ('key' in w) e(w.key); e(w.value) }
  if (m.assume) c(m.assume)
  if (m.pre) c(m.pre)
  laws.forEach(l => c(l.holds))
  return [...out].filter(k => Number.isSafeInteger(k) && Math.abs(k) <= 1e6)
}

// A cell's key as the kernel names it (kernel.ts keyOf): `name:coef` parts joined by ',', '1' the constant.
const keyValue = (cell: string, w: Record<string, number>): number | undefined => {
  const inner = cell.slice(cell.indexOf('[') + 1, -1)
  if (inner.includes('[')) return undefined
  let value = 0
  for (const part of inner.split(',').filter(Boolean)) {
    const at = part.lastIndexOf(':'), name = part.slice(0, at), coef = Number(part.slice(at + 1))
    if (name === '1') value += coef
    else if (name in w) value += coef * w[name]!
    else return undefined
  }
  return value
}

export function inferLaws(target: AnyRule | Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: InferOptions = {}): Inferred {
  return quietly(() => withDeadline(performance.now() + (opts.ms ?? 20000), () => inferLawsSearch(target, laws, stepLaws, opts)))
}
function inferLawsSearch(target: AnyRule | Machine, laws: Law[], stepLaws: StepLaw[] = [], opts: InferOptions = {}): Inferred {
  const t0 = performance.now(), until = t0 + (opts.ms ?? 20000), rule = isRule(target) ? target : undefined
  if (rule) { const ks = divisorsIn([...laws, ...stepLaws] as never); if (ks.size) rule.dividesBy(...ks) }
  const m = rule ? rule.machine : target as Machine
  let proofs = 0
  // The rule (or machine) the kernel proves the candidates with: once a remainder is among them, one that declares
  // div$k and mod$k for its divisors (rule.withDivisors leaves the caller's rule as it was until a found law needs them).
  let searchRule = rule, mm = m
  const prove = (ls: Law[]): Verdict => {
    proofs++
    if (searchRule) return stepLaws.length ? proveSteps(searchRule, ls, stepLaws, {search: false}) : proveRule(searchRule, ls, {search: false})
    const out = stepLaws.length ? proveStepLaws(mm, ls, stepLaws) : proveLaws(mm, ls)
    return {proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck, ...(out.failed.witness ? {witness: out.failed.witness} : {}), ...(out.failed.why ? {why: out.failed.why} : {})} : {})}
  }
  const stats = (samples: number, candidates: number, alive: number) => ({samples, candidates, alive, proofs, ms: Math.round(performance.now() - t0)})
  const first = opts.first ?? prove(laws)
  if ((first.proven && first.checked) || first.run) return {...first, found: [], stats: stats(0, 0, 0)}

  // --- runs ------------------------------------------------------------------------------------------------------------
  const run = interpret(m), rand = seeded(17), kinds = rule ? rule.kindsOfState() : []
  const given = rule ? [...rule.kindLaws().filter(k => !laws.some(l => l.name === k.name)), ...laws] : laws
  const randomParams = (bound: number): Env => (rule ? rule.randomParams(rand, bound) : Object.fromEntries(m.params.map(p => [p, rand(bound + 1)])))
  const randomInput = (params: Env, bound: number): Request => (rule ? rule.randomInput(rand, bound, params)
    : {...Object.fromEntries(m.inputs.map(i => [i, rand(bound + 1)])), ...Object.fromEntries((m.inputMaps ?? []).map(i => [i, new Map<number, number>()]))})
  type Sample = {params: Env, st: State}
  const samples: Sample[] = [], cap = 3000
  const keep = (s: Sample) => { if (samples.length < cap) samples.push(s); else if (rand(4) === 0) samples[rand(cap)] = s }
  for (const st of opts.seen ?? []) if (!m.params.length) keep({params: {}, st})
  const mapsText = (st: State) => JSON.stringify(Object.values(st.maps).map(c => [...c]))
  const runsUntil = Math.min(until, performance.now() + (opts.runsMs ?? 500))
  // (an assumption with "there exists", a value the request brings, may admit no request at a small bound, a multiple
  // of 5 but 0, say: a trial whose steps moved nothing doubles the bound at once)
  const skolems = m.inputs.some(i => i.startsWith('some$a'))
  for (let trial = 0, bound = 2, stuck = false; performance.now() < runsUntil; trial++, bound = trial % 20 === 0 || stuck ? (bound >= 1024 ? 2 : bound * 2) : bound) {
    stuck = false
    const params = randomParams(bound)
    if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) continue
    let st: State
    try { st = run.init(params) } catch { continue }
    keep({params, st})
    let took = 0
    for (let d = 0, tries = 0; d < 40 && tries < 200; tries++) {
      const input = randomInput(params, bound)
      let next: State
      try { if (!allowed(m, run, params, st, input)) continue; next = run.step(params, st, input) } catch { break }
      d++
      if (JSON.stringify(next.scalars) !== JSON.stringify(st.scalars) || mapsText(next) !== mapsText(st)) { keep({params, st: next}); took++ }
      st = next
    }
    stuck = skolems && took === 0
  }

  opts.progress?.('runs', {samples: samples.length})

  // --- atoms and rows --------------------------------------------------------------------------------------------------
  const scalars = Object.keys(m.state), stateSet = new Set(scalars), mapNames = Object.keys(m.maps ?? {}), mapSet = new Set(mapNames)
  const atoms: Atom[] = []
  const add = (name: string, has: (p: string) => boolean, param: boolean, cell: boolean) => {
    if (name.endsWith('$neg') && has(name.slice(0, -4))) return
    const neg = `${name}$neg`, int = has(neg)
    atoms.push({name: cell ? `${name}[k]` : name, parts: int ? [[name, 1], [neg, -1]] : [[name, 1]], param, int, cell})
  }
  for (const name of scalars) add(name, p => stateSet.has(p), false, false)
  for (const name of m.params) add(name, p => m.params.includes(p), true, false)
  for (const name of mapNames) add(name, p => mapSet.has(p), false, true)
  const A = atoms.length, cellAtoms = atoms.flatMap((a, i) => (a.cell ? [i] : []))
  const valueOf = (a: Atom, env: Env) => { let s = 0; for (const [p, sign] of a.parts) s += sign * (env[a.cell ? AT + p : p] ?? 0); return s }
  const cellOf = (st: State, map: string, key: number) => st.maps[map]?.get(key) ?? st.defaults?.[map] ?? m.maps![map]!
  // The scalar rows (one per state reached), and the cell rows (one per state and key a map holds, and one fresh key).
  const keysIn = (st: State) => { const ks = new Set<number>(); for (const c of Object.values(st.maps)) for (const k of c.keys()) ks.add(k); return [...ks] }
  const cellRows = (params: Env, st: State): Env[] => {
    if (!mapNames.length) return []
    const ks = keysIn(st), fresh = ks.length ? Math.max(...ks) + 1 : 0
    return [...ks, fresh].map(k => ({...params, ...st.scalars, [K]: k, ...Object.fromEntries(mapNames.map(mp => [AT + mp, cellOf(st, mp, k)]))}))
  }
  const rowsS = samples.map(s => ({...s.params, ...s.st.scalars}))
  const rowsK: Env[] = []
  for (const s of samples) { if (rowsK.length > 6000) break; rowsK.push(...cellRows(s.params, s.st)) }
  const valsS = atoms.map(a => Float64Array.from(rowsS, r => valueOf(a, r))), valsK = atoms.map(a => Float64Array.from(rowsK, r => valueOf(a, r)))
  const kindOf = new Map(kinds.map(([name, k]) => [name, k]))
  // Modes: a yes/no, a choice, or a state natural (or cell) no run took past a few values.
  type Mode = {atom: number, values: number[], choice?: readonly string[], bool?: boolean}
  const modes: Mode[] = []
  atoms.forEach((a, i) => {
    if (a.param || a.int) return
    const k = a.cell ? undefined : kindOf.get(a.name), seenValues = [...new Set(a.cell ? valsK[i]! : valsS[i]!)].sort((p, q) => p - q)
    const decoded = k?.vars(a.name).length === 1 ? k.decode(a.name, {[a.name]: 0}) : undefined
    const values = (k as unknown as {values?: readonly string[]} | undefined)?.values
    if (typeof decoded === 'boolean') modes.push({atom: i, values: [0, 1], bool: true})
    else if (typeof decoded === 'string' && values) modes.push({atom: i, values: values.map((_, j) => j), choice: values})
    else if (!k && seenValues.length && seenValues.length <= 4 && seenValues.every(v => v <= 8)) modes.push({atom: i, values: seenValues})
  })
  const modeOf = (i: number) => modes.find(mo => mo.atom === i)

  // --- candidates ----------------------------------------------------------------------------------------------------
  const consts = [...new Set([...constantsOf(m, laws), ...(opts.constants ?? [])].map(Math.abs))].filter(k => k > 0).sort((p, q) => p - q)
  const mags = [...new Set([1, 2, 3, ...consts.filter(k => k > 3 && k <= 1000).slice(0, 4)])]
  const bounds = [...new Set([...consts, ...consts.flatMap(a => consts.map(b => a * b)), ...consts.flatMap(a => consts.map(b => a + b))].flatMap(k => [k, -k])), 0].sort((p, q) => p - q)
  const maxCandidates = opts.maxCandidates ?? 60000
  // The shapes: every coefficient vector over up to three atoms, coprime; a scalar form reads a state variable, a
  // cell form a cell (and at most one scalar).
  const shapes: {coef: [number, number][], cells: boolean}[] = []
  const pick = (terms: number, ms: number[], pool: number[], ok: (acc: [number, number][]) => boolean, cells: boolean) => {
    const cs = ms.flatMap(k => [k, -k])
    const go = (from: number, acc: [number, number][]) => {
      if (shapes.length > maxCandidates) return
      if (acc.length === terms) { if (ok(acc) && acc.reduce((g, [, c]) => gcd(g, c), 0) === 1) shapes.push({coef: [...acc], cells}); return }
      for (let i = from; i < pool.length; i++) for (const c of cs) go(i + 1, [...acc, [pool[i]!, c]])
    }
    go(0, [])
  }
  const choose = (k: number, of: number) => { let r = 1; for (let i = 0; i < k; i++) r = r * (of - i) / (i + 1); return r }
  // A choice's index orders its values arbitrarily: it is a guard, or alone (a bound on it reads as the values it
  // allows), never a term among others.
  const plain = atoms.flatMap((a, i) => (a.cell ? [] : [i])), terms = plain.filter(i => !modeOf(i)?.choice), P = terms.length
  const scalarOk = (acc: [number, number][]) => acc.some(([i]) => !atoms[i]!.param)
  pick(1, [1], plain, scalarOk, false)
  pick(2, choose(2, P) * 4 * mags.length ** 2 <= maxCandidates / 4 ? mags : [1], terms, scalarOk, false)
  if (choose(3, P) * 8 * mags.length ** 3 <= maxCandidates / 2) pick(3, mags, terms, scalarOk, false)
  else if (choose(3, P) * 8 <= maxCandidates / 2) pick(3, [1], terms, scalarOk, false)
  if (cellAtoms.length) {
    const all = atoms.flatMap((_, i) => (modeOf(i)?.choice ? [] : [i])), cellOk = (acc: [number, number][]) => acc.some(([i]) => atoms[i]!.cell) && acc.filter(([i]) => !atoms[i]!.cell).length <= 1
    pick(1, [1], cellAtoms, () => true, true)
    pick(2, [1], all, cellOk, true)
    if (choose(3, A) * 8 <= maxCandidates / 4) pick(3, [1], all, acc => cellOk(acc) && acc.filter(([i]) => atoms[i]!.cell).length >= 2, true)
  }
  const sizeOf = (coef: [number, number][]) => coef.length * 100 + coef.reduce((s, [, c]) => s + Math.abs(c), 0)
  const forms: Form[] = []
  const NS = rowsS.length, NK = rowsK.length
  const at = (coef: [number, number][], vals: Float64Array[], j: number) => { let s = 0; for (const [i, c] of coef) s += c * vals[i]![j]!; return s }
  const keyNots = plain.filter(i => !atoms[i]!.param && !atoms[i]!.int)
  // The guards: the choices first, then yes/nos, then small naturals, at most eight; each shape's largest value per
  // guard in one pass over (at most 1,500 of) the rows. Building candidates takes at most a quarter of the time.
  const guards = [...modes].sort((p, q) => Number(!!q.choice) - Number(!!p.choice) || Number(!!q.bool) - Number(!!p.bool)).slice(0, 8)
  const strideS = Math.max(1, Math.ceil(NS / 1500)), strideK = Math.max(1, Math.ceil(NK / 1500))
  const buildUntil = Math.min(until, performance.now() + (until - performance.now()) / 4)
  for (const [n_, {coef, cells}] of shapes.entries()) {
    if (forms.length > maxCandidates || (n_ % 256 === 0 && performance.now() > buildUntil)) break
    const vals = cells ? valsK : valsS, N = cells ? NK : NS, rows = cells ? rowsK : rowsS
    let d = -Infinity
    for (let j = 0; j < N; j++) d = Math.max(d, at(coef, vals, j))
    if (!Number.isFinite(d)) continue
    forms.push({coef, d, cells, size: sizeOf(coef) + (cells ? 10 : 0)})
    // The rule's constants just above the largest value reached, a bound a run may not have hit.
    for (const b of bounds.filter(b => b > d).slice(0, 2)) forms.push({coef, d: b, cells, size: sizeOf(coef) + 1 + (cells ? 10 : 0)})
    if (coef.length > 2) continue
    const here = guards.filter(mode => !coef.some(([i]) => i === mode.atom) && (cells || !atoms[mode.atom]!.cell))
    const most = here.map(() => new Map<number, number>()), away = cells ? keyNots.map(() => -Infinity) : []
    for (let j = 0; j < N; j += cells ? strideK : strideS) {
      const value = at(coef, vals, j)
      here.forEach((mode, g) => { const v = vals[mode.atom]![j]!, b = most[g]!; b.set(v, Math.max(b.get(v) ?? -Infinity, value)) })
      // At every key but a scalar's: the largest value away from that key.
      if (cells) keyNots.forEach((s, g) => { if (rows[j]![K] !== valsK[s]![j]) away[g] = Math.max(away[g]!, value) })
    }
    here.forEach((mode, g) => { for (const [value, dv] of most[g]!) if (mode.values.includes(value) && dv < d) forms.push({coef, d: dv, cells, guard: {atom: mode.atom, value}, size: sizeOf(coef) + 50}) })
    keyNots.forEach((s, g) => { if (cells && Number.isFinite(away[g]!) && away[g]! < d) forms.push({coef, d: away[g]!, cells, guard: {keyNot: s}, size: sizeOf(coef) + 60}) })
  }
  for (const mode of modes) if (!atoms[mode.atom]!.cell) for (const value of mode.values) if (NS && !valsS[mode.atom]!.includes(value)) forms.push({coef: [], d: 0, cells: false, unreachable: {atom: mode.atom, value}, size: 1})
  // Remainders: a value, or the sum or difference of two, at one remainder by k in every run (or in every run where a
  // guard holds), k each divisor the rule and its laws read (modBy, divBy) and 2: x mod 2 = 0 for a counter that steps
  // by 2, the parity of a sum that two counters keep. No form above states one (no linear bound does).
  // The moduli: the divisors the rule and its laws read, then 2, 3, 4 and the rule's own constants up to 64 (six in all).
  const divisors = [...new Set([...[...divisorsIn([...machineTerms(m), ...laws.map(l => l.holds)])].filter(k => k >= 2 && k <= 1_000_000).sort((p, q) => p - q), 2, 3, 4, ...consts.filter(k => k > 4 && k <= 64)])].slice(0, 6)
  const modAtoms = terms.filter(i => !atoms[i]!.param && !modeOf(i)?.bool), modShapes: [number, number][][] = modAtoms.map(i => [[i, 1]])
  if (modAtoms.length * (modAtoms.length - 1) <= 2000) for (const [a, i] of modAtoms.entries()) for (const j of modAtoms.slice(a + 1)) modShapes.push([[i, 1], [j, 1]], [[i, 1], [j, -1]])
  const residue = (v: number, k: number) => ((v % k) + k) % k
  // A shape whose runs reached two values or fewer is a bound's (above), not a remainder's.
  const varied = (coef: [number, number][]) => { const vs = new Set<number>(); for (let j = 0; j < NS && vs.size < 3; j += strideS) vs.add(at(coef, valsS, j)); return vs.size >= 3 }
  for (const coef of NS && opts.remainders !== false ? modShapes.filter(varied) : []) for (const k of divisors) {
    if (forms.length > maxCandidates || performance.now() > buildUntil) break
    const all = new Set<number>(), byGuard = guards.map(() => new Map<number, Set<number>>())
    for (let j = 0; j < NS; j += strideS) {
      const r = residue(at(coef, valsS, j), k)
      all.add(r)
      guards.forEach((mode, g) => { const v = valsS[mode.atom]![j]!, b = byGuard[g]!; if (!b.has(v)) b.set(v, new Set()); b.get(v)!.add(r) })
    }
    const size = sizeOf(coef) + 30 + k
    if (all.size === 1) { forms.push({coef, d: 0, cells: false, mod: {k, r: [...all][0]!}, size}); continue }
    guards.forEach((mode, g) => { if (coef.some(([i]) => i === mode.atom)) return; for (const [value, rs] of byGuard[g]!) if (rs.size === 1 && mode.values.includes(value)) forms.push({coef, d: 0, cells: false, guard: {atom: mode.atom, value}, mod: {k, r: [...rs][0]!}, size: size + 50}) })
  }
  // Congruences, where remainders are off: a state value (or the sum or difference of two) whose every sample leaves
  // one remainder by a constant of the rule's (2 first), with at least three values reached: ∃k. v = c·k + r. The
  // remainder above says the same without a quantifier, so the kernel proves it as it stands (no witness to choose),
  // under a guard where only some runs keep it, and Lean states it with %: that is the form tried by default.
  if (opts.remainders === false && opts.existentials !== false && NS) {
    const mods = [...new Set([2, 3, 4, ...consts.filter(k => k > 4 && k <= 64)])].slice(0, 6)
    const congOf = (coef: [number, number][]) => {
      const vs = new Set<number>()
      for (let j = 0; j < NS; j++) vs.add(at(coef, valsS, j))
      if (vs.size < 3) return
      const nat = coef.every(([i, c]) => !atoms[i]!.int && c > 0), list = [...vs]
      for (const c of mods) {
        const r = ((list[0]! % c) + c) % c
        if (list.every(x => ((x % c) + c) % c === r) && (!nat || list.every(x => x >= r))) forms.push({coef, d: 0, cells: false, cong: {mod: c, rest: r}, size: sizeOf(coef) + 40 + c})
      }
    }
    const st = plain.filter(i => !atoms[i]!.param && !modeOf(i))
    for (const i of st) congOf([[i, 1]])
    if (st.length <= 24) for (const [a, i] of st.entries()) for (const j of st.slice(a + 1)) { congOf([[i, 1], [j, 1]]); congOf([[i, 1], [j, -1]]) }
  }
  opts.progress?.('candidates', {atoms: A, shapes: shapes.length, forms: forms.length})

  // --- how a form reads, and as a law ------------------------------------------------------------------------------------
  const nameOf = (i: number) => atoms[i]!.name
  const shownValue = (i: number, value: number) => { const mo = modeOf(i); return mo?.choice ? (mo.choice[value] ?? String(value)) : mo?.bool ? (value === 1 ? 'yes' : 'no') : String(value) }
  const sides = (f: Form) => {
    const term = ([i, c]: [number, number]) => `${Math.abs(c) === 1 ? '' : `${Math.abs(c)}·`}${nameOf(i)}`
    const left = f.coef.filter(([, c]) => c > 0), right = f.coef.filter(([, c]) => c < 0)
    return {left, right, l: [...left.map(term), ...(f.d < 0 ? [String(-f.d)] : [])].join(' + ') || '0', r: [...right.map(term), ...(f.d > 0 ? [String(f.d)] : [])].join(' + ') || '0'}
  }
  // A bound on a choice alone reads as the values it allows.
  const allowedValues = (f: Form) => {
    const only = f.coef.length === 1 ? modeOf(f.coef[0]![0]) : undefined
    if (!only?.choice) return undefined
    const c = f.coef[0]![1]
    return only.values.filter(v => c * v <= f.d)
  }
  const textOf = (f: Form) => {
    if (f.unreachable) return `${nameOf(f.unreachable.atom)} is never ${shownValue(f.unreachable.atom, f.unreachable.value)}`
    if (f.cong) return `∃k. ${f.coef.map(([i, c], j) => `${j ? (c > 0 ? ' + ' : ' − ') : c < 0 ? '−' : ''}${nameOf(i)}`).join('')} = ${f.cong.mod}·k${f.cong.rest ? ` + ${f.cong.rest}` : ''}`
    const {l, r} = sides(f), within = allowedValues(f)
    const body = f.mod ? `${f.coef.map(([i, c], j) => `${c < 0 ? (j ? ' − ' : '−') : j ? ' + ' : ''}${nameOf(i)}`).join('')} mod ${f.mod.k} = ${f.mod.r}` : within ? `${nameOf(f.coef[0]![0])} is ${within.map(v => shownValue(f.coef[0]![0], v)).join(' or ')}` : `${l} <= ${r}`
    const under = f.when ? (({l: wl, r: wr}) => `${wl} <= ${wr} → `)(sides({coef: f.when.coef, d: f.when.d, cells: false, size: 0})) : ''
    const guarded = !f.guard ? under + body : 'keyNot' in f.guard ? `k = ${nameOf(f.guard.keyNot)} or ${body}` : `${nameOf(f.guard.atom)} is ${shownValue(f.guard.atom, f.guard.value)} → ${under}${body}`
    return f.cells ? `every k: ${guarded}` : guarded
  }
  const sum = (es: E[]): E => es.reduce((p, q) => plus(p, q), n(0))
  // Each congruence its own witness's name (each may be a ghost of the machine).
  const someNames = new Map<Form, string>(), someName = (f: Form) => { let k = someNames.get(f); if (!k) someNames.set(f, (k = `${SOME}${someNames.size}`)); return k }
  const part = (a: Atom, p: string): E => (a.cell ? get(p, x(KEY)) : x(p))
  const partsOf = (f: Form, sign: 1 | -1): E[] => f.coef.flatMap(([i, c]) => atoms[i]!.parts.filter(([, s]) => s * c * sign > 0).map(([p]) => { const e = part(atoms[i]!, p); return Math.abs(c) === 1 ? e : times(Math.abs(c), e) }))
  // Σ c·v ≤ d over naturals: the positive parts on the left, the negative ones and d on the right (an integer's
  // negative part goes to the other side of its sign).
  const condOf = (f: Form): C => {
    // Not at a value, one-sided where it can be (less splitting for the kernel): a natural not 0 is at least 1, and a
    // yes/no or a choice not at its last value is below it (its kind's law bounds it).
    const notAt = (i: number, value: number): C => {
      const e = part(atoms[i]!, atoms[i]!.parts[0]![0]), mo = modeOf(i), lastValue = mo?.bool ? 1 : mo?.choice ? mo.choice.length - 1 : undefined
      return value === 0 ? atMost(n(1), e) : value === lastValue ? atMost(e, n(value - 1)) : not(same(e, n(value)))
    }
    if (f.unreachable) return notAt(f.unreachable.atom, f.unreachable.value)
    if (f.mod) {
      // Σ c·v = P − N over naturals (P the positive parts, N the negative ones), whose remainder by k is that of the
      // natural P + (k − 1)·N.
      const {k: dk, r} = f.mod, neg = partsOf(f, -1), e = get(modName(dk), sum([...partsOf(f, 1), ...neg.map(t => times(dk - 1, t))]))
      const body = same(e, n(r))
      return !f.guard ? body : 'keyNot' in f.guard ? any(same(x(KEY), x(atoms[f.guard.keyNot]!.parts[0]![0])), body) : any(notAt(f.guard.atom, f.guard.value), body)
    }
    // Σ = c·k + r, k = SOME (an integer's two parts where Σ reads an integer or a difference): the negative parts and
    // c·k's negative part on the other side.
    if (f.cong) {
      const k = someName(f), intK = f.coef.some(([i, c]) => atoms[i]!.int || c < 0), ck = times(f.cong.mod, x(k)), ckNeg = times(f.cong.mod, x(`${k}$neg`))
      return same(sum([...partsOf(f, 1), ...(intK ? [ckNeg] : [])]), sum([...partsOf(f, -1), ck, ...(f.cong.rest ? [n(f.cong.rest)] : [])]))
    }
    const lhs = sum([...partsOf(f, 1), ...(f.d < 0 ? [n(-f.d)] : [])]), rhs = sum([...partsOf(f, -1), ...(f.d > 0 ? [n(f.d)] : [])])
    // Under a condition Σ ≤ d: its negation, −Σ ≤ −d − 1, or the body.
    const body = f.when ? any(condOf({coef: f.when.coef.map(([i, c]) => [i, -c]), d: -f.when.d - 1, cells: false, size: 0}), atMost(lhs, rhs)) : atMost(lhs, rhs)
    return !f.guard ? body : 'keyNot' in f.guard ? any(same(x(KEY), x(atoms[f.guard.keyNot]!.parts[0]![0])), body) : any(notAt(f.guard.atom, f.guard.value), body)
  }
  // The builder call, for a rule whose atoms are its own variables (naturals, or integers alone).
  const sourceOf = (f: Form, text: string): string | undefined => {
    if (!rule || f.when || f.mod) return undefined
    const used = [...new Set([...f.coef.map(([i]) => i), ...(f.guard ? ['keyNot' in f.guard ? f.guard.keyNot : f.guard.atom] : []), ...(f.unreachable ? [f.unreachable.atom] : [])])]
    const ints = f.coef.filter(([i]) => atoms[i]!.int).length
    if (ints && ints !== f.coef.length) return undefined
    const ref = (i: number) => (atoms[i]!.cell ? `${atoms[i]!.parts[0]![0]}.at(k)` : nameOf(i))
    const val = (i: number) => { const mo = modeOf(i); return mo?.choice && !atoms[i]!.cell ? `${ref(i)}.index` : mo?.bool && !atoms[i]!.cell ? `${ref(i)}.n` : ref(i) }
    const cond = (i: number, value: number) => { const mo = modeOf(i); return mo?.choice && !atoms[i]!.cell ? `${ref(i)}.is('${mo.choice[value]}')` : mo?.bool && !atoms[i]!.cell ? (value === 1 ? ref(i) : `${ref(i)}.not()`) : `${ref(i)}.eq(${value})` }
    const args = `({${[...new Set(used.map(i => (atoms[i]!.cell ? atoms[i]!.parts[0]![0] : nameOf(i))))].join(', ')}})`
    const wrap = (body: string) => (f.cells ? `forall(k => ${body})` : body)
    if (f.unreachable) return `r.law('${text}', ${args} => ${cond(f.unreachable.atom, f.unreachable.value)}.not())`
    if (f.cong) {
      if (f.coef.length !== 1 || f.coef[0]![1] !== 1) return undefined
      const intK = atoms[f.coef[0]![0]]!.int
      return `r.law('${text}', ${args} => exists(${intK ? 'int, ' : ''}k => ${val(f.coef[0]![0])}.eq(k.times(${f.cong.mod})${f.cong.rest ? `.plus(${f.cong.rest})` : ''})))`
    }
    const term = (ts: [number, number][], k: number) => {
      const parts = ts.map(([i, c]) => (Math.abs(c) === 1 ? val(i) : `${val(i)}.times(${Math.abs(c)})`))
      if (!parts.length) return String(k)
      return parts.slice(1).reduce((acc, p) => `${acc}.plus(${p})`, parts[0]!) + (k > 0 ? `.plus(${k})` : '')
    }
    const {left, right} = sides(f)
    const body = left.length ? `${term(left, Math.max(0, -f.d))}.atMost(${term(right, Math.max(0, f.d))})` : `${term(right, Math.max(0, f.d))}.atLeast(${Math.max(0, -f.d)})`
    const guarded = !f.guard ? body : 'keyNot' in f.guard ? `k.eq(${nameOf(f.guard.keyNot)}).or(${body})` : `${cond(f.guard.atom, f.guard.value)}.implies(${body})`
    return `r.law('${text}', ${args} => ${wrap(guarded)})`
  }

  // --- evaluating a form ---------------------------------------------------------------------------------------------
  const holdsRow = (f: Form, env: Env): boolean => {
    if (f.unreachable) return valueOf(atoms[f.unreachable.atom]!, env) !== f.unreachable.value
    if (f.cong) {
      let v = 0
      for (const [i, c] of f.coef) v += c * valueOf(atoms[i]!, env)
      const nat = f.coef.every(([i, c]) => !atoms[i]!.int && c > 0)
      return ((v - f.cong.rest) % f.cong.mod + f.cong.mod) % f.cong.mod === 0 && (!nat || v >= f.cong.rest)
    }
    if (f.guard) {
      if ('keyNot' in f.guard) { if (env[K] === valueOf(atoms[f.guard.keyNot]!, env)) return true }
      else if (valueOf(atoms[f.guard.atom]!, env) !== f.guard.value) return true
    }
    if (f.when) { let w = 0; for (const [i, c] of f.when.coef) w += c * valueOf(atoms[i]!, env); if (w > f.when.d) return true }
    let s = 0
    for (const [i, c] of f.coef) s += c * valueOf(atoms[i]!, env)
    return f.mod ? residue(s, f.mod.k) === f.mod.r : s <= f.d
  }
  // At a state: a cell form at every key the maps hold and a fresh one.
  type Point = {scalar: Env, cells: Env[]}
  const pointOf = (params: Env, st: State): Point => ({scalar: {...params, ...st.scalars}, cells: cellRows(params, st)})
  const holdsAt = (f: Form, p: Point) => (f.cells ? p.cells.every(r => holdsRow(f, r)) : holdsRow(f, p.scalar))
  // A kernel witness as a point: its scalars, and a cell row per key it reads a map at.
  const witnessPoint = (w: Record<string, number>): Point => {
    const scalar: Env = Object.fromEntries([...scalars, ...m.params].map(v => [v, w[v] ?? 0]))
    const byKey = new Map<number, Env>()
    for (const [name, value] of Object.entries(w)) {
      const br = name.indexOf('[')
      if (br < 0 || !name.endsWith(']') || !mapSet.has(name.slice(0, br))) continue
      const key = keyValue(name, w)
      if (key === undefined) continue
      const row = byKey.get(key) ?? {...scalar, [K]: key}
      row[AT + name.slice(0, br)] = value
      byKey.set(key, row)
    }
    return {scalar, cells: [...byKey.values()]}
  }

  // --- Houdini on the runs' neighbors ----------------------------------------------------------------------------------
  let alive = forms.slice().sort((p, q) => p.size - q.size).slice(0, maxCandidates)
  const ctis: Point[] = []
  const lawful = (params: Env, st: State) => { try { return given.every(l => watch(m, run, l, params, 4).start(st)) } catch { return false } }
  const houdiniUntil = Math.min(until, performance.now() + Math.max(500, (until - performance.now()) / 4))
  for (let quiet = 0; samples.length && performance.now() < houdiniUntil && quiet < 3;) {
    const killed = new Set<Form>()
    for (let tries = 0; tries < 400 && performance.now() < houdiniUntil; tries++) {
      const base = samples[rand(samples.length)]!, scal = {...base.st.scalars}, maps = {...base.st.maps}
      for (let k = 0, moves = 1 + rand(2); k < moves; k++) {
        if (mapNames.length && rand(2) === 0) {
          const mp = mapNames[rand(mapNames.length)]!, ks = keysIn(base.st), key = ks.length && rand(3) ? ks[rand(ks.length)]! : rand(5)
          const cells = new Map(maps[mp] ?? []); cells.set(key, Math.max(0, cellOf(base.st, mp, key) + (rand(7) - 3))); maps[mp] = cells
        } else if (scalars.length) { const v = scalars[rand(scalars.length)]!; scal[v] = Math.max(0, scal[v]! + (rand(7) - 3)) }
      }
      const st: State = {...base.st, scalars: scal, maps}, pre = pointOf(base.params, st)
      if (!alive.every(f => killed.has(f) || holdsAt(f, pre)) || !lawful(base.params, st)) continue
      const input = randomInput(base.params, 4)
      let next: State
      try { if (!allowed(m, run, base.params, st, input)) continue; next = run.step(base.params, st, input) } catch { continue }
      const post = pointOf(base.params, next)
      let broke = false
      for (const f of alive) if (!killed.has(f) && !holdsAt(f, post)) { killed.add(f); broke = true }
      if (!broke && !lawful(base.params, next)) ctis.push(pre)
    }
    quiet = killed.size ? 0 : quiet + 1
    alive = alive.filter(f => !killed.has(f))
  }

  opts.progress?.('houdini', {alive: alive.length, ctis: ctis.length})
  const used = [...new Set(alive.flatMap(f => (f.mod ? [f.mod.k] : [])))]
  if (used.length) { searchRule = rule?.withDivisors(...used); mm = searchRule ? searchRule.machine : withArithmetic(m, [], used) }

  // --- the kernel ----------------------------------------------------------------------------------------------------
  const lawOf = new Map<Form, Law>()
  const someOf = (f: Form): string[] => (!f.cong ? [] : f.coef.some(([i, c]) => atoms[i]!.int || c < 0) ? [someName(f), `${someName(f)}$neg`] : [someName(f)])
  const lawFor = (f: Form) => { let l = lawOf.get(f); if (!l) lawOf.set(f, (l = {name: textOf(f), holds: condOf(f), ...(f.cells ? {forall: KEY} : {}), ...(f.cong ? {some: someOf(f)} : {})})); return l }
  const names = new Set(given.map(l => l.name))
  alive = alive.filter(f => !names.has(textOf(f)))
  let pool = alive.slice(), chosen: Form[] = []
  const goalName = (g: string) => g.replace(/ @[^@]*$/, '')
  let last: Verdict = first
  const slow = Math.max(3000, (opts.ms ?? 20000) / 10)
  // A point a form is false at; a cell form is judged only at rows that read every map it reads.
  const reads = (f: Form, r: Env) => f.coef.every(([i]) => !atoms[i]!.cell || atoms[i]!.parts.every(([q]) => AT + q in r))
  const falseAt = (f: Form, p: Point) => (f.cells ? p.cells.some(r => reads(f, r) && !holdsRow(f, r)) : !holdsRow(f, p.scalar))
  // (a congruence only where no bound of the candidates rules the point out, before the counterexample's own forms:
  // false at half the states a run doesn't reach, it would otherwise be chosen first everywhere)
  const best = (p: Point, congs = false) => {
    let pickF: Form | undefined, score = -Infinity
    for (const f of pool) {
      if (chosen.includes(f) || !!f.cong !== congs || !falseAt(f, p)) continue
      const s = ctis.reduce((k, c) => k + (falseAt(f, c) ? 1 : 0), 0) * 1000 - f.size
      if (s > score) (pickF = f, score = s)
    }
    return pickF
  }
  // A counterexample to induction no candidate rules out: forms false at it that every sample meets under a condition
  // it meets too (one value, or a sum or difference of two, at most a threshold: 0, ±1, or its own value there), the
  // choice (loc, say) at its value there as the guard. A condition no sample meets gives its negation instead. Only the
  // eight values most unusual at it are read (furthest past the samples in its guard, then the rarest there).
  const choiceMode = modes.find(mo => mo.choice && !atoms[mo.atom]!.cell)
  const condAtoms = plain.filter(i => !atoms[i]!.param && i !== choiceMode?.atom)
  const fromCti = (p: Point): Form[] => {
    const stop = Math.min(until, performance.now() + Math.max(300, (until - performance.now()) / 8))
    const sc = p.scalar, pv = (coef: [number, number][]) => { let v = 0; for (const [i, c] of coef) v += c * valueOf(atoms[i]!, sc); return v }
    const gv = choiceMode ? valueOf(atoms[choiceMode.atom]!, sc) : undefined
    const inGuard: number[] = []
    for (let j = 0; j < NS; j++) if (gv === undefined || valsS[choiceMode!.atom]![j] === gv) inGuard.push(j)
    const unusual = (i: number) => {
      const v = valueOf(atoms[i]!, sc)
      let lo = Infinity, hi = -Infinity, same = 0
      for (const j of inGuard) { const w = valsS[i]![j]!; if (w < lo) lo = w; if (w > hi) hi = w; if (w === v) same++ }
      return [Math.max(0, lo - v, v - hi), -same] as const
    }
    const focus = condAtoms.map(i => ({i, u: unusual(i)})).sort((a, b) => b.u[0] - a.u[0] || b.u[1] - a.u[1]).slice(0, 8).map(x => x.i)
    // Over the focus: one or two values with the magnitudes, three with ±1.
    const bodies: {coef: [number, number][]}[] = []
    const signed = (ks: number[]) => ks.flatMap(k => [k, -k])
    for (const [a, i] of focus.entries()) {
      bodies.push({coef: [[i, 1]]}, {coef: [[i, -1]]})
      for (const [b2, k] of focus.slice(a + 1).entries()) {
        for (const c1 of signed(mags)) for (const c2 of signed(mags)) if (gcd(c1, c2) === 1) bodies.push({coef: [[i, c1], [k, c2]]})
        for (const q of focus.slice(a + b2 + 2)) for (const c1 of [1, -1]) for (const c2 of [1, -1]) for (const c3 of [1, -1]) bodies.push({coef: [[i, c1], [k, c2], [q, c3]]})
      }
    }
    const conds: [number, number][][] = []
    for (const [a, i] of focus.entries()) {
      conds.push([[i, 1]], [[i, -1]])
      for (const k of focus.slice(a + 1)) conds.push([[i, 1], [k, -1]], [[i, -1], [k, 1]], [[i, 1], [k, 1]])
    }
    const out: Form[] = [], guard = choiceMode ? {atom: choiceMode.atom, value: gv!} : undefined
    for (const coef of conds) {
      const here = pv(coef)
      for (const d of [...new Set([here, 0, 1, -1])].filter(d => here <= d)) {
        if (performance.now() > stop) break
        const rows: number[] = []
        for (const j of inGuard) if (at(coef, valsS, j) <= d) rows.push(j)
        const when = {coef, d}, base = sizeOf(coef) + 80
        if (!rows.length) { out.push({coef: coef.map(([i, c]) => [i, -c]), d: -d - 1, cells: false, ...(guard ? {guard} : {}), size: base}); continue }
        const stride = Math.max(1, Math.ceil(rows.length / 600))
        for (const [q, sh] of bodies.entries()) {
          if (q % 256 === 0 && performance.now() > stop) break
          const v = pv(sh.coef)
          let most = -Infinity, ok = true
          for (let t = 0; t < rows.length; t += stride) { const w = at(sh.coef, valsS, rows[t]!); if (w >= v) { ok = false; break } if (w > most) most = w }
          if (ok && Number.isFinite(most)) out.push({coef: sh.coef, d: most, cells: false, ...(guard ? {guard} : {}), when, size: base + sizeOf(sh.coef)})
        }
      }
    }
    // A stride may skip a sample that breaks a form: each is checked again at every sample in its guard.
    return out.sort((x, y) => x.size - y.size).slice(0, 2000).filter(f => inGuard.every(j => holdsRow(f, rowsS[j]!))).slice(0, 400)
  }

  // The search proves one law at a time (proveLaw), each with every law assumed, and keeps what it proved while laws
  // are only added (more laws assumed keep a proof a proof); dropping one forgets it all. Once every law is proven so,
  // the set is proven as a whole, by the rule's own prover: that verdict is the answer.
  // A law of the caller's (or a kind's) proven before any candidate was added stays proven whatever is added or dropped.
  const done = new Set<string>(), base = new Set<string>()
  const forget = () => { done.clear(); for (const b of base) done.add(b) }
  const drop = (f: Form) => { chosen = chosen.filter(g => g !== f); pool = pool.filter(g => g !== f); forget() }
  const search = (ls: Law[]): Verdict => {
    // (laws with "there exists" are proven as a set, their witnesses chosen together: core/exists.ts)
    if (ls.some(l => l.some?.length)) { const whole = prove([...laws, ...chosen.map(lawFor)]); if (!(whole.proven && whole.checked)) forget(); return whole }
    for (let i = 0; i < ls.length; i++) {
      if (done.has(ls[i]!.name)) continue
      proofs++
      const r = proveLaw(mm, ls, i)
      if (!r.proven) return {proven: false, checked: false, goal: r.goal, stuck: r.stuck, ...(r.witness ? {witness: r.witness} : {})}
      done.add(ls[i]!.name)
      if (!chosen.length) base.add(ls[i]!.name)
    }
    if (stepLaws.length) { proofs++; const r = proveStepLaws(mm, ls, stepLaws); if (!r.proven) return {proven: false, checked: false, ...(r.failed ? {goal: r.failed.goal, stuck: r.failed.stuck, ...(r.failed.witness ? {witness: r.failed.witness} : {})} : {})} }
    const whole = prove([...laws, ...chosen.map(lawFor)])
    if (!(whole.proven && whole.checked)) forget()
    return whole
  }
  for (let iter = 0; iter < 300 && performance.now() < until; iter++) {
    const began = performance.now()
    last = search([...given, ...chosen.map(lawFor)])
    const took = performance.now() - began
    opts.progress?.('proof', {chosen: chosen.length, goal: last.goal ?? '', stuck: last.stuck ?? '', ms: Math.round(took)})
    if (last.proven && last.checked) break
    if (!last.goal) break
    const name = goalName(last.goal), stuckOn = chosen.find(f => lawFor(f).name === name)
    if (last.run) {
      // A real run breaks it: a candidate is false (dropped); a law of the caller's is false (the answer).
      if (!stuckOn) break
      drop(stuckOn); continue
    }
    // A proof the last candidate made slow (more cases to split) fails: that candidate goes.
    if (chosen.length && took > slow) { drop(chosen.at(-1)!); continue }
    const p = /@step|@\d+ steps/.test(last.goal) && last.witness ? witnessPoint(last.witness) : undefined
    if (p) ctis.push(p)
    let next = p ? best(p) : undefined
    if (!next && p) next = best(p, true)
    if (!next && p) { const t = performance.now(), made = fromCti(p); pool.push(...made); next = best(p); opts.progress?.('cti', {forms: made.length, ms: Math.round(performance.now() - t)}) }
    if (next) { chosen.push(next); continue }
    // Stuck with no counterexample on a goal not a candidate's: the last candidate made it harder, so it goes.
    if (chosen.length && !stuckOn && !p) { drop(chosen.at(-1)!); continue }
    if (!stuckOn) break
    drop(stuckOn)
  }
  // Unproven: each congruence the runs left alive, with the laws alone (the counterexamples' choice may have gone to the
  // bounds instead), at most four.
  if (!(last.proven && last.checked)) {
    for (const f of alive.filter(g => g.cong).slice(0, 4)) {
      if (performance.now() > until) break
      const v = prove([...laws, lawFor(f)])
      if (v.proven && v.checked) { chosen = [f]; last = v; break }
    }
  }
  if (!(last.proven && last.checked)) return {...last, found: [], stats: stats(samples.length, forms.length, alive.length)}
  // Take out what the proof doesn't need, the last added first.
  for (const f of [...chosen].reverse()) {
    if (performance.now() > until) break
    const without = chosen.filter(g => g !== f), v = prove([...laws, ...without.map(lawFor)])
    if (v.proven && v.checked) (chosen = without, last = v)
  }
  const kept = chosen.flatMap(f => (f.mod ? [f.mod.k] : []))
  if (kept.length) rule?.dividesBy(...kept)
  return {...last, found: chosen.map(f => { const law = lawFor(f), text = law.name, source = sourceOf(f, text); return {law, text, ...(source ? {source} : {})} }), stats: stats(samples.length, forms.length, alive.length)}
}
