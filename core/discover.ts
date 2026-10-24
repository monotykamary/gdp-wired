// Lemmas nobody stated, found: when a rule's laws need a fact about a function defined by a recurrence (`recur`) or
// about the folds of a list a request carries (`carriesList`) that nobody wrote, `discover` looks for it. Candidates come
// from the values themselves: the function computed at many points, the folds over many random lists, and every
// statement of a few shapes that all of them meet (bounds, bounds linear in x, in the further arguments, in the other
// folds or in the params, a closed form fitted exactly to the values, a polynomial of degree 2 at most, and laws
// between two points: never shrinks, never grows faster than it did). Those are proven the way stated lemmas are, by
// induction, together (one that isn't inductive is dropped and the rest tried again: Houdini), and of what is proven
// only the lemmas the laws need are kept. Nothing here is trusted: what it finds is a lemma like any other, proven by
// the kernel when the function or the list is made again with it, and exported to Lean the same way.
//   const out = discover(r, laws, stepLaws)
//   out.verdict          // the laws, proven of out.rule: r with its functions and lists made again with the lemmas
//   out.found            // per function or list, the lemmas found, as source to paste into recur(...) or carriesList(...)
import {quietly} from './cyclic.ts'
import {type C, type E, type Law, type Machine, type Recurrence, type State, any, atMost, compileFunction, evalC, evalE, n, plus, prod, same, seeded, times, x} from './machine.ts'
import {type FnDef, type Kind, type ListFold, type ListLemma, type StepLaw, type Verdict, Cond, Rule, Term, Unproven, lit, proveFold, proveSteps, recur, recurOf} from './dsl.ts'
import {type Fold} from '../kernel/kernel.ts'
import {gcd, plus as addLin} from './solver.ts'
import {closedForm as fit, nfold, polyOf} from './accel.ts'

type Obj = object
type AnyRule = Rule<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>
// A statement over named atoms: Σ coef·atom (+ the constant at '1') <= 0, or = 0. Atoms are the names a lemma's callback
// reads (x and f, y and g between two points, the further arguments; a list's folds, i and the params), and x·x.
type Lin = Record<string, number>
type Cand = {name: string, rel: '<=' | '=', lin: Lin, target?: string}
export type Found = {lemmas?: string[], between?: string[]}
export type Discovery = {verdict: Verdict, rule: AnyRule, found: Record<string, Found>}

const valueOf = (t: Term | number): number | undefined => (typeof t === 'number' ? t : t.val)
const evalLin = (l: Lin, at: Record<string, number>) => Object.entries(l).reduce((s, [a, c]) => s + c * (a === '1' ? 1 : at[a]!), 0)
const holds = (c: Cand, at: Record<string, number>) => { const v = evalLin(c.lin, at); return c.rel === '=' ? v === 0 : v <= 0 }

// The statement as a condition over terms, and as source: the atoms with a positive coefficient on one side, the rest on
// the other (naturals: no subtraction).
const sides = (l: Lin) => {
  const pos: [string, number][] = [], neg: [string, number][] = []
  for (const [a, c] of Object.entries(l)) if (c > 0) pos.push([a, c]); else if (c < 0) neg.push([a, -c])
  return {pos, neg}
}
const termOfSide = (side: [string, number][], atoms: Record<string, Term>): Term => {
  const ts = side.map(([a, c]) => (a === '1' ? lit(c) : c === 1 ? atoms[a]! : atoms[a]!.times(c)))
  return ts.length ? ts.slice(1).reduce((acc, t) => acc.plus(t), ts[0]!) : lit(0)
}
const condOf = (c: Cand, atoms: Record<string, Term>): Cond => {
  const {pos, neg} = sides(c.lin), a = termOfSide(pos, atoms), b = termOfSide(neg, atoms)
  return c.rel === '=' ? a.eq(b) : a.atMost(b)
}
const srcOfSide = (side: [string, number][], src: (a: string) => string): string => {
  const parts = side.filter(([a]) => a !== '1'), k = side.find(([a]) => a === '1')?.[1]
  if (!parts.length) return String(k ?? 0)
  const one = ([a, c]: [string, number]) => (c === 1 ? src(a) : `${src(a)}.times(${c})`)
  return [one(parts[0]!), ...parts.slice(1).map(p => `.plus(${one(p)})`), ...(k ? [`.plus(${k})`] : [])].join('')
}
// The side that holds the value the lemma is about (f(x), or the fold) goes first: f.atLeast(1), not lit(1).atMost(f).
const flipped = (c: Cand, target: string) => { const {pos, neg} = sides(c.lin); return neg.some(([a]) => a === target) || (pos.every(([a]) => a === '1') && neg.some(([a]) => a !== '1')) }
const srcOf = (c: Cand, src: (a: string) => string, target: string): string => {
  const {pos, neg} = sides(c.lin)
  if (flipped(c, target)) return `${srcOfSide(neg, src)}.${c.rel === '=' ? 'eq' : 'atLeast'}(${srcOfSide(pos, src)})`
  return `${srcOfSide(pos, src)}.${c.rel === '=' ? 'eq' : 'atMost'}(${srcOfSide(neg, src)})`
}
// The name a found lemma goes by: the statement in plain arithmetic.
const nameOf = (c: Cand, show: (a: string) => string, target: string): string => {
  const {pos, neg} = sides(c.lin)
  const side = (s: [string, number][]) => (s.length ? [...s.filter(([a]) => a === target), ...s.filter(([a]) => a !== target)].map(([a, k]) => (a === '1' ? String(k) : k === 1 ? show(a) : `${k}·${show(a)}`)).join(' + ') : '0')
  return flipped(c, target) ? `${side(neg)} ${c.rel === '=' ? '=' : '>='} ${side(pos)}` : `${side(pos)} ${c.rel === '=' ? '=' : '<='} ${side(neg)}`
}

// Candidates: `target` against forms built from `bases` (each a scaled atom or nothing) and a fitted constant, kept when
// the samples hold them. An equality where the upper and lower constant meet.
function linearCands(target: string, forms: Lin[], samples: Record<string, number>[], show: (a: string) => string): Cand[] {
  const out: Cand[] = []
  for (const form of forms) {
    const d = samples.map(s => s[target]! - evalLin(form, s)), hi = Math.max(...d), lo = Math.min(...d)
    const lin = (k: number, sign: number): Lin => { const l: Lin = {[target]: sign}; for (const [a, c] of Object.entries(form)) l[a] = (l[a] ?? 0) - sign * c; if (k) l['1'] = -sign * k; return l }
    const constOnly = Object.keys(form).length === 0
    if (hi === lo) out.push({name: '', rel: '=', lin: lin(hi, 1)})
    else {
      out.push({name: '', rel: '<=', lin: lin(hi, 1)})
      // f >= 0 says nothing; a lower bound against a form only where it is one.
      if (!(constOnly && lo <= 0)) out.push({name: '', rel: '<=', lin: lin(lo, -1)})
    }
  }
  for (const c of out) { c.name = nameOf(c, show, target); c.target = target }
  return dedupe(out.filter(c => exact(c) && samples.every(s => holds(c, s))))
}
const dedupe = (cs: Cand[]) => [...new Map(cs.map(c => [c.name, c])).values()]
// A statement whose coefficients are naturals a term can hold (a fit to values near 2^53 can make one that isn't).
const exact = (c: Cand) => Object.values(c.lin).every(Number.isSafeInteger)

// A polynomial in x of degree 2 or 3, exact over the rationals, as d·f = a·x·x·x + b·x·x + c·x + e with whole numbers,
// from core/accel.ts's closed forms: the recurrence's own where its step is affine in f and a polynomial in x (the
// engine on f and the powers of x, a triangular system), else the values' (the engine on the numbers: the shortest
// recurrence they all meet); kept when every sample meets it.
function closedForm(samples: Record<string, number>[], show: (a: string) => string, rec?: Recurrence): Cand[] {
  const at = new Map<number, number>()
  for (const s of samples) { if (at.has(s.x!) && at.get(s.x!) !== s.f) return []; at.set(s.x!, s.f!) }
  const seq: Lin[] = []
  while (at.has(seq.length)) seq.push({1: at.get(seq.length)!})
  const p = (() => {
    const next = rec && powers(rec.next), zero = rec?.zero.op === 'const' ? rec.zero.value : undefined
    const f = next && zero !== undefined ? nfold({prev: 1}, {x: {x: 1, 1: 1}, xx: {xx: 1, x: 2, 1: 1}, xxx: {xxx: 1, xx: 3, x: 3, 1: 1}, prev: next}) : undefined
    const start = (c: Lin) => ({1: (c['1'] ?? 0) + (c.prev ?? 0) * zero!})
    if (f) return {terms: f.terms.map(t => ({...t, c: start(t.c)})), den: f.den}
    return seq.length >= 3 ? fit(seq, false) : undefined
  })()
  const cs = p && polyOf(p)
  if (!cs || cs.length < 3 || cs.length > 4) return []
  // Σ c_k·C(x, k) / den, times 6·den: C(x, 2)·6 = 3·x·x − 3·x, C(x, 3)·6 = x·x·x − 3·x·x + 2·x
  const [c0, c1, c2, c3] = [0, 1, 2, 3].map(k => cs[k]?.['1'] ?? 0) as [number, number, number, number]
  const lin: Lin = {f: 6 * p!.den, xxx: -c3, xx: -(3 * c2 - 3 * c3), x: -(6 * c1 - 3 * c2 + 2 * c3), 1: -6 * c0}
  const g = Object.values(lin).reduce((a, b) => gcd(a, Math.abs(b)), 0)
  const c: Cand = {name: '', rel: '=', lin: Object.fromEntries(Object.entries(lin).map(([a, k]) => [a, k / g]).filter(([, k]) => k !== 0))}
  c.name = nameOf(c, show, 'f')
  return exact(c) && samples.every(s => holds(c, s)) ? [c] : []
}
// A step as a form over prev and the powers of x up to x·x·x (x, xx, xxx), or undefined where it isn't one.
function powers(e: E): Lin | undefined {
  switch (e.op) {
    case 'var': return e.name === 'x' || e.name === 'prev' ? {[e.name]: 1} : undefined
    case 'const': return {1: e.value}
    case 'add': { const a = powers(e.a), b = powers(e.b); return a && b && addLin(a, b) }
    case 'mul': { const a = powers(e.a); return a && Object.fromEntries(Object.entries(a).map(([k, c]) => [k, c * e.k])) }
    case 'prod': {
      const a = powers(e.a), b = powers(e.b)
      if (!a || !b) return undefined
      let o: Lin = {}
      for (const [u, c] of Object.entries(a)) for (const [w, d] of Object.entries(b)) {
        if (u !== '1' && w !== '1' && (u === 'prev' || w === 'prev' || u.length + w.length > 3)) return undefined
        const m = u === '1' ? w : w === '1' ? u : 'x'.repeat(u.length + w.length)
        o = addLin(o, {[m]: c * d})
      }
      return o
    }
    case 'sub': case 'min': case 'max': case 'if': case 'get': return undefined
  }
}
// The law a goal is of (the kernel names each goal after its law: '<law> @step').
const lawOfGoal = (goal: string) => goal.replace(/ @(start|step|step law|\d+ steps|leaf|node)$/, '')
const isGoalOf = (goal: string) => (c: Cand) => { const law = lawOfGoal(goal); return law === c.name || law === `${c.name} at y` }

// --- recurrences ---------------------------------------------------------------------------------------------------

const showRecur = (a: string) => (a === 'f' ? 'f(x)' : a === 'g' ? 'f(y)' : a === 'xx' ? 'x·x' : a === 'xxx' ? 'x·x·x' : a)
const srcRecur = (a: string) => (a === 'xx' ? 'x.mul(x)' : a === 'xxx' ? 'x.mul(x).mul(x)' : a)
// The function's values: x from 0 to 40 at a few values of each further argument (all of them for two at most).
function recurSamples(d: FnDef, args: string[]): Record<string, number>[] {
  const f = (typeof d.js === 'function' ? d.js : compileFunction<() => (...a: number[]) => number>([], `return (${d.js})`)()) as (...a: number[]) => number
  const vals = [0, 1, 2, 3, 5, 8, 13, 40]
  const tuples: number[][] = args.reduce<number[][]>((acc) => acc.flatMap(t => vals.map(v => [...t, v])), [[]])
  const out: Record<string, number>[] = []
  for (const t of tuples) for (let x = 0; x <= 40; x++) {
    let y: number
    try { y = f(x, ...t) } catch (e) { if (e instanceof RangeError) break; throw e }
    // (past 2^53 a value isn't exact, and no statement a lemma makes may hold its constants: the run stops there too)
    if (!Number.isSafeInteger(y) || y < 0) break
    out.push({x, f: y, xx: x * x, xxx: x * x * x, ...Object.fromEntries(args.map((a, i) => [a, t[i]!]))})
  }
  return out
}
// Lemmas about every x and f(x), and laws between two points, that every value meets.
function recurCands(samples: Record<string, number>[], args: string[], rec?: Recurrence) {
  const slopes = new Set<number>()
  const byArgs = new Map<string, Record<string, number>[]>()
  for (const s of samples) { const k = args.map(a => s[a]).join(); byArgs.set(k, [...(byArgs.get(k) ?? []), s]) }
  for (const run of byArgs.values()) for (let i = 1; i < run.length; i++) { const dd = run[i]!.f! - run[i - 1]!.f!; if (dd > 0) slopes.add(dd) }
  // The gentlest slopes and the steepest.
  const sorted = [...slopes].sort((a, b) => a - b), picked = [...new Set([...sorted.slice(0, 3), ...sorted.slice(-1)])]
  const xs = [{}, ...picked.map(s => ({x: s}))]
  const forms: Lin[] = xs.flatMap(fx => [fx, ...args.map(a => ({...fx, [a]: 1}))])
  const lemmas = [...linearCands('f', forms, samples, showRecur), ...(args.length ? [] : closedForm(samples, showRecur, rec))]
  const pairs: Record<string, number>[] = []
  for (const run of byArgs.values()) for (const a of run) for (const b of run) if (a.x! <= b.x!) pairs.push({x: a.x!, f: a.f!, y: b.x!, g: b.f!})
  const steepest = Math.max(0, ...slopes)
  const between = ([
    {name: '', rel: '<=', lin: {f: 1, g: -1}},
    {name: '', rel: '<=', lin: {g: 1, f: -1}},
    ...(steepest ? [{name: '', rel: '<=', lin: {g: 1, x: steepest, f: -1, y: -steepest}}] : []),
  ] as Cand[]).filter(c => exact(c) && pairs.every(p => holds(c, p)))
  for (const c of between) c.name = nameOf(c, showRecur, 'g')
  return {lemmas, between}
}
const recurAtoms = (args: string[], x: Term, f: Term, env: Record<string, Term>, y?: Term, g?: Term): Record<string, Term> =>
  ({x, f, xx: x.mul(x), xxx: x.mul(x).mul(x), ...(y && g ? {y, g} : {}), ...Object.fromEntries(args.map(a => [a, env[a]!]))})
const recurSrc = (c: Cand, args: string[], between: boolean) => {
  const reads = (a: string) => Object.keys(c.lin).includes(a) || (a === 'x' && ('xx' in c.lin || 'xxx' in c.lin))
  const names = between ? ['x', 'f', 'y', 'g'] : ['x', 'f']
  let unused = 0
  const params = [...names.map(n => (reads(n) ? n : '_'.repeat(++unused))), ...(args.some(reads) ? [`{${args.filter(reads).join(', ')}}`] : [])]
  while (params.length && /^_+$/.test(params.at(-1)!)) params.pop()
  return `${quoted(c.name)}: (${params.join(', ')}) => ${srcOf(c, srcRecur, between ? 'g' : 'f')}`
}

type Made = {d: FnDef & {verdict: Verdict}, lemmas: Cand[], between: Cand[]}
// The function made again with the lemmas and laws between, those that aren't proven dropped one at a time.
function houdiniRecur(d: FnDef, lemmas: Cand[], between: Cand[]): Made | undefined {
  const src = recurOf(d)!, args = [...(src.def.args ?? [])]
  let ls = [...lemmas], bs = [...between]
  for (let round = 0; round < lemmas.length + between.length + 1; round++) {
    try {
      const made = recur(src.name, src.def, {...src.lemmas, ...Object.fromEntries(ls.map(c => [c.name, (x: Term, f: Term, env: Record<string, Term>) => condOf(c, recurAtoms(args, x, f, env))]))},
        {...src.between, ...Object.fromEntries(bs.map(c => [c.name, (x: Term, f: Term, y: Term, g: Term, env: Record<string, Term>) => condOf(c, recurAtoms(args, x, f, env, y, g))]))})
      return {d: made, lemmas: ls, between: bs}
    } catch (e) {
      if (!(e instanceof Unproven)) throw e
      const goal = e.verdict.goal ?? '', l = ls.find(isGoalOf(goal)), b = bs.find(isGoalOf(goal))
      if (l) ls = ls.filter(c => c !== l)
      else if (b) bs = bs.filter(c => c !== b)
      else if (bs.length) bs = [] // a lemma at y that isn't proven between the points: give up on the laws between
      else return undefined
    }
  }
  return undefined
}

// --- lists a request carries ---------------------------------------------------------------------------------------

type ListPart = [string, Kind<unknown>, Record<string, ListFold<unknown>>, Record<string, ListLemma>]
const natParams = (params: [string, Kind<unknown>][]) => params.filter(([n, k]) => { const vs = k.vars(n); return vs.length === 1 && vs[0] === n }).map(([n]) => n)
function listSamples([name, kind, folds]: ListPart, params: [string, Kind<unknown>][]): Record<string, number>[] {
  const rand = seeded(7), out: Record<string, number>[] = []
  for (let trial = 0; trial < 300; trial++) {
    const pv: Record<string, number> = Object.assign({}, ...params.map(([n, k]) => k.random(n, rand, 12)))
    const p = Object.fromEntries(params.map(([n, k]) => [n, k.build(n, part => lit(pv[part]!))]))
    const acc: Record<string, number> = {}
    for (const [f, d] of Object.entries(folds)) acc[f] = typeof d.from === 'number' ? d.from : valueOf(d.from(p) as Term | number)!
    const len = rand(9), at = (i: number) => ({...acc, i, ...pv})
    out.push(at(0))
    for (let i = 0; i < len; i++) {
      const raw = kind.random(name, rand, 12), item = kind.build(name, part => lit(raw[part] ?? 0))
      for (const [f, d] of Object.entries(folds)) acc[f] = valueOf(d.step(lit(acc[f]!), item, p) as Term | number)!
      out.push(at(i + 1))
    }
  }
  return out.filter(s => Object.values(s).every(v => v !== undefined && Number.isSafeInteger(v)))
}
function listCands(part: ListPart, params: [string, Kind<unknown>][], samples: Record<string, number>[]): Cand[] {
  const folds = Object.keys(part[2]), ps = natParams(params)
  // The position reads only as itself (a list's lemmas hold at every position, a condition at every key, which reads its
  // key alone or plus a constant).
  const out: Cand[] = []
  for (const f of folds) {
    const others = [...folds.filter(g => g !== f), ...ps]
    const forms: Lin[] = [{}, {i: 1}, ...others.map(g => ({[g]: 1})), ...others.flatMap((g, j) => others.slice(j + 1).map(h => ({[g]: 1, [h]: 1})))]
    out.push(...linearCands(f, forms, samples, a => a))
  }
  return dedupe(out)
}
const listSrc = (c: Cand, folds: string[], params: string[], target: string) => {
  const reads = (a: string) => a in c.lin
  const ps = [`{${folds.filter(reads).join(', ')}}`, ...(reads('i') || params.some(reads) ? [reads('i') ? 'i' : '_'] : []), ...(params.some(reads) ? [`{${params.filter(reads).join(', ')}}`] : [])]
  return `${quoted(c.name)}: (${ps.join(', ')}) => ${srcOf(c, a => a, target)}`
}
const listLemma = (c: Cand, params: string[]): ListLemma => (acc, i, p: Record<string, Term>) => condOf(c, {...acc, i, ...Object.fromEntries(params.map(n => [n, p[n]!]))})
function houdiniList(r: AnyRule, part: ListPart, cands: Cand[], params: string[]): {rule: AnyRule, kept: Cand[]} | undefined {
  let ls = [...cands]
  for (let round = 0; round <= cands.length; round++) {
    try { return {rule: r.withParts({}, {[part[0]]: Object.fromEntries(ls.map(c => [c.name, listLemma(c, params)]))}), kept: ls} } catch (e) {
      if (!(e instanceof Unproven)) throw e
      const goal = e.verdict.goal ?? '', l = ls.find(isGoalOf(goal))
      if (!l) return undefined
      ls = ls.filter(c => c !== l)
    }
  }
  return undefined
}

// --- the search ----------------------------------------------------------------------------------------------------

// The laws of r, and where they aren't proven as r states them, the lemmas found for its functions and lists: all that
// is proven first, then each dropped in turn while the laws stay proven without it.
// `first`: the laws' verdict on r alone, when the caller has it.
export function discover(r: AnyRule, laws: Law[], stepLaws: StepLaw[] = [], first?: Verdict): Discovery {
  return quietly(() => discoverSearch(r, laws, stepLaws, first ?? proveSteps(r, laws, stepLaws, {search: false})))
}
function discoverSearch(r: AnyRule, laws: Law[], stepLaws: StepLaw[], first: Verdict): Discovery {
  if (first.proven && first.checked) return {verdict: first, rule: r, found: {}}
  const {params, fns, lists} = r.parts, ps = natParams(params)
  // Per function and per list: what is proven, made into the rule. A function with a closed form (of degree 2 or 3,
  // fitted exactly) first with it alone: it decides the function, and the bounds beside it, which the closed form
  // implies only through products, are slow to prove by induction; the rest where the laws aren't proven with it.
  const cands = new Map(fns.flatMap(([n, d]) => { const src = recurOf(d); if (!src) return []; const args = [...(src.def.args ?? [])]; return [[n, recurCands(recurSamples(d, args), args, d.recur)] as const] }))
  const exact = (c: Cand) => c.rel === '=' && ('xx' in c.lin || 'xxx' in c.lin)
  const makeFns = (closedOnly: boolean): Record<string, Made> => {
    const out: Record<string, Made> = {}
    for (const [n, d] of fns) {
      const cs = cands.get(n)
      if (!cs) continue
      const closed = cs.lemmas.filter(exact), made = closedOnly && closed.length ? houdiniRecur(d, closed, []) : houdiniRecur(d, cs.lemmas, cs.between)
      if (made && (made.lemmas.length || made.between.length)) out[n] = made
    }
    return out
  }
  const withLists = (fnMade: Record<string, Made>) => {
    let rule = r.withParts(Object.fromEntries(Object.entries(fnMade).map(([n, m]) => [n, m.d])))
    const listKept: Record<string, Cand[]> = {}
    for (const part of lists) {
      const out = houdiniList(rule, part, listCands(part, params, listSamples(part, params)), ps)
      if (out && out.kept.length) { rule = out.rule; listKept[part[0]] = out.kept }
    }
    return {fnMade, rule, listKept, verdict: proveSteps(rule, laws, stepLaws, {search: false})}
  }
  let made = [...cands.values()].some(cs => cs.lemmas.some(exact)) ? withLists(makeFns(true)) : undefined
  if (!made || !(made.verdict.proven && made.verdict.checked)) made = withLists(makeFns(false))
  const {fnMade, rule, listKept, verdict} = made
  const found = (): Record<string, Found> => ({
    ...Object.fromEntries(Object.entries(fnMade).map(([n, m]) => { const args = [...(recurOf(m.d)!.def.args ?? [])]; return [n, {...(m.lemmas.length ? {lemmas: m.lemmas.map(c => recurSrc(c, args, false))} : {}), ...(m.between.length ? {between: m.between.map(c => recurSrc(c, args, true))} : {})}] })),
    ...Object.fromEntries(Object.entries(listKept).map(([n, cs]) => [n, {lemmas: cs.map(c => listSrc(c, Object.keys(lists.find(l => l[0] === n)![2]), ps, c.target!))}])),
  })
  if (!(verdict.proven && verdict.checked)) return {verdict, rule, found: found()}
  // Only what the laws need: each lemma dropped in turn (the function or list made again without it, which fails when
  // another lemma leaned on it), kept where the laws aren't proven without it.
  let best = {rule, verdict}
  // A rule made again and the laws proven of it; or the lemma whose proof failed without the one dropped.
  const tryRule = (next: () => AnyRule): {rule: AnyRule, verdict: Verdict} | {leaned: string} | undefined => {
    try { const r2 = next(), v = proveSteps(r2, laws, stepLaws, {search: false}); return v.proven && v.checked ? {rule: r2, verdict: v} : undefined } catch (e) {
      if (e instanceof Unproven) return {leaned: e.verdict.goal ?? ''}
      throw e
    }
  }
  const original = Object.fromEntries(fns)
  const fnRecur = (n: string, m: Made) => { const src = recurOf(original[n]!)!, args = [...(src.def.args ?? [])]
    return recur(src.name, src.def, {...src.lemmas, ...Object.fromEntries(m.lemmas.map(c => [c.name, (x: Term, f: Term, env: Record<string, Term>) => condOf(c, recurAtoms(args, x, f, env))]))},
      {...src.between, ...Object.fromEntries(m.between.map(c => [c.name, (x: Term, f: Term, y: Term, g: Term, env: Record<string, Term>) => condOf(c, recurAtoms(args, x, f, env, y, g))]))}) }
  const build = () => r.withParts(Object.fromEntries(Object.entries(fnMade).map(([n, m]) => [n, fnRecur(n, m)])), Object.fromEntries(Object.entries(listKept).map(([n, cs]) => [n, Object.fromEntries(cs.map(c => [c.name, listLemma(c, ps)]))])))
  for (const [n, m] of Object.entries(fnMade)) {
    // A lemma dropped takes with it those that leaned on it, each named by the proof that failed without it.
    for (const kind of ['between', 'lemmas'] as const) for (const c of [...m[kind]]) {
      if (!m[kind].includes(c)) continue
      const before = {lemmas: m.lemmas, between: m.between}
      m[kind] = m[kind].filter(x => x !== c)
      for (;;) {
        const out = tryRule(build)
        if (out && 'rule' in out) { best = out; break }
        const d: Cand | undefined = out ? [...m.lemmas, ...m.between].find(isGoalOf(out.leaned)) : undefined
        if (!d) { m.lemmas = before.lemmas; m.between = before.between; break }
        m.lemmas = m.lemmas.filter(x => x !== d); m.between = m.between.filter(x => x !== d)
      }
    }
    if (!m.lemmas.length && !m.between.length) delete fnMade[n]
  }
  for (const [n, cs] of Object.entries(listKept)) {
    for (const c of [...cs]) {
      if (!listKept[n]!.includes(c)) continue
      const before = listKept[n]!
      listKept[n] = listKept[n]!.filter(x => x !== c)
      for (;;) {
        const out = tryRule(build)
        if (out && 'rule' in out) { best = out; break }
        const d: Cand | undefined = out ? listKept[n]!.find(isGoalOf(out.leaned)) : undefined
        if (!d) { listKept[n] = before; break }
        listKept[n] = listKept[n]!.filter(x => x !== d)
      }
    }
    if (!listKept[n]!.length) delete listKept[n]
  }
  const again = tryRule(build), last = again && 'rule' in again ? again : best
  return {verdict: last.verdict, rule: last.rule, found: found()}
}

// --- folds over trees ----------------------------------------------------------------------------------------------

// The same for a fold over trees (`fold`, binary or with `.children`): candidates about a tree's values (and, under
// `.children`, about the running values of a node's children, where kind$ is 1), from the values of random trees, kept
// when every one meets them, proven by induction over the tree beside the laws (Houdini), only those the laws need kept.
// `found` is source: laws to give proveFold as `lemmas` (`f.law(...)`), and for `.children` the lemmas it takes.
type TreeFold = {fold: Fold, lemmas?: Law[], name: string}
export type FoldDiscovery = {verdict: Verdict, lemmas: Law[], found: string[]}
function foldSamples(f: Fold): Record<string, number>[] {
  const rand = seeded(11), none: Machine = {name: f.name, params: [], inputs: [], state: {}, step: {}}, st: State = {scalars: {}, maps: {}}
  const out: Record<string, number>[] = []
  const draw = (names: string[], ok: C | undefined, env: Record<string, number>) => {
    for (let tries = 0; tries < 50; tries++) {
      const e = {...env, ...Object.fromEntries(names.map(n => [n, rand(2) ? rand(2) : rand(13)]))}
      if (!ok || evalC(ok, e, st, none)) return e
    }
    return undefined
  }
  for (let trial = 0; trial < 300; trial++) {
    const ps = draw(f.params, f.pre, {})
    if (!ps) continue
    const tree = (depth: number): Record<string, number> | undefined => {
      const own = draw(f.inputs, f.assume, ps)
      if (!own) return undefined
      if (depth === 0 || rand(4) === 0) return Object.fromEntries(Object.entries(f.leaf).map(([n, e]) => [n, evalE(e, own, st, none)]))
      const l = tree(depth - 1), r = tree(depth - 1)
      if (!l || !r) return undefined
      const env = {...own, ...Object.fromEntries(Object.entries(l).map(([n, x]) => [`l_${n}`, x])), ...Object.fromEntries(Object.entries(r).map(([n, x]) => [`r_${n}`, x]))}
      const vals = Object.fromEntries(Object.entries(f.node).map(([n, e]) => [n, evalE(e, env, st, none)]))
      out.push({...ps, ...vals})
      return vals
    }
    const top = tree(1 + rand(6))
    if (top) out.push({...ps, ...top})
  }
  return out.filter(s => Object.values(s).every(x => Number.isSafeInteger(x)))
}
const eOfSide = (side: [string, number][]): E => {
  const es = side.map(([a, c]) => { const t = a === '1' ? n(c) : a.includes('*') ? prod(x(a.split('*')[0]!), x(a.split('*')[1]!)) : x(a); return a === '1' || c === 1 ? t : times(c, t) })
  return es.length ? es.slice(1).reduce((acc, t) => plus(acc, t), es[0]!) : n(0)
}
const cOfCand = (c: Cand): C => { const {pos, neg} = sides(c.lin), a = eOfSide(pos), b = eOfSide(neg); return c.rel === '=' ? same(a, b) : atMost(a, b) }
export function discoverFold(f: TreeFold, laws: Law[]): FoldDiscovery { return quietly(() => discoverFoldSearch(f, laws)) }
function discoverFoldSearch(f: TreeFold, laws: Law[]): FoldDiscovery {
  const stated = f.lemmas ?? [], first = proveFold({fold: f.fold, lemmas: stated}, laws)
  if (first.proven && first.checked) return {verdict: first, lemmas: [], found: []}
  const fold = f.fold, names = Object.keys(fold.leaf), rose = names.includes('kind$'), samples = foldSamples(fold)
  // The values a law reads (a tree's own, or under .children the running values of the children), each group with the
  // samples it is claimed of and the guard it is claimed under.
  const groups = rose
    ? [{atoms: names.filter(n => !n.startsWith('kids$') && n !== 'kind$'), at: 0}, {atoms: names.filter(n => n.startsWith('kids$')), at: 1}]
    : [{atoms: names, at: undefined}]
  const cands: {cand: Cand, at?: number}[] = []
  for (const g of groups) {
    const here = samples.filter(s => g.at === undefined || s['kind$'] === g.at).map(s => ({...s, ...Object.fromEntries(g.atoms.flatMap(a => fold.params.map(p => [`${a}*${p}`, s[a]! * s[p]!])))}))
    if (!here.length) continue
    for (const t of g.atoms) {
      const others = [...g.atoms.filter(a => a !== t), ...fold.params]
      const forms: Lin[] = [{}, ...others.map(o => ({[o]: 1})), ...others.flatMap((o, j) => others.slice(j + 1).map(q => ({[o]: 1, [q]: 1}))), ...g.atoms.filter(a => a !== t).flatMap(a => fold.params.map(p => ({[`${a}*${p}`]: 1})))]
      const show = (a: string) => a.replace(/kids\$/g, '').replace('*', '·')
      // A lemma about the children's running values goes by "the children's ...", apart from the laws about a tree's.
      for (const c of linearCands(t, forms, here, show)) cands.push({cand: g.at === 1 ? {...c, name: `the children's ${c.name}`} : c, ...(g.at === undefined ? {} : {at: g.at})})
    }
  }
  const lawOf = ({cand, at}: {cand: Cand, at?: number}): Law => ({name: cand.name, holds: at === undefined ? cOfCand(cand) : any(at === 0 ? atMost(n(1), x('kind$')) : same(x('kind$'), n(0)), cOfCand(cand))})
  // Houdini: every candidate beside the laws; a candidate whose goal fails is dropped, until the rest are proven.
  let kept = dedupeBy(cands, c => `${c.at}:${c.cand.name}`)
  const prove = (ks: typeof kept) => proveFold({fold, lemmas: [...stated, ...ks.map(lawOf)]}, laws)
  let verdict = prove(kept)
  for (let round = 0; round <= cands.length && !(verdict.proven && verdict.checked); round++) {
    const bad = kept.find(c => isGoalOf(verdict.goal ?? '')(c.cand))
    if (!bad) break
    // The kernel's witness is a counterexample to induction: the leaf or node it names, from children that meet every
    // law kept. Each candidate its values break goes with the one the goal named.
    const broken = new Set([bad, ...brokenAt(fold, verdict, kept)])
    kept = kept.filter(c => !broken.has(c))
    verdict = prove(kept)
  }
  if (!(verdict.proven && verdict.checked)) return {verdict, lemmas: [], found: []}
  // Only what the laws need.
  for (const c of [...kept]) {
    const v = prove(kept.filter(k => k !== c))
    if (v.proven && v.checked) { kept = kept.filter(k => k !== c); verdict = v }
  }
  const src = ({cand, at}: {cand: Cand, at?: number}) => {
    const reads = Object.keys(cand.lin).flatMap(a => a.split('*')).filter(a => a !== '1'), own = reads.filter(a => !fold.params.includes(a)), ps = reads.filter(a => fold.params.includes(a))
    const body = srcOf(cand, a => (a.includes('*') ? `${a.split('*')[0]!}.mul(${a.split('*')[1]!})` : a).replace(/kids\$/g, ''), cand.target!)
    if (at === 1) return `${quoted(cand.name)}: ({${own.map(a => a.replace('kids$', '')).join(', ')}}${ps.length ? `, {${ps.join(', ')}}` : ''}) => ${body}`
    return `f.law(${quoted(cand.name)}, ({${[...own, ...ps].join(', ')}}) => ${body})`
  }
  return {verdict, lemmas: kept.map(lawOf), found: kept.map(src)}
}
function brokenAt(fold: Fold, v: Verdict, kept: {cand: Cand, at?: number}[]): {cand: Cand, at?: number}[] {
  const w = v.witness, where = /@(leaf|node)$/.exec(v.goal ?? '')?.[1]
  // A witness over products (each a variable of its own to the linear refutation) isn't a point of the fold.
  if (!w || !where || Object.keys(w).some(k => k.includes('*'))) return []
  const none: Machine = {name: fold.name, params: [], inputs: [], state: {}, step: {}}, st: State = {scalars: {}, maps: {}}
  const withProducts = (c: Cand, at: Record<string, number>) => ({...at, ...Object.fromEntries(Object.keys(c.lin).filter(a => a.includes('*')).map(a => [a, at[a.split('*')[0]!]! * at[a.split('*')[1]!]!]))})
  const meets = (c: {cand: Cand, at?: number}, at: Record<string, number>) => (c.at !== undefined && at['kind$'] !== c.at) || holds(c.cand, withProducts(c.cand, at))
  try {
    const env = {...Object.fromEntries([...fold.params, ...fold.inputs, ...Object.keys(fold.leaf).flatMap(k => [`l_${k}`, `r_${k}`])].map(k => [k, 0])), ...w}
    if ((fold.pre && !evalC(fold.pre, env, st, none)) || (fold.assume && !evalC(fold.assume, env, st, none))) return []
    const side = (p: string) => ({...Object.fromEntries(fold.params.map(k => [k, env[k]!])), ...Object.fromEntries(Object.keys(fold.leaf).map(k => [k, env[`${p}${k}`]!]))})
    // The children must meet what is kept, or the point isn't one the induction step starts from.
    if (where === 'node' && !kept.every(c => meets(c, side('l_')) && meets(c, side('r_')))) return []
    const vals = Object.fromEntries(Object.entries(where === 'leaf' ? fold.leaf : fold.node).map(([k, e]) => [k, evalE(e, env, st, none)]))
    const at = {...Object.fromEntries(fold.params.map(k => [k, env[k]!])), ...vals}
    return kept.filter(c => !meets(c, at))
  } catch { return [] }
}
const quoted = (name: string) => (name.includes("'") ? JSON.stringify(name) : `'${name}'`)
const dedupeBy = <T>(xs: T[], key: (x: T) => string) => [...new Map(xs.map(x => [key(x), x])).values()]
