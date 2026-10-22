// Q4 on TIP: `bun research/table/tip.ts <problem.smt2> --lemmas compare/tip/lemmas-sample30.json --task <name>
// [--max-size 8] [--samples 100] [--ms 500000] [--max-classes 50000]`. Prints one JSON line per size and a last one
// (stage 'result') with everything measured.
//   signature  the functions the goal calls, closed over the functions their bodies call (those with a function
//              argument left out), the constructors of every datatype their types reach, TIP's built-in `=` at the
//              goal's variables' types, true and false; type variables at the problem's Peano naturals (a datatype
//              of a constructor of no field and one of a single field of itself), else at Int from 0
//   rows       N random valuations of the variables: 3 a type for the goal's variables' types, 2 for the others
//   columns    terms by size (symbols) 1..max, built from class representatives only (QuickSpec): a term is a new
//              column; its values on the rows its fingerprint
//   Q4         columns grouped by (type, fingerprint): a term landing in an existing class is an equation
//   lemmas     an equation l = r is found when both sides' fingerprints (evaluated on the same rows) are classes the
//              enumeration reached and are the same class (the equation is then in the congruence closure of those
//              emitted); a boolean lemma t when t's class is true's; `(=> h c)` and `(or a b)` (as ¬a ⇒ b) by Q5:
//              the rows split by h's column (depth 2 for a conjunction of two), c checked on h's part, its size noted
// Uses compare/tip/tip.ts (its reader and evaluator) and nothing of gdp-wired.
import {readFileSync} from 'node:fs'
import {type Sx, type Tip, type Ty, type V, BOOL, INT, OutOfFuel, Unsupported, evaluate, parseTip, parseSx, prenex, sameV, show, showTy, showV, substTy, tyOf} from '../../compare/tip/tip.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: string) => { const i = args.indexOf(k); return i < 0 ? d : args[i + 1]! }
const task = opt('--task', file), maxSize = Number(opt('--max-size', '8')), N = Number(opt('--samples', '100'))
const budgetMs = Number(opt('--ms', '500000')), maxClasses = Number(opt('--max-classes', '50000')), fuelPer = Number(opt('--fuel', '20000'))
const T0 = performance.now(), ms = () => Math.round(performance.now() - T0)
const out: Record<string, unknown> = {task}
const say = (o: object) => console.log(JSON.stringify({stage: 'progress', task, ms: ms(), ...o}))
const done = (o: object = {}) => { console.log(JSON.stringify({stage: 'result', ms: ms(), ...out, ...o})); process.exit(0) }

let tip: Tip
try { tip = parseTip(readFileSync(file, 'utf8')) } catch (e) { done({error: e instanceof Unsupported ? `unsupported: ${e.message}` : `parse: ${(e as Error).message}`}) }
const P = tip!

// --- the element type and ground types ---------------------------------------------------------------------------------
const peano = [...P.datas.values()].find(d => {
  if (d.params.length || d.ctors.length !== 2) return false
  const [a, b] = [...d.ctors].sort((x, y) => x.fields.length - y.fields.length)
  return a!.fields.length === 0 && b!.fields.length === 1 && showTy(b!.fields[0]!.ty) === d.name
})
const ELEM: Ty = peano ? {k: 'con', name: peano.name, args: []} : INT
out.elem = showTy(ELEM)
const ground = (t: Ty, params: string[]): Ty => substTy(t, new Map(params.map(p => [p, ELEM])))
const key = (t: Ty) => showTy(t)

// --- the signature -------------------------------------------------------------------------------------------------------
type Sym = {name: string, args: Ty[], ret: Ty, kind: 'fun' | 'ctor' | 'eq' | 'const' | 'builtin'}
const goal = prenex(P.goal.body), goalTv = new Set(P.goal.params)
const goalVars = goal.vars.map(v => ({name: v.name, ty: ground(tyOf(v.ty, goalTv), P.goal.params)}))
const calls = (s: Sx, acc: Set<string>) => { if (typeof s === 'string') { if (P.funs.has(s)) acc.add(s); return } s.forEach(x => calls(x, acc)) }
const used = new Set<string>()
calls(goal.body, used)
for (let grew = true; grew;) { grew = false; for (const f of [...used]) { const n = used.size; calls(P.funs.get(f)!.body, used); if (used.size > n) grew = true } }
const skipped: string[] = []
const syms: Sym[] = []
for (const f of used) {
  const d = P.funs.get(f)!
  if (d.args.some(a => a.ty.k === 'fun') || d.ret.k === 'fun') { skipped.push(f); continue }
  syms.push({name: f, args: d.args.map(a => ground(a.ty, d.params)), ret: ground(d.ret, d.params), kind: d.args.length ? 'fun' : 'const'})
}
// datatypes reached by the signature's types (and their fields'), each at its ground instance
const types = new Map<string, Ty>()
const reach = (t: Ty) => {
  if (t.k !== 'con' || types.has(key(t))) return
  types.set(key(t), t)
  t.args.forEach(reach)
  const d = P.datas.get(t.name)
  if (d) { const m = new Map(d.params.map((p, i) => [p, t.args[i]!])); for (const c of d.ctors) for (const f of c.fields) reach(substTy(f.ty, m)) }
}
for (const s of syms) { s.args.forEach(reach); reach(s.ret) }
goalVars.forEach(v => reach(v.ty))
for (const t of types.values()) {
  if (t.k !== 'con') continue
  const d = P.datas.get(t.name)
  if (!d) continue
  const m = new Map(d.params.map((p, i) => [p, t.args[i]!]))
  for (const c of d.ctors) syms.push({name: c.name, args: c.fields.map(f => substTy(f.ty, m)), ret: t, kind: c.fields.length ? 'ctor' : 'const'})
}
const goalTypes = new Set(goalVars.filter(v => v.ty.k !== 'fun').map(v => key(v.ty)))
for (const k of goalTypes) syms.push({name: '=', args: [types.get(k)!, types.get(k)!], ret: BOOL, kind: 'eq'})
syms.push({name: 'true', args: [], ret: BOOL, kind: 'builtin'}, {name: 'false', args: [], ret: BOOL, kind: 'builtin'})
// a constructor name may be shared by two instances (nil at two lists): the term is the same text, typed apart
out.signature = {funs: syms.filter(s => s.kind === 'fun' || (s.kind === 'const' && P.funs.has(s.name))).map(s => s.name), ctors: syms.filter(s => s.kind === 'ctor' || (s.kind === 'const' && !P.funs.has(s.name))).map(s => `${s.name}:${key(s.ret)}`), eqAt: [...goalTypes], skipped}

// --- variables and random values -------------------------------------------------------------------------------------
const varTypes = [...types.values()].filter(t => t.k === 'con' && t.name !== 'Bool' && syms.some(s => s.args.some(a => key(a) === key(t))))
for (const k of goalTypes) if (!varTypes.some(t => key(t) === k)) varTypes.push(types.get(k)!)
// 3 variables of a type where the goal has one of it or (--vars-from-lemmas) a lemma reads 3 of it; 2 otherwise
const lemmaTexts = (JSON.parse(readFileSync(opt('--lemmas', 'compare/tip/lemmas-sample30.json'), 'utf8')) as Record<string, string[]>)[task] ?? []
const needs3 = new Set<string>()
if (args.includes('--vars-from-lemmas')) for (const text of lemmaTexts) {
  try {
    let s = parseSx(text)[0]!, tv = new Set<string>(), tps: string[] = []
    if (Array.isArray(s) && s[0] === 'par') { tps = s[1] as string[]; tv = new Set(tps); s = s[2]! }
    const c = new Map<string, number>()
    for (const v of prenex(s).vars) { const k = key(ground(tyOf(v.ty, tv), tps)); c.set(k, (c.get(k) ?? 0) + 1) }
    for (const [k, n] of c) if (n >= 3) needs3.add(k)
  } catch { /* read again below, where its failure is recorded */ }
}
const nVars = (t: Ty) => (goalTypes.has(key(t)) || needs3.has(key(t)) ? 3 : 2)
const vars: {name: string, ty: Ty}[] = []
varTypes.forEach((t, i) => { for (let j = 0; j < nVars(t); j++) vars.push({name: `$v${i}_${j}`, ty: t}) })
out.vars = varTypes.map(t => `${key(t)}×${nVars(t)}`)
let seed = 12345
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
function gen(t: Ty, size: number): V {
  if (t.k !== 'con') throw new Unsupported(`a value of ${showTy(t)}`)
  if (t.name === 'Int') return BigInt(rand(7))
  if (t.name === 'Bool') return rand(2) === 1
  const d = P.datas.get(t.name)
  if (!d) throw new Unsupported(`a value of the sort ${t.name}`)
  const m = new Map(d.params.map((p, i) => [p, t.args[i]!]))
  const self = (ft: Ty) => ft.k === 'con' && ft.name === t.name
  const rec = (c: typeof d.ctors[number]) => c.fields.some(f => self(substTy(f.ty, m)))
  const base = d.ctors.filter(c => !rec(c)), recs = d.ctors.filter(rec)
  // the depth along the first recursive field is `size` exactly (a natural of size n, a list of n items); the other
  // recursive fields (a tree's) take a smaller size drawn at random
  const pool = size <= 0 ? (base.length ? base : d.ctors) : recs.length ? recs : d.ctors
  const c = pool[rand(pool.length)]!
  let first = true
  return {c: c.name, a: c.fields.map(f => { const ft = substTy(f.ty, m); if (!self(ft)) return gen(ft, rand(4)); const n = first ? size - 1 : rand(Math.max(1, size)); first = false; return gen(ft, n) })}
}
// sizes: a draw of 0..7 per value (naturals 0..7, lists of 0..7 items, a tree's depth up to 7); a field of another
// datatype (a list's item) a draw of 0..3
const valuation = (): Map<string, V> => new Map(vars.map(v => [v.name, gen(v.ty, rand(8))]))
let rows: Map<string, V>[]
try { rows = Array.from({length: N}, valuation) } catch (e) { done({error: `values: ${(e as Error).message}`}) }

// --- evaluation --------------------------------------------------------------------------------------------------------
const ERR = {c: '$error', a: []} as V
let errors = 0
let evalMs = 0, fpMs = 0
const applyRaw = (s: Sym, xs: V[]): V => {
  if (s.kind === 'eq') return xs.some(x => x === ERR) ? ERR : sameV(xs[0]!, xs[1]!)
  if (s.kind === 'builtin') return s.name === 'true'
  if (xs.some(x => x === ERR)) return ERR
  const env = new Map<string, V>(xs.map((x, i) => [`$a${i}`, x]))
  try { return evaluate(P, xs.length ? [s.name, ...xs.map((_, i) => `$a${i}`)] : s.name, env, {n: fuelPer}) } catch (e) {
    if (e instanceof OutOfFuel || e instanceof RangeError || (e as Error).message?.includes('selector')) { errors++; return ERR }
    errors++; return ERR
  }
}
const apply = (s: Sym, xs: V[]): V => { const t = performance.now(); try { return applyRaw(s, xs) } finally { evalMs += performance.now() - t } }
const fpOf = (vs: V[]) => vs.map(v => (v === ERR ? '!' : showV(v))).join('|')
// every column of the size being enumerated (for the GPU fingerprint pass, --fp-target)
let lastCols: {ty: string, vals: V[]}[] = []

// --- enumeration (Q4) --------------------------------------------------------------------------------------------------
type Cls = {term: Sx, size: number, vals: V[], ty: string}
const classes = new Map<string, Cls>()               // `${type}#${fingerprint}` → its representative
const bySize = new Map<string, Cls[][]>()             // type → representatives by size
const reps = (ty: string, size: number) => bySize.get(ty)?.[size] ?? []
const eqs: {l: Sx, r: Sx, size: number}[] = []
const sizes: {size: number, terms: number, classes: number, eqs: number, ms: number, complete: boolean}[] = []
let cut: string | undefined
const addTerm = (term: Sx, size: number, ty: string, vals: V[]): void => {
  if (lastCols.length < 200000) lastCols.push({ty, vals})
  const tf = performance.now(), k = `${ty}#${fpOf(vals)}`, c = classes.get(k)
  fpMs += performance.now() - tf
  if (c) { if (typeof term !== 'string') eqs.push({l: term, r: c.term, size}); return }
  const cl = {term, size, vals, ty}
  classes.set(k, cl)
  if (!bySize.has(ty)) bySize.set(ty, [])
  const arr = bySize.get(ty)!
  while (arr.length <= size) arr.push([])
  arr[size]!.push(cl)
}
// compositions of n into k positive parts
const parts = (n: number, k: number): number[][] => (k === 0 ? (n === 0 ? [[]] : []) : Array.from({length: Math.max(0, n - k + 1)}, (_, i) => i + 1).flatMap(f => parts(n - f, k - 1).map(r => [f, ...r])))
for (let size = 1; size <= maxSize && !cut; size++) {
  const t0 = performance.now(), before = classes.size, eq0 = eqs.length
  lastCols = []
  let terms = 0
  if (size === 1) {
    for (const v of vars) { addTerm(v.name, 1, key(v.ty), rows!.map(r => r.get(v.name)!)); terms++ }
    for (const s of syms) if (!s.args.length) { const v = apply(s, []); addTerm(s.name, 1, key(s.ret), rows!.map(() => v)); terms++ }
  } else {
    outer: for (const s of syms) {
      if (!s.args.length) continue
      for (const p of parts(size - 1, s.args.length)) {
        const lists = s.args.map((a, i) => reps(key(a), p[i]!))
        if (lists.some(l => !l.length)) continue
        // every combination of representatives
        const idx = lists.map(() => 0)
        for (;;) {
          const chosen = idx.map((j, i) => lists[i]![j]!)
          const vals = rows!.map((_, r) => apply(s, chosen.map(c => c.vals[r]!)))
          addTerm([s.name, ...chosen.map(c => c.term)], size, key(s.ret), vals)
          terms++
          if ((terms & 255) === 0 && (performance.now() - T0 > budgetMs || classes.size > maxClasses)) { cut = performance.now() - T0 > budgetMs ? `time at size ${size}` : `classes past ${maxClasses} at size ${size}`; break outer }
          let i = idx.length - 1
          while (i >= 0 && ++idx[i]! >= lists[i]!.length) idx[i--] = 0
          if (i < 0) break
        }
      }
    }
  }
  sizes.push({size, terms, classes: classes.size - before, eqs: eqs.length - eq0, ms: Math.round(performance.now() - t0), complete: !cut})
  say({size, terms, classes: classes.size, eqs: eqs.length, complete: !cut})
}
out.sizes = sizes
out.classes = classes.size
out.equations = eqs.length
out.evalErrors = errors
out.cut = cut ?? null
const reached = sizes.filter(s => s.complete).at(-1)?.size ?? 0
out.completeTo = reached
out.evalMs = Math.round(evalMs); out.fpMs = Math.round(fpMs)

// --- Q4's fingerprints on the GPU (--fp-target gpu|cpu): the last size's columns, each value interned to a number,
// fingerprinted by gpu.ts's columns kernel (two sums mod a prime over the rows), grouped, and each group checked
// exactly on the rows; against the CPU's grouping by the values' text
if (args.includes('--fp-target')) {
  const g = await import('./gpu.ts')
  const tg = performance.now(), target = opt('--fp-target', 'cpu') === 'gpu' ? await g.gpuTarget() : {kind: 'cpu' as const}
  const fp: Record<string, unknown> = {target: target.kind, setupMs: Math.round(performance.now() - tg), columns: lastCols.length, rows: rows!.length}
  const K = lastCols.length, R = rows!.length
  const tc = performance.now(), cpuGroups = new Map<string, number[]>()
  lastCols.forEach((c, j) => { const k = `${c.ty}#${fpOf(c.vals)}`; const a = cpuGroups.get(k); if (a) a.push(j); else cpuGroups.set(k, [j]) })
  fp.cpuMs = Math.round(performance.now() - tc)
  const ti = performance.now(), ids = new Map<string, number>(), mat = new Int32Array(R * K)
  lastCols.forEach((c, j) => c.vals.forEach((v, r) => { const key = v === ERR ? '!' : showV(v); let id = ids.get(key); if (id === undefined) { id = ids.size + 1; ids.set(key, id) } mat[r * K + j] = id }))
  fp.internMs = Math.round(performance.now() - ti)
  const Pg = g.columnsProgram(K, R, K, 8, 128), cols = lastCols.map((_, j) => ({idx: [j], coef: [1]}))
  const shared = Pg.fill(mat, R, cols), docs = Pg.docs(R)
  const t1 = performance.now(), run = await g.runnerOf(target, Pg.loop, docs, Pg.vpd)
  fp.compileMs = Math.round(performance.now() - t1)
  const t2 = performance.now(), o = await run.run(shared, docs)
  fp.runMs = Math.round(performance.now() - t2)
  run.destroy()
  const t3 = performance.now(), res = g.combineColumns(o, K, Pg.nb, Pg.CB, docs), groups = new Map<string, number[]>()
  for (let j = 0; j < K; j++) { const k = `${lastCols[j]!.ty}#${res.h1[j]},${res.h2[j]}`; const a = groups.get(k); if (a) a.push(j); else groups.set(k, [j]) }
  // each group split by exact equality of the values (the recheck): false merges are members unlike the first
  const exact: number[][] = []
  for (const grp of groups.values()) {
    const left = [...grp]
    while (left.length) { const a = left.shift()!, same = [a]; for (let i = left.length - 1; i >= 0; i--) { const b = left[i]!; if (lastCols[a]!.vals.every((v, r) => v === ERR ? lastCols[b]!.vals[r] === ERR : lastCols[b]!.vals[r] !== ERR && sameV(v, lastCols[b]!.vals[r]!))) { same.push(b); left.splice(i, 1) } } exact.push(same) }
  }
  fp.groupAndRecheckMs = Math.round(performance.now() - t3)
  // the two partitions agree?
  const norm = (gs: number[][]) => gs.map(x => [...x].sort((a, b) => a - b).join(',')).sort().join('|')
  fp.partitionsAgree = norm(exact) === norm([...cpuGroups.values()])
  fp.gpuClasses = exact.length; fp.cpuClasses = cpuGroups.size; fp.fingerprintGroups = groups.size; fp.falseMerges = exact.length - groups.size  // classes a fingerprint group held beyond one
  out.fp = fp
  say({stage: 'fp', ...fp})
}

// --- the lemmas ----------------------------------------------------------------------------------------------------------
const symbols = (s: Sx): number => (typeof s === 'string' ? 1 : s[0] === '_' || s[0] === 'as' ? 1 : (Array.isArray(s[0]) ? 1 : 1) + s.slice(1).reduce((a: number, x) => a + symbols(x), 0))
const lemmas = lemmaTexts
type Outcome = {lemma: string, kind: string, sizes?: number[], found: boolean | null, why?: string, part?: number}
const outcomes: Outcome[] = []
// a term's values on the rows, the lemma's variables mapped to the table's of their type (in order)
const valsOn = (s: Sx, env: (r: number) => Map<string, V>): V[] => rows!.map((_, r) => { try { return evaluate(P, s, env(r), {n: fuelPer * 20}) } catch { return ERR } })
const inClass = (ty: string, vals: V[]) => classes.get(`${ty}#${fpOf(vals)}`)
for (const text of lemmas) {
  const o: Outcome = {lemma: text, kind: '?', found: null}
  outcomes.push(o)
  try {
    let s = parseSx(text)[0]!, tv = new Set<string>(), tps: string[] = []
    if (Array.isArray(s) && s[0] === 'par') { tps = s[1] as string[]; tv = new Set(tps); s = s[2]! }
    const pre = prenex(s), lvars = pre.vars.map(v => ({name: v.name, ty: ground(tyOf(v.ty, tv), tps)}))
    // the lemma's variables onto the table's
    const map = new Map<string, string>(), count = new Map<string, number>()
    for (const v of lvars) {
      const k = key(v.ty), j = count.get(k) ?? 0, mine = vars.filter(x => key(x.ty) === k)
      if (j >= mine.length) throw new Error(`needs ${j + 1} variables of ${k}, the table has ${mine.length}`)
      map.set(v.name, mine[j]!.name); count.set(k, j + 1)
    }
    const env = (r: number) => new Map([...map].map(([a, b]) => [a, rows![r]!.get(b)!]))
    const tyOfTerm = (t: Sx): string => {
      if (typeof t === 'string') {
        const v = lvars.find(x => x.name === t)
        if (v) return key(v.ty)
        if (t === 'true' || t === 'false') return 'Bool'
        const c = syms.find(x => x.name === t && !x.args.length)
        if (c) return key(c.ret)
        throw new Error(`the symbol ${t} isn't in the signature`)
      }
      if (Array.isArray(t[0]) || t[0] === '_') return tyOfTerm((Array.isArray(t[0]) ? t[0][1] : t[1]) as Sx)
      if (t[0] === '=' || t[0] === 'not' || t[0] === 'and' || t[0] === 'or' || t[0] === '=>' || t[0] === 'distinct') return 'Bool'
      const cands = syms.filter(x => x.name === t[0] && x.args.length === t.length - 1)
      if (!cands.length) throw new Error(`the function ${String(t[0])} isn't in the signature`)
      if (cands.length === 1) return key(cands[0]!.ret)
      const at = t.slice(1).map(tyOfTerm), c = cands.find(x => x.args.every((a, i) => key(a) === at[i]))
      if (!c) throw new Error(`no instance of ${String(t[0])} at ${at.join(', ')}`)
      return key(c.ret)
    }
    // a column of the table: the term's class, where the enumeration reached it
    const column = (t: Sx) => { const ty = tyOfTerm(t), vals = valsOn(t, env); return {ty, vals, cls: inClass(ty, vals), size: symbols(t)} }
    const equation = (l: Sx, r: Sx): {found: boolean, sizes: number[], why?: string} => {
      const a = column(l), b = column(r)
      const sizes = [a.size, b.size]
      if (!a.cls) return {found: false, sizes, why: `the left side's class wasn't reached (size ${a.size}, enumeration complete to ${reached})`}
      if (!b.cls) return {found: false, sizes, why: `the right side's class wasn't reached (size ${b.size}, enumeration complete to ${reached})`}
      return a.cls === b.cls ? {found: true, sizes} : {found: false, sizes, why: 'the two sides differ on the rows'}
    }
    const body = pre.body
    const isEq = (t: Sx) => Array.isArray(t) && t[0] === '=' && t.length === 3
    // a split (Q5): the rows where every hypothesis holds; c checked there as an equation of columns or a true column
    const splitCheck = (hyps: Sx[], c: Sx, polarity = true) => {
      const hs = hyps.map(column)
      const missing = hs.findIndex(h => !h.cls)
      const part = rows!.map((_, r) => r).filter(r => hs.every(h => h.vals[r] === polarity))
      o.part = part.length
      if (missing >= 0) { o.found = false; o.why = `the hypothesis column ${show(hyps[missing]!)} wasn't reached (size ${hs[missing]!.size})`; return }
      const cs = isEq(c) ? [column((c as Sx[])[1]!), column((c as Sx[])[2]!)] : [column(c)]
      o.sizes = [...hs.map(h => h.size), ...cs.map(x => x.size)]
      if (cs.some(x => !x.cls)) { o.found = false; o.why = 'a column of the conclusion wasn\'t reached'; return }
      const holdsOnPart = part.every(r => (cs.length === 2 ? sameOrErr(cs[0]!.vals[r]!, cs[1]!.vals[r]!) : cs[0]!.vals[r] === true))
      o.found = holdsOnPart && part.length >= 5
      if (!o.found) o.why = part.length < 5 ? `the hypothesis holds on ${part.length} of ${N} rows (fewer than 5)` : 'the conclusion fails on the part'
    }
    if (isEq(body)) {
      o.kind = 'equation (Q4)'
      const r = equation((body as Sx[])[1]!, (body as Sx[])[2]!)
      o.found = r.found; o.sizes = r.sizes; if (r.why) o.why = r.why
    } else if (Array.isArray(body) && body[0] === '=>') {
      const hyp = body[1]!, c = body[2]!
      const hyps = Array.isArray(hyp) && hyp[0] === 'and' ? hyp.slice(1) : [hyp]
      o.kind = hyps.length > 1 ? 'implication of two (Q5 depth 2)' : 'implication (Q5 depth 1)'
      splitCheck(hyps, c)
    } else if (Array.isArray(body) && body[0] === 'or' && body.length === 3) {
      o.kind = 'disjunction of two (Q5: ¬a ⇒ b)'
      splitCheck([body[1]!], body[2]!, false)
    } else if (Array.isArray(body) && body[0] === 'distinct') {
      o.kind = 'disequation (Q4: the = column equal to false)'
      const a = column(['=', body[1]!, body[2]!])
      o.sizes = [a.size]
      const f = inClass('Bool', rows!.map(() => false))
      o.found = !!a.cls && a.cls === f
      if (!o.found) o.why = a.cls ? 'the = column isn\'t constantly false' : `the = column wasn't reached (size ${a.size})`
    } else {
      o.kind = 'boolean (Q2 on a 0/1 column: equal to true)'
      const a = column(body)
      o.sizes = [a.size]
      const t = inClass('Bool', rows!.map(() => true))
      o.found = !!a.cls && a.cls === t
      if (!o.found) o.why = a.cls ? 'the column isn\'t constantly true' : `the column wasn't reached (size ${a.size})`
    }
  } catch (e) { o.found = null; o.why = `doesn't fit: ${(e as Error).message}` }
}
function sameOrErr(a: V, b: V) { return a !== ERR && b !== ERR && sameV(a, b) }
out.lemmas = outcomes

// --- false positives: equations re-checked on 1,000 fresh valuations ----------------------------------------------------
{
  const fresh = Array.from({length: 1000}, valuation)
  const check = (es: typeof eqs) => {
    const stride = Math.max(1, Math.ceil(es.length / 300))
    let n = 0, bad = 0
    for (let i = 0; i < es.length && performance.now() - T0 < budgetMs * 1.4; i += stride) {
      const e = es[i]!
      n++
      for (const env of fresh) {
        let a: V, b: V
        try { a = evaluate(P, e.l, env, {n: fuelPer}) } catch { a = ERR }
        try { b = evaluate(P, e.r, env, {n: fuelPer}) } catch { b = ERR }
        if (a === ERR || b === ERR ? a !== b : !sameV(a, b)) { bad++; break }
      }
    }
    return {checked: n, of: es.length, false: bad}
  }
  const top = eqs.length ? Math.max(...eqs.map(e => e.size)) : 0
  out.falsePositives = {all: check(eqs), atLargest: {size: top, ...check(eqs.filter(e => e.size === top))}}
}
done()
