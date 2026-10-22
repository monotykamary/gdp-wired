// The table on one CHC-COMP task: `bun research/table/chc.ts <task.smt2> --model <spacer model file> [--sample-ms 10000]`.
// Prints one JSON line per stage and a last one with everything measured.
//   sample   runs of the CHC system, each step a model of one clause's constraint where the run is (Z3 solving the
//            guard), some of the head's values fixed at random first (solve.ts's guided runs, Z3 in place of the
//            kernel's grow); the distinct states reached per predicate are the rows
//   table    per predicate: the grammar's columns over its slots (Int i0.., Bool b0.. as 0/1, translate.ts's names)
//   queries  L0 = Q1 + Q2 over every column; L1 = L0 + Q5 split by one atom; L2 = L1 + Q5 split by two
//   recover  does L_k imply Spacer's interpretation of each predicate (Z3)? — "on the samples": L_k may hold of
//            every sample and not be an invariant
//   houdini  the largest subset of L2's relations inductive over the clauses (Z3: each clause's step, the facts), and
//            whether it is safe (every query clause unsatisfiable under it) and implies Spacer's
import {readFileSync} from 'node:fs'
import {parseChc, Unsupported, type Sx as CSx, type Sort} from '../../compare/chc/chc.ts'
import {Z3, parseSx, show, sym, getValues, type Sx} from './z3.ts'
import {type Lin, type Rel, type Term, type Row, type Atom, grammar, observe, equalities, bounds, boundRels, split, atomsOf, holes, holds, equalColumns, smtTerm} from './table.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: string) => { const i = args.indexOf(k); return i < 0 ? d : args[i + 1]! }
const sampleMs = Number(opt('--sample-ms', '10000')), modelFile = opt('--model', ''), deadline = Number(opt('--deadline-ms', '400000'))
const T0 = performance.now(), ms = () => Math.round(performance.now() - T0)
const out: Record<string, unknown> = {task: opt('--task', file)}
const say = (o: object) => console.log(JSON.stringify({stage: 'progress', ms: ms(), ...o}))
const done = (o: object = {}) => { console.log(JSON.stringify({stage: 'result', ms: ms(), ...out, ...o})); process.exit(0) }

let chc
try { chc = parseChc(readFileSync(file, 'utf8')) } catch (e) { done({error: e instanceof Unsupported ? `unsupported: ${e.message}` : `parse: ${(e as Error).message}`}) }
const C = chc!
const predNames = [...C.preds.keys()]
const slotsOf = (p: string): {name: string, sort: Sort}[] => { const n = {Int: 0, Bool: 0}; return C.preds.get(p)!.map(s => ({name: `${s === 'Int' ? 'i' : 'b'}${n[s]++}`, sort: s})) }
const SLOTS = new Map(predNames.map(p => [p, slotsOf(p)]))

// --- Z3 text of the clauses: each clause's variables renamed apart (c<j>!<name>) and declared once -----------------------
const rename = (s: CSx, m: Map<string, string>, bound = new Set<string>()): Sx => {
  if (typeof s === 'string') return bound.has(s) ? s : m.get(s) ?? s
  if (s[0] === 'let') { const bs = s[1] as CSx[][], inner = new Set([...bound, ...bs.map(b => b[0] as string)]); return ['let', bs.map(b => [b[0] as string, rename(b[1]!, m, bound)]), rename(s[2]!, m, inner)] }
  if (s[0] === 'exists' || s[0] === 'forall') { const bs = s[1] as CSx[][], inner = new Set([...bound, ...bs.map(b => b[0] as string)]); return [s[0], bs as Sx[], rename(s[2]!, m, inner)] }
  return s.map(x => rename(x, m, bound))
}
const clauses = C.clauses.map((c, j) => {
  const m = new Map([...c.vars.keys()].map(v => [v, `c${j}!${v}`]))
  const decls = [...c.vars].map(([v, s]) => `(declare-const ${sym(m.get(v)!)} ${s})`)
  const body = c.body[0] ? {pred: c.body[0].pred, args: c.body[0].args.map(a => show(rename(a, m)))} : undefined
  const head = c.head ? {pred: c.head.pred, args: c.head.args.map(a => show(rename(a, m)))} : undefined
  const constraint = c.constraint.length ? `(and true ${c.constraint.map(x => show(rename(x, m))).join(' ')})` : 'true'
  return {j, decls, body, head, constraint, nonlinear: c.body.length > 1}
})
if (clauses.some(c => c.nonlinear)) done({error: 'a clause with two or more body predicates (not linear)'})
const declText = clauses.flatMap(c => c.decls).join('\n')

// --- sampling ----------------------------------------------------------------------------------------------------------
type St = {pred: string, vals: (bigint | boolean)[]}
const seen = new Map(predNames.map(p => [p, new Map<string, St>()]))
let rx = 7
const rand = (k: number) => { rx = (rx * 1103515245 + 12345) % 2 ** 31; return Math.floor(rx / 2 ** 31 * k) }
const lit = (v: bigint | boolean) => (typeof v === 'boolean' ? String(v) : v < 0n ? `(- ${-v})` : `${v}`)
const S = new Z3(1000)
S.send(declText)
let samplerSteps = 0, samplerUnknown = 0
async function stepOf(c: typeof clauses[number], st: St | undefined, hints: Map<number, bigint | boolean>): Promise<St | undefined> {
  const parts: string[] = ['(push 1)']
  if (c.body && st) c.body.args.forEach((a, k) => parts.push(`(assert (= ${a} ${lit(st.vals[k]!)}))`))
  parts.push(`(assert ${c.constraint})`)
  for (const [k, v] of hints) parts.push(`(assert (= ${c.head!.args[k]} ${lit(v)}))`)
  S.send(parts.join('\n'))
  const r = await S.check()
  samplerSteps++
  let res: St | undefined
  if (r === 'sat') res = {pred: c.head!.pred, vals: await getValues(S, c.head!.args)}
  if (r === 'unknown') samplerUnknown++
  S.send('(pop 1)')
  return res
}
{
  const facts = clauses.filter(c => !c.body && c.head), steps = clauses.filter(c => c.body && c.head)
  await S.check()  // Z3 started: the budget counts from here
  const until = performance.now() + sampleMs
  let trials = 0, stale = 0
  const record = (s: St) => { const m = seen.get(s.pred)!, key = s.vals.map(String).join(','); if (m.has(key)) return false; if (m.size < 3000) m.set(key, s); return true }
  while (performance.now() < until && facts.length && stale < 40) {
    trials++
    const bound = 1 << Math.min(10, 1 + Math.floor(trials / 4))
    let fresh = false
    const hintsFor = (c: typeof clauses[number], st: St | undefined, tries: number) => {
      const h = new Map<number, bigint | boolean>()
      if (tries >= 4) return h
      const sorts = C.preds.get(c.head!.pred)!, cur = (st?.vals ?? []).filter(v => typeof v === 'bigint') as bigint[]
      sorts.forEach((s, k) => {
        if (rand(2)) return
        if (s === 'Bool') { h.set(k, rand(2) === 1); return }
        const pool = [0n, 1n, -1n, ...cur, ...cur.map(v => v + 1n), ...cur.map(v => v - 1n), BigInt(rand(2 * bound + 1) - bound)]
        h.set(k, pool[rand(pool.length)]!)
      })
      return h
    }
    let st: St | undefined
    const f = facts[rand(facts.length)]!
    for (let tries = 0; tries < 5 && !st; tries++) st = await stepOf(f, undefined, hintsFor(f, undefined, tries))
    if (!st) { stale++; continue }
    if (record(st)) fresh = true
    for (let d = 0; d < 64 && performance.now() < until; d++) {
      const here = st!.pred, choices = steps.filter(c => c.body!.pred === here)
      if (!choices.length) break
      let next: St | undefined
      for (let tries = 0; tries < 5 && !next; tries++) { const c = choices[rand(choices.length)]!; next = await stepOf(c, st, hintsFor(c, st, tries)) }
      if (!next) break
      st = next
      if (record(st)) fresh = true
    }
    stale = fresh ? 0 : stale + 1
  }
  out.sample = {ms: ms(), trials, steps: samplerSteps, unknown: samplerUnknown, states: Object.fromEntries([...seen].map(([p, m]) => [p, m.size]))}
  say({stage: 'sample', ...out.sample as object})
}
S.kill()

// --- tables and queries ------------------------------------------------------------------------------------------------
type PredTable = {pred: string, terms: Term[], t: ReturnType<typeof observe>, rowsData: Row[], atomList: Atom[], rows: number, cols: {L0: number, L1: number, L2: number}, atoms: number, levels: {L0: Rel[], L1: Rel[], L2: Rel[]}}
const tables: PredTable[] = []
const tq0 = performance.now()
for (const p of predNames) {
  const slots = SLOTS.get(p)!, ints = slots.filter(s => s.sort === 'Int').map(s => s.name), boolsN = slots.filter(s => s.sort === 'Bool').map(s => s.name)
  const rows: Row[] = [...seen.get(p)!.values()].map(st => Object.fromEntries(slots.map((s, k) => [s.name, typeof st.vals[k] === 'boolean' ? (st.vals[k] ? 1n : 0n) : st.vals[k] as bigint])))
  const n = ints.length
  const terms = grammar(ints, boolsN, {upTo: n <= 6 ? 4 : n <= 8 ? 3 : 2, coef: 3, mods: [2n, 3n, 4n], caps: {pairs: 40, three: 8, four: 6, coefPairs: 8, mods: 12}})
  const t = observe(terms, rows)
  const base = terms.map((_, i) => i).filter(i => terms[i]!.k === 'var'), all = terms.map((_, i) => i)
  const L0: Rel[] = []
  if (rows.length) {
    for (const l of equalities(t, base)) L0.push({guard: [], rel: l, query: 'Q1'})
    for (const l of boundRels(bounds(t, all))) L0.push({guard: [], rel: l, query: 'Q2'})
  }
  // atoms: the 0/1 columns, the columns of few values (each value), the signs of differences of two (n <= 8)
  const pairCols = all.filter(i => { const x = terms[i]!; return x.k === 'lin' && x.terms.length === 2 && x.terms.every(([, c]) => c === 1n || c === -1n) })
  const atoms: Atom[] = rows.length ? [...atomsOf(t, base.filter(i => boolsN.includes((terms[i] as {name: string}).name))), ...atomsOf(t, base.filter(i => ints.includes((terms[i] as {name: string}).name)), 12)] : []
  if (n <= 8) for (const c of pairCols) { const x = terms[c] as {k: 'lin', terms: [string, bigint][]}; if (x.terms[1]![1] === -1n) atoms.push({col: c, op: '<=', c: 0n, neg: false}) }
  const A = atoms.slice(0, 32)
  const b1 = n <= 8 ? [...base, ...pairCols] : base, b2 = n <= 6 ? [...base, ...pairCols] : base
  let L1: Rel[] = [], L2: Rel[] = []
  if (rows.length && A.length) {
    const s = split(t, A, {eqCols: base, boundCols: b1, depth2: 0})
    L1 = [...s.depth1, ...holes(t, base.filter(i => ints.includes((terms[i] as {name: string}).name)))]
    const s2 = split(t, A.slice(0, 8), {eqCols: base, boundCols: b2, depth2: 8})
    L2 = s2.depth2
  }
  tables.push({pred: p, terms, t, rowsData: rows, atomList: A, rows: rows.length, cols: {L0: all.length, L1: b1.length, L2: b2.length}, atoms: A.length, levels: {L0, L1: [...L0, ...L1], L2: [...L0, ...L1, ...L2]}})
}
out.table = {ms: Math.round(performance.now() - tq0), preds: tables.map(t => ({pred: t.pred, rows: t.rows, cols: t.cols, atoms: t.atoms, L0: t.levels.L0.length, L1: t.levels.L1.length, L2: t.levels.L2.length}))}
say({stage: 'table', ...out.table as object})

// --- the GPU passes (--table-target gpu|cpu): the sparse linear columns' bounds and fingerprints, and the atoms'
// implications, on Handwired's kernels; each checked against the exact CPU table (the queries above use the CPU's
// values whatever these say) and the GPU against its JavaScript twin
if (args.includes('--table-target')) {
  const g = await import('./gpu.ts')
  const tg = performance.now(), target = opt('--table-target', 'cpu') === 'gpu' ? await g.gpuTarget() : {kind: 'cpu' as const}
  const res: Record<string, unknown>[] = []
  const setupMs = Math.round(performance.now() - tg)
  for (const pt of tables) {
    if (!pt.rows) continue
    const slots = SLOTS.get(pt.pred)!, names = slots.map(x => x.name), V = names.length, R = pt.rows
    const sparse = pt.terms.map((x, i) => [x, i] as const).filter(([x]) => x.k === 'var' || (x.k === 'lin' && x.terms.length <= 4))
    const cols = sparse.map(([x]) => (x.k === 'var' ? {idx: [names.indexOf(x.name)], coef: [1]} : {idx: (x as {terms: [string, bigint][]}).terms.map(([v]) => names.indexOf(v)), coef: (x as {terms: [string, bigint][]}).terms.map(([, c]) => Number(c))}))
    const rows = new Int32Array(R * V)
    let fits = true
    pt.rowsData.forEach((r, i) => names.forEach((n, k) => { const v = r[n]!; if (v > 0x7fffffffn || v < -0x80000000n) fits = false; rows[i * V + k] = Number(v) }))
    const st: Record<string, unknown> = {pred: pt.pred, rows: R, columns: cols.length, fits}
    res.push(st)
    if (!fits) continue
    // exact: the CPU table's columns and bounds for the same columns (timed again on just these)
    const te = performance.now(), sub = observe(sparse.map(([x]) => x), pt.rowsData), exact = bounds(sub)
    st.exactMs = Math.round(performance.now() - te)
    const P = g.columnsProgram(V, R, cols.length, 8, 256)
    const shared = P.fill(rows, R, cols), docs = P.docs(R)
    const t1 = performance.now(), run = await g.runnerOf(target, P.loop, docs, P.vpd)
    st.compileMs = Math.round(performance.now() - t1)
    const t2 = performance.now(), outw = await run.run(shared, docs)
    st.runMs = Math.round(performance.now() - t2)
    run.destroy()
    const gpu = g.combineColumns(outw, cols.length, P.nb, P.CB, docs), wts = P.weights()
    const t3 = performance.now(), js = g.columnsJs(rows, R, V, cols, wts.w1, wts.w2)
    st.jsMs = Math.round(performance.now() - t3)
    let twinDiff = 0, exactDiff = 0
    for (let j = 0; j < cols.length; j++) {
      if (gpu.lo[j] !== js.lo[j] || gpu.hi[j] !== js.hi[j] || gpu.h1[j] !== js.h1[j] || gpu.h2[j] !== js.h2[j]) twinDiff++
      if (BigInt(gpu.lo[j]!) !== exact[j]!.lo || BigInt(gpu.hi[j]!) !== exact[j]!.hi) exactDiff++
    }
    st.twinDiff = twinDiff; st.exactDiff = exactDiff
    // Q4 by fingerprints: groups of equal (h1, h2), each checked exactly on the rows
    const fp = new Map<string, number[]>()
    for (let j = 0; j < cols.length; j++) { const key = `${gpu.h1[j]},${gpu.h2[j]}`; const a = fp.get(key); if (a) a.push(j); else fp.set(key, [j]) }
    const cand = [...fp.values()].filter(x => x.length > 1)
    const t4 = performance.now()
    let falseMerges = 0
    for (const grp of cand) { const key0 = sub.cols[grp[0]!]!.join(','); for (const j of grp.slice(1)) if (sub.cols[j]!.join(',') !== key0) falseMerges++ }
    st.recheckMs = Math.round(performance.now() - t4)
    const te2 = performance.now(), truth = equalColumns(sub)
    st.exactQ4Ms = Math.round(performance.now() - te2)
    st.fpGroups = cand.length; st.falseMerges = falseMerges; st.exactGroups = truth.length
    // implications between atoms (0/1 columns and t = c atoms), as bitsets
    const atoms = pt.atomList
    if (atoms.length >= 2) {
      const NA = atoms.length, NW = Math.ceil(R / 32), bits = new Uint32Array(NA * NW)
      atoms.forEach((a, i) => { for (let r = 0; r < R; r++) if (holds(pt.t, a, r)) bits[i * NW + (r >>> 5)]! |= 1 << (r & 31) })
      const I = g.impliesProgram(NA, NW, 32)
      const t5 = performance.now(), ir = await g.runnerOf(target, I.loop, I.docs, I.CB)
      st.impliesCompileMs = Math.round(performance.now() - t5)
      const t6 = performance.now(), io = await ir.run(I.fill(bits), I.docs)
      st.impliesRunMs = Math.round(performance.now() - t6)
      ir.destroy()
      const t7 = performance.now(), ij = g.impliesJs(bits, NA, NW)
      st.impliesJsMs = Math.round(performance.now() - t7)
      let diff = 0, imp = 0
      for (let a = 0; a < NA; a++) for (let b = 0; b < NA; b++) { const v = io[(a * I.nb + Math.floor(b / I.CB)) * I.CB + (b % I.CB)] === 0 ? 1 : 0; if (v !== ij[a * NA + b]) diff++; if (v && a !== b) imp++ }
      st.atoms = NA; st.implications = imp; st.impliesTwinDiff = diff
    }
  }
  out.gpu = {target: target.kind, setupMs, adapter: target.kind === 'gpu' ? target.adapter : undefined, preds: res}
  say({stage: 'gpu', ...out.gpu as object})
  if (args.includes('--gpu-only')) done()
}

// --- relations as Z3 text over a predicate's parameters -----------------------------------------------------------------
const P = (p: string, k: number) => sym(`p!${k}`)
function relText(pt: PredTable, r: Rel): string {
  const slots = SLOTS.get(pt.pred)!, idx = new Map(slots.map((s, k) => [s.name, k]))
  const name = (x: string) => { const k = idx.get(x)!; return slots[k]!.sort === 'Bool' ? `(ite ${P(pt.pred, k)} 1 0)` : P(pt.pred, k) }
  const lin = (l: Lin) => {
    const ps = l.coefs.map(([c, x]) => `(* ${lit(x)} ${smtTerm(pt.terms[c]!, name)})`)
    if (!ps.length) return `(${l.op} ${lit(l.k)} 0)`
    return `(${l.op} (+ ${ps.join(' ')} ${lit(l.k)}) 0)`
  }
  const atom = (a: Atom) => { const s = `(${a.op} ${smtTerm(pt.terms[a.col]!, name)} ${lit(a.c)})`; return a.neg ? `(not ${s})` : s }
  const body = lin(r.rel)
  return r.guard.length ? `(=> (and ${r.guard.map(atom).join(' ')}) ${body})` : body
}
const params = (p: string) => SLOTS.get(p)!.map((s, k) => `(${P(p, k)} ${s.sort})`).join(' ')

// --- Spacer's interpretations --------------------------------------------------------------------------------------------
let spacerDefs = '', spacerHas = new Set<string>()
if (modelFile) {
  const want = String(out.task)
  let text = ''
  for (const line of readFileSync(modelFile, 'utf8').split('\n')) { if (!line) continue; const r = JSON.parse(line); if (r.task === want) { text = r.model; break } }
  const sx = parseSx(text)
  const list = sx.find(x => Array.isArray(x)) as Sx[] | undefined
  const defs = (list ?? []).filter(d => Array.isArray(d) && d[0] === 'define-fun') as Sx[][]
  const names = new Set(defs.map(d => d[1] as string))
  const ren = (s: Sx): Sx => (typeof s === 'string' ? (names.has(s) ? `spacer!${s}` : s) : s.map(ren))
  spacerDefs = defs.map(d => show(['define-fun', `spacer!${d[1] as string}`, d[2]!, d[3]!, ren(d[4]!)])).join('\n')
  spacerHas = new Set([...names].filter(n => C.preds.has(n)))
  out.spacer = {defs: defs.length, preds: spacerHas.size, chars: text.length}
}

// --- recovery on the samples: L_k ⇒ Spacer, per predicate ------------------------------------------------------------------
const Zc = new Z3(10000)
Zc.send(spacerDefs)
const recover: Record<string, Record<string, string>> = {}
const implies = (p: string, rels: string[], target: string) => impliesWith(Zc, p, rels, target)
async function impliesWith(Zc: Z3, p: string, rels: string[], target: string): Promise<string> {
  Zc.send(`(push 1)\n${SLOTS.get(p)!.map((s, k) => `(declare-const ${P(p, k)} ${s.sort})`).join('\n')}\n${rels.map(r => `(assert ${r})`).join('\n')}\n(assert (not ${target}))`)
  const r = await Zc.check()
  Zc.send('(pop 1)')
  return r === 'unsat' ? 'yes' : r === 'sat' ? 'no' : 'unknown'
}
const spacerAt = (p: string) => (!spacerHas.has(p) ? 'true' : SLOTS.get(p)!.length ? `(${sym(`spacer!${p}`)} ${SLOTS.get(p)!.map((_, k) => P(p, k)).join(' ')})` : sym(`spacer!${p}`))
if (modelFile && out.spacer && (out.spacer as {defs: number}).defs) {
  for (const lv of ['L0', 'L1', 'L2'] as const) {
    recover[lv] = {}
    for (const pt of tables) {
      if (performance.now() - T0 > deadline * 0.45) { recover[lv]![pt.pred] = 'deadline'; continue }
      // a predicate no run reached: the table's answer is false (no row), which implies anything
      recover[lv]![pt.pred] = pt.rows ? await implies(pt.pred, pt.levels[lv].map(r => relText(pt, r)), spacerAt(pt.pred)) : 'yes'
    }
  }
  out.recover = Object.fromEntries(Object.entries(recover).map(([lv, m]) => [lv, Object.values(m).every(v => v === 'yes') ? 'yes' : Object.values(m).some(v => v === 'no') ? 'no' : 'unknown']))
  out.recoverPreds = recover
  say({stage: 'recover', ...out.recover as object})
}

// --- Houdini over each level's relations (Z3): the largest inductive subset ------------------------------------------------
const zStats = {calls: 0, ms: 0}
async function houdini(level: 'L0' | 'L1' | 'L2', until: number): Promise<Record<string, unknown>> {
  const th = performance.now(), Zh = new Z3(10000)
  Zh.send(spacerDefs)
  const cand = new Map<string, string[]>(), alive = new Map<string, Set<number>>()
  let total = 0
  for (const pt of tables) {
    const lv = pt.levels[level]
    const texts = pt.rows ? [...new Set(lv.map(r => relText(pt, r)))] : ['false']
    cand.set(pt.pred, texts); alive.set(pt.pred, new Set(texts.map((_, k) => k))); total += texts.length
  }
  const defs: string[] = []
  for (const [p, texts] of cand) texts.forEach((t, k) => defs.push(`(define-fun ${sym(`K!${p}!${k}`)} (${params(p)}) Bool ${t})`))
  Zh.send(declText + '\n' + defs.join('\n'))
  const at = (p: string, k: number, argsT: string[]) => (argsT.length ? `(${sym(`K!${p}!${k}`)} ${argsT.join(' ')})` : sym(`K!${p}!${k}`))
  const conj = (p: string, argsT: string[]) => { const ks = [...alive.get(p)!]; return ks.length ? `(and true ${ks.map(k => at(p, k, argsT)).join(' ')})` : 'true' }
  let checks = 0, unknowns = 0, over = false
  for (let changed = true; changed && !over;) {
    changed = false
    for (const c of clauses) {
      if (!c.head) continue
      for (;;) {
        if (performance.now() > until) { over = true; break }
        const hs = [...alive.get(c.head.pred)!]
        if (!hs.length) break
        Zh.send(`(push 1)\n${c.body ? `(assert ${conj(c.body.pred, c.body.args)})` : ''}\n(assert ${c.constraint})\n(assert (not ${conj(c.head.pred, c.head.args)}))`)
        const r = await Zh.check()
        checks++
        if (r === 'unsat') { Zh.send('(pop 1)'); break }
        if (r === 'sat') {
          const vals = await getValues(Zh, hs.map(k => at(c.head!.pred, k, c.head!.args)))
          Zh.send('(pop 1)')
          hs.forEach((k, i) => { if (vals[i] === false) alive.get(c.head!.pred)!.delete(k) })
          changed = true
          continue
        }
        // unknown: each head relation alone, dropped unless proven
        Zh.send('(pop 1)')
        unknowns++
        for (const k of hs) {
          Zh.send(`(push 1)\n${c.body ? `(assert ${conj(c.body.pred, c.body.args)})` : ''}\n(assert ${c.constraint})\n(assert (not ${at(c.head.pred, k, c.head.args)}))`)
          const r1 = await Zh.check(); checks++
          Zh.send('(pop 1)')
          if (r1 !== 'unsat') alive.get(c.head.pred)!.delete(k)
        }
        changed = true
        break
      }
      if (over) break
    }
  }
  const kept = [...alive.values()].reduce((a, s) => a + s.size, 0)
  // safe: every query clause unsatisfiable under the kept relations
  let safe: string = over ? 'deadline' : 'yes'
  if (!over) for (const c of clauses) {
    if (c.head) continue
    Zh.send(`(push 1)\n${c.body ? `(assert ${conj(c.body.pred, c.body.args)})` : ''}\n(assert ${c.constraint})`)
    const r = await Zh.check(); checks++
    Zh.send('(pop 1)')
    if (r !== 'unsat') { safe = r === 'sat' ? 'no' : 'unknown'; break }
  }
  // the kept relations against Spacer's, per predicate
  let impliesSpacer: string = 'n/a'
  if (!over && modelFile && spacerHas.size) {
    const per: string[] = []
    for (const pt of tables) {
      const texts = cand.get(pt.pred)!, ks = [...alive.get(pt.pred)!]
      per.push(await impliesWith(Zh, pt.pred, ks.map(k => texts[k]!), spacerAt(pt.pred)))
    }
    impliesSpacer = per.every(v => v === 'yes') ? 'yes' : per.some(v => v === 'no') ? 'no' : 'unknown'
  }
  // of the relations Houdini dropped (a sample of 100), how many Spacer's invariant implies (true invariants the
  // others don't make inductive) — the rest hold of every sample and maybe of no invariant
  let droppedImplied = 0, droppedChecked = 0
  if (!over && modelFile && spacerHas.size) {
    const dropped: [PredTable, number][] = []
    for (const pt of tables) { const a = alive.get(pt.pred)!; cand.get(pt.pred)!.forEach((_, k) => { if (!a.has(k)) dropped.push([pt, k]) }) }
    const stride = Math.max(1, Math.ceil(dropped.length / 100))
    for (let i = 0; i < dropped.length && performance.now() < until + 20000; i += stride) {
      const [pt, k] = dropped[i]!
      if (!spacerHas.has(pt.pred)) continue
      const r = await impliesWith(Zh, pt.pred, [spacerAt(pt.pred)], cand.get(pt.pred)![k]!)
      droppedChecked++
      if (r === 'yes') droppedImplied++
    }
  }
  zStats.calls += Zh.calls; zStats.ms += Zh.ms
  Zh.kill()
  const res = {ms: Math.round(performance.now() - th), candidates: total, kept, checks, unknowns, safe, impliesSpacer, droppedChecked, droppedImplied, over}
  keptTexts.set(level, new Map([...cand].map(([p, texts]) => [p, [...alive.get(p)!].map(k => texts[k]!)])))
  say({stage: `houdini ${level}`, ...res})
  return res
}
out.houdini = {}
const left = () => Math.max(5000, deadline - (performance.now() - T0))
const keptTexts = new Map<string, Map<string, string[]>>()
for (const [lv, share] of [['L0', 0.3], ['L1', 0.45], ['L2', 1]] as const) (out.houdini as Record<string, unknown>)[lv] = await houdini(lv, performance.now() + left() * share)

// --- the kernel (--kernel): at the first level whose kept relations are safe, those relations handed to gdp-wired's
// prover as laws with no search (compare/chc/prof/given.ts, as Spacer's invariant was), when there are at most 300
if (args.includes('--kernel')) {
  const lv = (['L0', 'L1', 'L2'] as const).find(l => ((out.houdini as Record<string, {safe: string}>)[l]!.safe === 'yes'))
  if (lv) {
    const kt = keptTexts.get(lv)!, n = [...kt.values()].reduce((a, x) => a + x.length, 0)
    const k: Record<string, unknown> = {level: lv, relations: n}
    out.kernel = k
    if (n > 300) k.skipped = 'more than 300 relations'
    else {
      const model = `sat\n(\n${predNames.map(p => `(define-fun ${sym(p)} (${params(p)}) Bool (and true ${(kt.get(p) ?? []).join(' ')}))`).join('\n')}\n)`
      const {writeFileSync} = await import('node:fs'), {spawnSync} = await import('node:child_process')
      writeFileSync('/tmp/table-model.json', JSON.stringify({[file]: model}))
      const t = performance.now(), pr = spawnSync('bun', ['compare/chc/prof/given.ts', file, '/tmp/table-model.json', '--ms', '55000'], {encoding: 'utf8', timeout: 90000})
      k.ms = Math.round(performance.now() - t)
      try { Object.assign(k, JSON.parse((pr.stdout ?? '').trim().split('\n').at(-1)!)) } catch { k.error = (pr.stderr ?? '').slice(-300) || `exit ${pr.status}` }
    }
    say({stage: 'kernel', ...k})
  }
}

Zc.kill()
out.z3 = {calls: Zc.calls + zStats.calls, ms: Math.round(Zc.ms + zStats.ms)}
done()
