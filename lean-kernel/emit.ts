// Kernel proofs as Lean: the machine, its laws and the kernel's trees as Lean.Kern data, each law a theorem by the twin's
// soundness theorems (Kernel.lean, Progress.lean, StepLaw.lean, Steps.lean, History.lean, Sets.lean) with `decide +kernel`. The
// emitter is untrusted: it names columns, orders rows and claims cell equalities; Lean checks every claim. Pure string
// building, so it ships in the package (`gdp-wired/lean`); export-kernel.ts is the repo's script around it.
import type {C, E, Law, Machine, Recurrence} from '../core/machine.ts'
import {atMost, n, not, pointWrite} from '../core/machine.ts'
import {type Lin, type RowSrc, type Step, add, k, scale, sub} from '../core/solver.ts'
import {type Fold, type Goal, type Instances, type Liveness, type Loop, type Path, type StepLaw, type Tree, boundOf, canon, factorsOf, isCell, isMonomial, columnTerm, stateName, termColumn, historyMachine, foldObligations, leafConstraints, loopLiveness, loopMachine, linear, livenessHelpful, livenessParts, livenessRanks, loopObligations, trueC, obligations, progressObligations, stepLawObligations, substC, witnessesOf, withProducts} from '../kernel/kernel.ts'
import {grow, minimal, proveBuilt, proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {refinement, refinementSides} from '../core/compose.ts'
import {leanSurface, leanTerms} from './lean-terms.ts'
import {type Cyclic, descentGoal, mainGoal, premiseGoal} from '../kernel/cyclic.ts'
import {allowNode, closingInsts, cyclicMachine, foldNodes, hasQuantified, kWhens, machineNodes, type NodeSpec, proveCyclic, qflagNodes, routeOf, skMachine, stepLawNodes, tBack} from '../core/cyclic.ts'
import type {Fact} from '../kernel/cyclic.ts'
import {leanLibrary} from './library.ts'
export {leanLibrary}

export type Exported = {name: string, goal: Goal, tree: Tree}
// --- to Lean ------------------------------------------------------------------------------------------------------------

const varsOf = (c: C): string[] => [...JSON.stringify(c).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!)
const parseKey = (text: string): Lin => {
  const lin: Lin = {}
  let depth = 0, start = 0
  for (let i = 0; i <= text.length; i++) {
    const ch = text[i]
    if (ch === '[') depth++
    else if (ch === ']') depth--
    else if ((ch === ',' && depth === 0) || i === text.length) {
      if (i > start) { const part = text.slice(start, i), at = part.lastIndexOf(':'); lin[part.slice(0, at)] = Number(part.slice(at + 1)) }
      start = i + 1
    }
  }
  return lin
}
const cellKey = (cell: string) => parseKey(cell.slice(cell.indexOf('[') + 1, -1))
const cellMap = (cell: string) => cell.slice(0, cell.indexOf('['))
const decide = (lin: Lin, path: Path): boolean | undefined => {
  if (Object.keys(lin).every(key => key === '1')) return (lin['1'] ?? 0) <= 0
  const d = path.get(canon(lin))?.holds
  if (d !== undefined) return d
  const f = path.get(canon(add(k(1), scale(lin, -1))))?.holds
  return f === undefined ? undefined : !f
}
export const int = (v: number) => (v < 0 ? `(${v})` : String(v))
export const list = (xs: string[]) => `[${xs.join(', ')}]`

export function leaves(t: Tree, path: Path, visit: (t: Tree & {leaf: Step[], products?: [number, number][], squares?: Lin[]}, path: Path) => void) {
  if ('leaf' in t) return visit(t, path)
  const id = canon(t.split)
  leaves(t.yes, new Map(path).set(id, {lin: t.split, holds: true}), visit)
  leaves(t.no, new Map(path).set(id, {lin: t.split, holds: false}), visit)
}

export function encode(ex: Exported, tamper = false, dropStep = true, globalVars?: string[], globalMaps?: string[]) {
  const {goal, tree} = ex
  // Columns: every variable of the hypotheses, then every cell any leaf uses (and the cells inside their keys),
  // shallower cells first so a key reads only earlier columns.
  const vars = globalVars ?? [...new Set(goal.hyps.flatMap(varsOf))]
  const cells = new Set<string>(), terms = new Set<string>()
  // Monomials: every one a leaf's rows or products use, or that a product term has under the leaf's path, with the
  // cells among their factors.
  const monos = new Set<string>()
  const addMono = (name: string) => { monos.add(name); for (const f of factorsOf(name)) if (isCell(f)) addCell(f) }
  const addCell = (name: string) => { if (cells.has(name)) return; cells.add(name); for (const key of Object.keys(cellKey(name))) if (isMonomial(key)) addMono(key); else if (key.includes('[')) addCell(key); else if (key.startsWith('⟦')) terms.add(key) }
  const subterms = (c: C): E[] => {
    const out2: E[] = []
    const we = (e: E): void => { out2.push(e); if (e.op === 'if') { wc(e.c); we(e.then); we(e.else) } else if (e.op === 'get') we(e.key); else if ('a' in e) { we(e.a); if ('b' in e) we(e.b) } }
    const wc = (c2: C): void => (c2.op === 'flag' ? undefined : c2.op === 'all' ? wc(c2.c) : c2.op === 'not' ? wc(c2.x) : c2.op === 'and' || c2.op === 'or' ? c2.xs.forEach(wc) : (we(c2.a), we(c2.b)))
    wc(c)
    return out2
  }
  // Every choice in the hypotheses has its column, whether or not a leaf's rows keep it (a column can cancel, T − T,
  // yet Lean's linear form of T still needs it): each distinct subterm once, as a run's states are shared.
  const seenTerms = new WeakSet<object>()
  const choices = (t: E | C): void => {
    if (seenTerms.has(t)) return
    seenTerms.add(t)
    if (t.op === 'sub' || t.op === 'min' || t.op === 'max' || t.op === 'if') terms.add(termColumn(t))
    for (const val of Object.values(t)) if (Array.isArray(val)) val.forEach(x => choices(x as E | C)); else if (typeof val === 'object' && val !== null) choices(val as E | C)
  }
  goal.hyps.forEach(choices)
  leaves(tree, new Map(), (leaf, path) => {
    for (const r of [...withProducts(leafConstraints(goal, path), leaf.products ?? [], leaf.squares), ...(leaf.squares ?? []).map(lin => ({lin}))]) for (const key of Object.keys(r.lin)) {
      if (isMonomial(key)) addMono(key)
      else if (key.includes('[')) addCell(key)
      else if (key.startsWith('⟦')) terms.add(key)
    }
    // Each cell a hypothesis reads under the path, kept or not: two reads of one cell cancel in a row (T − T), yet
    // Lean's linear form of each still needs the cell's column to see the comparison decided.
    for (const h of goal.hyps) for (const e of subterms(h)) {
      if (e.op === 'prod') for (const key of Object.keys(linear(e, path) ?? {})) if (isMonomial(key)) addMono(key)
      if (e.op === 'get') for (const key of Object.keys(linear(e, path) ?? {})) if (isCell(key)) addCell(key)
    }
  })
  const depth = (name: string) => name.split('[').length
  // Term columns (open choices, each standing for its term's value) before the cells, whose keys may read them; a
  // monomial with a cell among its factors after the cells.
  const degree = (a: string, b: string) => factorsOf(a).length - factorsOf(b).length
  const plainMonos = [...monos].filter(m => factorsOf(m).every(f => !isCell(f))).sort(degree), cellMonos = [...monos].filter(m => factorsOf(m).some(isCell)).sort(degree)
  // A cell whose key reads a product of cells (a cyclic proof's map at u + k·Ω, its key k read from a map over time)
  // comes after that product, and the product after its cells: each column placed after the columns it reads.
  const late: string[] = [], placed = new Set<string>()
  const place = (name: string): void => {
    if (placed.has(name)) return
    placed.add(name)
    for (const d of isMonomial(name) ? factorsOf(name) : Object.keys(cellKey(name))) if (cells.has(d) || cellMonos.includes(d)) place(d)
    late.push(name)
  }
  for (const cell of [...cells].sort((a, b) => depth(a) - depth(b))) place(cell)
  for (const mono of cellMonos) place(mono)
  const cols = [...vars, ...plainMonos, ...[...terms].sort((a, b) => Number(a.slice(1, -1)) - Number(b.slice(1, -1))), ...late]
  const col = new Map(cols.map((name, j) => [name, j]))
  const maps = globalMaps ?? [...new Set([...[...cells].map(cellMap), ...goal.hyps.flatMap(h => [...JSON.stringify(h).matchAll(/"op":"get","map":"([^"]+)"/g)].map(m => m[1]!))])]
  const dense = (lin: Lin) => {
    const coefs = new Array(cols.length).fill(0)
    for (const [key, c] of Object.entries(lin)) if (key !== '1') { const j = col.get(key); if (j === undefined) throw new Error(`${ex.name}: no column for ${key}`); coefs[j] = c }
    while (coefs.length && coefs.at(-1) === 0) coefs.pop()
    return coefs as number[]
  }
  // Rows by their nonzero coefficients (Cert.lean's rows hold them so): most of a wide row is zeros.
  const sparse = (coefs: number[]) => list(coefs.flatMap((x, j) => (x === 0 ? [] : [`(${j}, ${int(x)})`])))
  const row = (lin: Lin) => `(sp ${sparse(dense(lin))} ${int(lin['1'] ?? 0)})`
  const {e, c} = leanTerms(vars, maps, ex.name)
  const tab = cols.map(name => (isMonomial(name) ? `.mono ${list(factorsOf(name).map(f => { const j = col.get(f); if (j === undefined) throw new Error(`${ex.name}: factor ${f}`); return j }).sort((a, b) => a - b).map(String))}`
    : name.includes('[') ? `.cell ${maps.indexOf(cellMap(name))} ${row(cellKey(name))}`
    : name.startsWith('⟦') ? `.term (${e(columnTerm(name)!)})`
    : `.var ${vars.indexOf(name)}`))

  let leafNo = 0
  const lean = (t: Tree, path: Path): string => {
    if (!('leaf' in t)) {
      const id = canon(t.split)
      return `.split ${row(t.split)}\n  (${lean(t.yes, new Map(path).set(id, {lin: t.split, holds: true}))})\n  (${lean(t.no, new Map(path).set(id, {lin: t.split, holds: false}))})`
    }
    const base = leafConstraints(goal, path), prods = t.products ?? [], squares = t.squares ?? []
    const rows = withProducts(base, prods, squares).map(r => r.lin), n0 = base.length
    // Only the rows the derivation and the products read, renumbered (the squares follow them, then the products, in
    // order); cuts carry their quotient row (Cert's format).
    const used = [...new Set([...t.leaf.flatMap(s => (s.kind === 'input' && s.index < n0 ? [s.index] : [])), ...prods.flat().filter(i => i < n0)])].sort((a, b) => a - b)
    const at = new Map(used.map((old, j) => [old, j]))
    const idx = (i: number) => (i < n0 ? at.get(i)! : used.length + i - n0)
    const replay: Lin[] = []
    let steps = t.leaf.map(s => {
      if (s.kind === 'input') { replay.push(rows[s.index]!); return `.input ${idx(s.index)}` }
      if (s.kind === 'combine') {
        replay.push(add(scale(replay[s.a]!, s.ma), scale(replay[s.b]!, s.mb)))
        return `.combine ${s.a} ${s.b} ${int(s.ma)} ${int(s.mb)}`
      }
      const from = replay[s.of]!
      const q: Lin = Object.fromEntries(Object.entries(from).filter(([key]) => key !== '1').map(([key, v]) => [key, v / s.g]))
      const cc = Math.ceil((from['1'] ?? 0) / s.g)
      replay.push({...q, 1: cc})
      return `.cut ${s.of} ${int(s.g)} ${sparse(dense(q))} ${int(cc)}`
    })
    if (tamper && dropStep && leafNo++ === 0) steps = steps.slice(0, -1) // the first leaf loses its last step
    // Cell pairs the path proves equal (Lean re-checks each).
    const eqs: string[] = [], pairs: string[] = []
    const cellCols = cols.map((name, j) => ({name, j})).filter(c2 => isCell(c2.name))
    for (const [a, p] of cellCols.entries()) for (const q of cellCols.slice(a + 1)) {
      if (cellMap(p.name) !== cellMap(q.name)) continue
      const d = sub(cellKey(p.name), cellKey(q.name))
      if (decide(d, path) === true && decide(scale(d, -1), path) === true) { eqs.push(`(${p.j}, ${q.j})`); pairs.push([p.name, q.name].sort().join('\n')) }
    }
    // Each row with where Lean finds it (a hint: missed, Lean looks among all of the leaf's rows).
    const hint = (src?: RowSrc): string => {
      if (!src) return '.any'
      if ('atom' in src) return `.atom ${path.size - 1 - src.atom}` // Lean's path has the latest decision first
      if ('fact' in src) return `.fact ${src.fact}`
      const j = 'pair' in src ? pairs.indexOf([...src.pair].sort().join('\n')) : col.get('nat' in src ? src.nat : src.term) ?? -1
      return j < 0 ? '.any' : 'pair' in src ? `.eq ${j}` : 'nat' in src ? `.nat ${j}` : `.term ${j}`
    }
    const at2 = list(used.map(u => `(${row(rows[u]!)}, ${hint(base[u]!.src)})`)), rest = `${list(steps)} ${list(eqs)} ${list(prods.map(([i, j]) => `(${idx(i)}, ${idx(j)})`))}`
    return squares.length ? `.leafSq ${at2} ${list(squares.map(row))} ${rest}` : `.leafAt ${at2} ${rest}`
  }
  return {tab: list(tab), hyps: list(goal.hyps.map(c)), tree: lean(tree, new Map()), cols, c, e}
}

export function goalToLean(ex: Exported, i: number, tamper = false, dropStep = true): string {
  const {tab, hyps, tree, cols} = encode(ex, tamper, dropStep)
  const name = tamper ? `tampered${i}` : `t${i}`
  const body = `def ${name}_goal : Goal := ⟨${tab},\n  ${hyps}⟩
def ${name}_tree : Tree :=
  ${tree}`
  return tamper
    ? `-- TAMPERED: ${ex.name}${dropStep ? ", the first leaf's derivation without its last step" : ''}. Lean computes the check to false.
${body}
example : checkGoal ${name}_goal ${name}_tree = false := by ${checkBy}`
    : `-- ${ex.name}  (${cols.length} columns)
${body}
theorem ${name} : ∀ env maps, ¬ ∀ c ∈ ${name}_goal.hyps, evalC env maps c = true :=
  sound ${name}_goal ${name}_tree (by ${checkBy})`
}

// Whole machines through Kern.machine_sound: Lean builds the goals from the machine; the trees are the kernel's.
export function machineToLean(id: string, m: Machine, laws: Law[], corollary?: string): string {
  if (m.maps && Object.keys(m.maps).length) throw new Error('machine_sound covers scalar state only')
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const flags = Object.entries(m.step.flags ?? {})
  const vars = [...m.params, ...m.inputs, ...Object.keys(m.state), ...flags.map(([f]) => `?${f}`)]
  const gs = obligations(m, laws, r.proof.instances)
  const enc = (g: Goal) => encode({name: `${id}: ${g.name}`, goal: g, tree: r.proof!.trees[g.name]!}, false, true, vars)
  const any0 = enc(gs[0]!)
  const ix = (name: string) => vars.indexOf(name)
  const machine = `⟨${list(m.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(m.state).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(m.step.state ?? {}).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${m.pre ? any0.c(m.pre) : TRUE},
  ${m.assume ? any0.c(m.assume) : TRUE}⟩`
  const proof = laws.map((law, j) => {
    const s = enc(gs[2 * j]!), t = enc(gs[2 * j + 1]!)
    return `(${any0.c(law.holds)},\n  (${s.tab}, ${s.tree}),\n  (${t.tab}, ${t.tree}))`
  })
  if (flags.length) {
    // Flags pass through untouched; Lean inlines them (FMachine.plain) and fmachine_sound covers the machine with flags.
    const fl = (mm: Machine) => list(Object.entries(mm.step.flags ?? {}).map(([f, c2]) => `(${ix(`?${f}`)}, ${any0.c(c2)})`))
    const lit = (mm: Machine) => `⟨⟨${list(mm.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(mm.state).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(mm.step.state ?? {}).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${mm.pre ? any0.c(mm.pre) : TRUE},
  ${mm.assume ? any0.c(mm.assume) : TRUE}⟩,
  ${fl(mm)}⟩`
    return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}, with flags ${flags.map(([f]) => f).join(', ')}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_machine : FMachine := ${lit(m)}
def ${id}_proof : MachineProof := ${list(proof)}
theorem ${id}_laws : ∀ maps ρ, FReach ${id}_machine maps ρ → ∀ l ∈ ${id}_proof.map (·.1), evalC ρ maps l = true :=
  fmachine_sound ${id}_machine ${id}_proof (by ${checkBy})${corollary ? `\n${corollary}` : ''}`
  }
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_machine : Machine := ${machine}
def ${id}_proof : MachineProof := ${list(proof)}
theorem ${id}_laws : ∀ maps ρ, Reach ${id}_machine maps ρ → ∀ l ∈ ${id}_proof.map (·.1), evalC ρ maps l = true :=
  machine_sound ${id}_machine ${id}_proof (by ${checkBy})${corollary ? `\n${corollary}` : ''}`
}
export const TRUE = '.le (.const 0) (.const 0)'
// The tactic each check is closed by: `decide +kernel`, or `native_decide` for toLean's `native`.
let checkBy = 'decide +kernel'
export const grown = (g: Goal) => { const o = grow(g); if (!('tree' in o)) throw new Error(`${g.name}: stuck`); return o.tree }

// Loops through Kern.loop_halts_of: the loop's machine (Live.lean's Loop.machine) with its invariants as laws, and its
// halting as a liveness (kernel.ts's loopMachine, loopLiveness); the trees are the kernel's.
export function loopToLean(id: string, l: Loop, laws: Law[], rank: E | E[], tamper?: {what: string, loop: Loop}): string {
  loopObligations(l, laws, rank)
  return smachineToLean(id, loopMachine(l), laws, {liveness: [loopLiveness(l, rank)], loop: {loop: l, ...(tamper ? {tamper} : {})}})
}

// Folds through Kern.fold_sound: Lean builds the leaf and node goals; the trees are the kernel's.
export function foldToLean(id: string, f: Fold, laws: Law[], extra = ''): string {
  const st = Object.keys(f.leaf)
  const vars = [...f.params, ...f.inputs, ...st, ...st.map(n2 => `l_${n2}`), ...st.map(n2 => `r_${n2}`)]
  const gs = foldObligations(f, laws)
  const enc = (g: Goal, tree = grown(g)) => encode({name: `${id}: ${g.name}`, goal: g, tree}, false, true, vars)
  const any0 = enc(gs[0]!, {leaf: []})
  const ix = (name: string) => vars.indexOf(name)
  const fold = `⟨${list(f.inputs.map(name => String(ix(name))))},
  ${list(st.map(n2 => `(${ix(n2)}, ${ix(`l_${n2}`)}, ${ix(`r_${n2}`)})`))},
  ${list(Object.entries(f.leaf).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(f.node).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${f.pre ? any0.c(f.pre) : TRUE},
  ${f.assume ? any0.c(f.assume) : TRUE}⟩`
  const proof = laws.map((law, j) => {
    const a = enc(gs[2 * j]!), b = enc(gs[2 * j + 1]!)
    return `(${any0.c(law.holds)},\n  (${a.tab}, ${a.tree}),\n  (${b.tab}, ${b.tree}))`
  })
  return `-- ${f.name}: ${laws.map(law => law.name).join('; ')}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_fold : Fold := ${fold}
def ${id}_proof : FoldProof := ${list(proof)}
theorem ${id}_laws : ∀ maps ρ, evalC ρ maps ${id}_fold.pre = true → ∀ t, Allowed ${id}_fold ρ maps t →
    ∀ l ∈ ${id}_proof.map (·.1), evalC (foldT ${id}_fold ρ maps t) maps l = true :=
  fold_sound ${id}_fold ${id}_proof (by ${checkBy})${extra}`
}

// Machines with maps (and flags) through Kern.fmmachine_sound: Lean inlines the flags, then builds the start and step
// goals (read-over-write, ∀-laws at the proof's keys and at a skolem); the trees and the instance keys are the kernel's.
// Progress laws through Kern.progress_sound: Lean builds "the request is allowed" and "the step it causes"; a false
// variant is offered the true one's proof, and Lean computes the check to false.
// Readable corollaries: each law as a plain Lean statement over named variables (ρ the state, μ the maps, each name an
// abbreviation for its column), proven from the machine's theorem by unfolding the law's own definition. The statement
// is what a Lean development cites; the column numbers stay inside the namespace.
// `have`: the line that gives each law as a hypothesis hl (an SEntry's Holds by default; a cyclic proof's, holdsOver).
export function readable(id: string, laws: Law[], vars: string[], maps: string[], reach: {binders: string, hyp: string, call: string, have?: (j: number) => string}): string {
  for (const name of [...vars, ...maps]) if (name === 'ρ' || name === 'μ' || name.includes('«') || name.includes('»')) throw new Error(`${id}: the name ${name} can't be a Lean abbreviation here`)
  const q = (name: string) => `«${name}»`
  const statement = (law: Law): string => {
    const t = (e: E): string => {
      switch (e.op) {
        case 'var': { const j = (law.keys ?? []).indexOf(e.name); return e.name === law.forall ? 'k' : j >= 0 ? `k${j + 2}` : `ρ ${q(e.name)}` }
        case 'const': return String(e.value)
        case 'add': return `(${t(e.a)} + ${t(e.b)})`
        case 'sub': return `(${t(e.a)} - ${t(e.b)})`
        case 'mul': return `(${e.k} * ${t(e.a)})`
        case 'prod': return `(${t(e.a)} * ${t(e.b)})`
        case 'min': case 'max': return `(${e.op} ${t(e.a)} ${t(e.b)})`
        case 'if': return `(if ${p(e.c)} then ${t(e.then)} else ${t(e.else)})`
        case 'get': return `(μ ${q(e.map)} (${t(e.key)}))`
      }
    }
    const p = (c: C): string => {
      switch (c.op) {
        case '<=': return `${t(c.a)} ≤ ${t(c.b)}`
        case '<': return `${t(c.a)} < ${t(c.b)}`
        case '=': return `${t(c.a)} = ${t(c.b)}`
        case 'and': return c.xs.length ? `(${c.xs.map(p).join(' ∧ ')})` : 'True'
        case 'or': return c.xs.length ? `(${c.xs.map(p).join(' ∨ ')})` : 'False'
        case 'not': return `¬(${p(c.x)})`
        case 'flag': throw new Error(`${id}: a law reads no flag`)
        case 'all': throw new Error(`${id}: a law has no quantifier inside`)
      }
    }
    return law.keys?.length ? `∀ k ${law.keys.map((_, j) => `k${j + 2}`).join(' ')} : Nat, ${p(law.holds)}` : law.forall ? `∀ k : Nat, ${p(law.holds)}` : p(law.holds)
  }
  const used = new Set(laws.flatMap(l => [...JSON.stringify(l.holds).matchAll(/"name":"([^"]+)"|"map":"([^"]+)"/g)].map(m => m[1] ?? m[2]!).filter(name => name !== l.forall && !(l.keys ?? []).includes(name))))
  return `namespace ${id}
${[...vars.filter(v => used.has(v)).map(v => `abbrev ${q(v)} : Nat := ${vars.indexOf(v)}`), ...maps.filter(mp => used.has(mp)).map(mp => `abbrev ${q(mp)} : Nat := ${maps.indexOf(mp)}`)].join('\n')}
${laws.map((law, j) => (law.stated ? `-- ${law.name}: as written, with some key; proven (below) with the prover's witness in place\n` : '') + (JSON.stringify(law.holds).includes('"op":"if"') ? `-- ${law.name}: its terms read an if, so no plain statement here (${id}_laws holds it)` : `/-- ${law.name.replace(/-\//g, '- /')} -/
theorem law${j} ${reach.binders} (h : ${reach.hyp}) : ${statement(law)} := by
  ${law.keys?.length ? `${reach.have ? reach.have(j) : `have hl : ${id}_e${j}.Holds ρ μ := ${reach.call} ${id}_e${j} (by simp [${id}_proof])`}
  exact fun k ${law.keys.map((_, i) => `k${i + 2}`).join(' ')} => (evalC_iff (upd (${law.keys.reduce((acc, key, i) => `upd (${acc}) ${vars.indexOf(key)} k${i + 2}`, 'ρ')}) ${vars.indexOf(law.forall!)} k) μ ${id}_l${j}.holds).mp (hl ${law.keys.map((_, i) => `k${i + 2}`).join(' ')} k)` : `${reach.have ? reach.have(j) : `have hl : ${id}_l${j}.Holds ρ μ := ${reach.call} ${id}_e${j} (by simp [${id}_proof])`}
  ${law.forall ? `exact fun k => (evalC_iff (upd ρ ${vars.indexOf(law.forall)} k) μ ${id}_l${j}.holds).mp (hl k)` : `exact (evalC_iff ρ μ ${id}_l${j}.holds).mp hl`}`}`)).join('\n')}
end ${id}`
}

export type ProgressCase = {id: string, name: string, when: C, then: C, request: Record<string, E>, instances: Instances, tamper?: {what: string, when: C}}
// Live.lean's reqC: each input named by its term, two parts per and.
const reqTS = (req: [string, E][]): C => (req.length ? {op: 'and', xs: [{op: '=', a: {op: 'var', name: req[0]![0]}, b: req[0]![1]}, reqTS(req.slice(1))]} : {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}})
// Witnesses for a helpful request's free inputs, for its allowed goal: all free first, then each free input fixed to 0, a
// state variable or a param (a history's query, say, which its relations bound), the first combination that proves.
function withWitness<R>(m: Machine, request: Record<string, E>, attempt: (wit: [string, E][]) => R | undefined): {wit: [string, E][], out: R} | undefined {
  const free = m.inputs.filter(i => !(i in request))
  const cands: (E | undefined)[] = [undefined, {op: 'const', value: 0}, ...Object.keys(m.state).map(v => ({op: 'var', name: v}) as E), ...m.params.map(v => ({op: 'var', name: v}) as E)]
  const combos: [string, E][][] = [[]]
  if (free.length <= 2) {
    const go = (i: number, acc: [string, E][]) => { if (i === free.length) { if (acc.length) combos.push(acc); return } for (const c of cands) go(i + 1, c ? [...acc, [free[i]!, c]] : acc) }
    go(0, [])
  }
  for (const wit of combos) { const out = attempt(wit); if (out !== undefined) return {wit, out} }
  return undefined
}

// A liveness as Live.lean's record: from, to, the rank's parts, each helpful request with its region, the primes.
function liveLit(l: Liveness, t: {e: (x: E) => string, c: (x: C) => string}, ix: (name: string) => number, primes: string, primeMaps: string): string {
  return `⟨${t.c(l.from)}, ${t.c(l.to)}, ${list(livenessRanks(l).map(t.e))},
  ${list(livenessHelpful(l).map(h => `(${t.c(h.when)}, ${list(Object.entries(h.request).map(([inp, x]) => `(${ix(inp)}, ${t.e(x)})`))})`))},
  ${primes},
  ${primeMaps}⟩`
}
// The base twin's export (Progress.lean, StepLaw.lean, Steps.lean): laws, step laws, k-step laws and progress over a
// machine with maps and flags, for the demos in export-kernel.ts. Everything built on top (liveness, ghosts, refinement)
// goes through the sets twin, smachineToLean.
export function mmachineToLean(id: string, m: Machine, laws: Law[], opts: {corollary?: string, tamper?: {what: string, machine: Machine}, progress?: ProgressCase[], free?: string[], stepLaws?: StepLaw[]} = {}): string {
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const keysOf = [...new Set(laws.flatMap(l => (l.forall ? [l.forall] : [])))]
  const flagNames = Object.keys(m.step.flags ?? {})
  const primed = !!(opts.progress || opts.stepLaws?.length)
  const primes = primed ? Object.keys(m.state).map(s2 => `${s2}'`) : []
  // A k-step law reads the j-th request's inputs (j >= 2) by input@j.
  const later = [...new Set((opts.stepLaws ?? []).flatMap(sl => Array.from({length: (sl.steps ?? 1) - 1}, (_, j) => m.inputs.map(i => `${i}@${j + 2}`)).flat()))]
  const vars = [...m.params, ...m.inputs, ...Object.keys(m.state), ...keysOf, ...keysOf.map(k2 => `${k2}#`), '#', ...flagNames.map(f => `?${f}`), ...(opts.free ?? []), ...(opts.stepLaws ?? []).flatMap(sl => (sl.forall ? [sl.forall] : [])), ...primes, ...later]
  const baseMaps = [...new Set([...Object.keys(m.maps ?? {}), ...Object.keys(m.step.maps ?? {}), ...[...JSON.stringify(laws).matchAll(/"op":"get","map":"([^"]+)"/g)].map(x2 => x2[1]!)])]
  const mapNames = [...baseMaps, ...(primed ? baseMaps.map(mp => `${mp}'`) : [])]
  const gs = obligations(m, laws, r.proof.instances)
  const enc = (g: Goal, tree = r.proof!.trees[g.name]!) => encode({name: `${id}: ${g.name}`, goal: g, tree}, false, true, vars, mapNames)
  const any0 = enc(gs[0]!, {leaf: []})
  const ix = (name: string) => vars.indexOf(name)
  const lit = (mm: Machine) => `⟨⟨${list(mm.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(mm.state).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(mm.maps ?? {}).map(([name, c2]) => `(${mapNames.indexOf(name)}, ${c2})`))},
  ${list(Object.entries(mm.step.state ?? {}).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(mm.step.maps ?? {}).map(([name, w]) => { const pw = pointWrite(w, 'Lean (for now)'); return `(${mapNames.indexOf(name)}, ${any0.e(pw.key)}, ${any0.e(pw.value)})` }))},
  ${mm.pre ? any0.c(mm.pre) : TRUE},
  ${mm.assume ? any0.c(mm.assume) : TRUE}⟩,
  ${list(Object.entries(mm.step.flags ?? {}).map(([f, c2]) => `(${ix(`?${f}`)}, ${any0.c(c2)})`))}⟩`
  const entries = laws.map((law, j) => {
    const a = enc(gs[2 * j]!), b = enc(gs[2 * j + 1]!)
    const insts = Object.entries(r.proof!.instances[law.name] ?? {}).flatMap(([lname, keys]) => keys.map(key => `(${laws.findIndex(l => l.name === lname)}, ${any0.e(key)})`))
    return `def ${id}_l${j} : MLaw := ⟨${any0.c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩\ndef ${id}_e${j} : MEntry := ⟨${id}_l${j}, ${ix(law.forall ? `${law.forall}#` : '#')}, ${list(insts)},\n  (${a.tab}, ${a.tree}),\n  (${b.tab}, ${b.tree})⟩`
  })
  const progress = (opts.progress ?? []).map(pc => {
    const gs2 = progressObligations(m, laws, pc.instances, {name: pc.name, when: pc.when, then: pc.then, request: pc.request})
    const causes = gs2.at(-1)!
    // Lean always has the allowed goal; without an assumption it is refuted by its own last hypothesis.
    const allowed = m.assume ? gs2[0]! : {name: `${pc.name}: the request is allowed`, hyps: [...causes.hyps.slice(0, -1), not(atMost(n(0), n(0)))]}
    const ea = enc(allowed, grown(allowed)), ec = enc(causes, grown(causes))
    const insts = laws.flatMap((l, j) => (l.forall ? (pc.instances[l.name] ?? []).map(key => `(${j}, ${any0.e(key)})`) : []))
    const record = (when: C) => `⟨${any0.c(when)},
  ${any0.c(pc.then)},
  ${list(Object.entries(pc.request).map(([inp, e]) => `(${ix(inp)}, ${any0.e(e)})`))},
  ${list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`))},
  ${list(baseMaps.map(mp => `(${mapNames.indexOf(mp)}, ${mapNames.indexOf(`${mp}'`)})`))},
  ${list(insts)},
  (${ea.tab}, ${ea.tree}),
  (${ec.tab}, ${ec.tree})⟩`
    return `-- Progress: ${pc.name}
def ${pc.id} : Progress := ${record(pc.when)}
theorem ${pc.id}_holds : ProgressHolds ${id}_machine ${pc.id} :=
  progress_sound ${id}_machine ${id}_proof ${pc.id} ${id}_check (by ${checkBy})${pc.tamper ? `
-- TAMPERED: ${pc.tamper.what}: the proof above offered for it. Lean computes the check to false.
def ${pc.id}_tampered : Progress := ${record(pc.tamper.when)}
example : checkProgress ${id}_machine ${id}_proof ${pc.id}_tampered = false := by ${checkBy}` : ''}`
  })
  // Step laws through Kern.steplaw_sound: `when` and `then` sent with the flags inlined (as kernel.ts's goal has them);
  // a law over several steps goes through smachineToLean.
  const sp = opts.stepLaws?.length ? proveStepLaws(m, laws, opts.stepLaws) : undefined
  if (opts.stepLaws?.length && (!sp?.proven || !sp.proof)) throw new Error(`${id}: step laws not proven`)
  const inlineFlags = (c: C): C => substC(c, {vars: {}, maps: {}, flags: m.step.flags ?? {}})
  const stepRecords = (opts.stepLaws ?? []).map((sl, j) => {
    const goal = stepLawObligations(m, laws, sp!.proof!.instances, sl)[0]!
    const pr = enc(goal, sp!.proof!.trees[goal.name]!)
    const insts = laws.flatMap((l, li) => (l.forall ? (sp!.proof!.instances[l.name] ?? []).map(key => `(${li}, ${any0.e(key)})`) : []))
    const primes = list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`)), primeMaps = list(baseMaps.map(mp => `(${mapNames.indexOf(mp)}, ${mapNames.indexOf(`${mp}'`)})`))
    const k = sl.steps ?? 1
    const when = Array.isArray(sl.when) ? sl.when[0] : sl.when
    if (k !== 1) throw new Error(`${id}: step law ${sl.name}: a law over several steps goes through smachineToLean (Sets.lean's skstep_sound)`)
    return `-- Step law: ${sl.name}
def ${id}_step${j} : StepLaw := ⟨${when ? any0.c(inlineFlags(when)) : TRUE},
  ${any0.c(inlineFlags(sl.then))},
  ${primes},
  ${primeMaps},
  ${list(insts)},
  (${pr.tab}, ${pr.tree})⟩
theorem ${id}_step${j}_holds : StepLawHolds ${id}_machine ${id}_step${j} :=
  steplaw_sound ${id}_machine ${id}_proof ${id}_step${j} ${id}_check (by ${checkBy})`
  })
  const machineDef = `def ${id}_machine : FMMachine := ${lit(m)}`
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}${flagNames.length ? `, with flags ${flagNames.join(', ')}` : ''}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${mapNames.map((v2, j) => `${j} ${v2}`).join(', ')})
${machineDef}
${entries.join('\n')}
def ${id}_proof : List MEntry := ${list(laws.map((_, j) => `${id}_e${j}`))}
theorem ${id}_check : checkFMMachine ${id}_machine ${id}_proof = true := by ${checkBy}
theorem ${id}_laws : ∀ ρ M, FMReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.law.Holds ρ M :=
  fmmachine_sound ${id}_machine ${id}_proof ${id}_check
${readable(id, laws, vars, mapNames, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: `FMReach ${id}_machine ρ μ`, call: `${id}_laws ρ μ h`})}${opts.corollary ? `\n${opts.corollary}` : ''}${opts.tamper ? `
-- TAMPERED: ${opts.tamper.what}. Lean computes the check to false.
def ${id}_tampered : FMMachine := ${lit(opts.tamper.machine)}
example : checkFMMachine ${id}_tampered ${id}_proof = false := by ${checkBy}` : ''}${progress.length ? `\n\n${progress.join('\n\n')}` : ''}${stepRecords.length ? `\n\n${stepRecords.join('\n\n')}` : ''}`
}

// Machines with sets through Kern.smachine_sound and Kern.skstep_sound (Sets.lean): maps a request carries, flags that
// hold at every key (each its 0/1 variable ?f, closed at the proof's keys and at a witness w?f) and writes at every
// key. Lean builds every goal from the machine; the trees, the instance keys and the flag instances are the kernel's.
// Step laws, one step or k, go through the k-step rule, the j-th request read by input@j, ?f@j, w?f@j and Map@j.
const flagsOfM = (m: Machine): Record<string, C> => {
  const out: Record<string, C> = {}
  for (const [f, c] of Object.entries(m.step.flags ?? {})) out[f] = c.op === 'all' ? {op: '=', a: {op: 'var', name: `?${f}`}, b: {op: 'const', value: 1}} : substC(c, {vars: {}, maps: {}, flags: out})
  return out
}
// Sets, or functions with facts: both go through Sets.lean.
export const hasSets = (m: Machine) => !!m.inputMaps?.length || Object.values(m.step.flags ?? {}).some(c => c.op === 'all') || Object.values(m.step.maps ?? {}).some(w => 'each' in w)
  || !!Object.keys(m.fns ?? {}).length || !!m.facts?.length
const boundKeys = (m: Machine) => [...Object.values(m.step.flags ?? {}).flatMap(c => (c.op === 'all' ? boundOf(c) : [])), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : []))]
// A machine with a history goes as its plain machine (kernel.ts's historyMachine: sums as state, queries as inputs,
// the relations assumed), built in Lean from the machine and its history (History.lean's HMachine.plain), so every claim
// below is about it; with the relations' record goals, its laws hold over histories too (hmachine_sound).
// `historyTampers`: the history with other relations, each refused.
// A machine as Sets.lean's SMachine literal: its variables and maps numbered by `ix` and `mx`, its terms by `t`.
export function machineLit(mm: Machine, t: {e: (x: E) => string, c: (x: C) => string}, ix: (name: string) => number, mx: (name: string) => number): string {
  const {e, c} = t
  const fl = flagsOfM(mm), fs = Object.entries(mm.step.flags ?? {}), ws = Object.entries(mm.step.maps ?? {})
  return `⟨⟨⟨${list(mm.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(mm.state).map(([name, e2]) => `(${ix(name)}, ${e(e2)})`))},
  ${list(Object.entries(mm.maps ?? {}).map(([name, c2]) => `(${mx(name)}, ${c2})`))},
  ${list(Object.entries(mm.step.state ?? {}).map(([name, e2]) => `(${ix(name)}, ${e(e2)})`))},
  ${list(ws.flatMap(([name, w]) => ('each' in w ? [] : [`(${mx(name)}, ${e(w.key)}, ${e(w.value)})`])))},
  ${mm.pre ? c(mm.pre) : TRUE},
  ${mm.assume ? c(mm.assume) : TRUE}⟩,
  ${list(fs.flatMap(([f, c2]) => (c2.op === 'all' ? [] : [`(${ix(`?${f}`)}, ${c(fl[f]!)})`])))}⟩,
  ${list((mm.inputMaps ?? []).map(mp => String(mx(mp))))},
  ${list(ws.flatMap(([name, w]) => ('each' in w ? [`(${mx(name)}, ${ix(w.each)}, ${e(w.value)})`] : [])))},
  ${list(fs.flatMap(([f, c2]) => (c2.op === 'all' ? [`(${ix(`?${f}`)}, ${list(boundOf(c2).map(key => String(ix(key))))}, ${c(c2.c)})`] : [])))},
  ${list(fs.flatMap(([f, c2]) => (c2.op === 'all' ? [`(${ix(`?${f}`)}, ${list(witnessesOf(f, c2).map(w => String(ix(w))))})`] : [])))},
  ${list((mm.facts ?? []).filter(l => !l.keys?.length).map(l => `⟨${c(l.holds)}, ${l.forall ? `some ${ix(l.forall)}` : 'none'}⟩`))},
  ${list((mm.facts ?? []).filter(l => l.keys?.length).map(l => `(⟨${c(l.holds)}, some ${ix(l.forall!)}⟩, ${list(l.keys!.map(k2 => String(ix(k2))))})`))}⟩`
}

// A request's extended names: its inputs, each flag that holds at every key and its witnesses (Sets.lean's extVars, in
// the order the usual export lists a later step's names in).
const extOf = (m: Machine): string[] => [...m.inputs, ...Object.entries(m.step.flags ?? {}).flatMap(([f, c]) => (c.op === 'all' ? [`?${f}`, ...witnessesOf(f, c)] : []))]

// The names a machine's export numbers first, before those only its goals read: the machine's own (params, inputs, state,
// flags, the keys of its laws and facts, the keys its writes and quantified flags bind) and its claims' (each step law's
// key, the state after the step, each later request's names, the state between steps, a history's record). The usual
// export and the cyclic one (cycMachineToLean) number them alike, so that a machine, a law's statement and a step law are
// the same Lean text in both.
function machineNames(m: Machine, laws: Law[], allSteps: StepLaw[], stepLaws: StepLaw[], opts: {tamper?: {machine: Machine}, free?: string[], record?: string[]}): {vars: string[], maps: string[]} {
  const flags = Object.entries(m.step.flags ?? {}), quantified = flags.filter(([, c]) => c.op === 'all').map(([f]) => f)
  const qwits = (f: string) => witnessesOf(f, m.step.flags![f] as Extract<C, {op: 'all'}>)
  const carried = m.inputMaps ?? [], keysOf = [...new Set([...laws, ...(m.facts ?? [])].flatMap(l => [l.forall, ...(l.keys ?? [])].filter((k): k is string => !!k)))]
  const k = Math.max(1, ...allSteps.map(sl => sl.steps ?? 1))
  const ext = [...m.inputs, ...quantified.flatMap(f => [`?${f}`, ...qwits(f)])]
  const later = Array.from({length: k - 1}, (_, j) => ext.map(v => `${v}@${j + 2}`)).flat()
  const laterMaps = Array.from({length: k - 1}, (_, j) => carried.map(mp => `${mp}@${j + 2}`)).flat()
  const primes = allSteps.length ? Object.keys(m.state).map(s2 => `${s2}'`) : []
  const vars = [...new Set([...m.params, ...m.inputs, ...Object.keys(m.state), ...keysOf, ...keysOf.map(k2 => `${k2}#`), '#', ...flags.map(([f]) => `?${f}`),
    ...quantified.flatMap(qwits), ...boundKeys(m), ...(opts.tamper ? boundKeys(opts.tamper.machine) : []), ...stepLaws.flatMap(sl => (sl.forall ? [sl.forall] : [])), ...(opts.free ?? []),
    ...primes, ...later, ...Array.from({length: k - 1}, (_, j) => Object.keys(m.state).map(n2 => stateName(n2, j + 1))).flat(), ...(opts.record ?? []).map(f => `r.${f}`)])]
  const baseMaps = [...new Set([...Object.keys(m.maps ?? {}), ...Object.keys(m.step.maps ?? {}), ...Object.keys(m.fns ?? {})])]
  const maps = [...new Set([...baseMaps, ...carried, ...(allSteps.length ? Object.keys(m.maps ?? {}).map(mp => `${mp}'`) : []), ...laterMaps])]
  return {vars, maps}
}

export function smachineToLean(id: string, given: Machine, laws: Law[], opts: {stepLaws?: StepLaw[], liveness?: Liveness[], tamper?: {what: string, machine: Machine}, simp?: string[], free?: string[],
    ghosts?: string[], after?: (ix: (name: string) => number) => string, historyTampers?: {what: string, relations: {when: C, holds: C}[], withRecordTrees: boolean}[],
    refined?: {impl: Machine, spec: Machine, wit: Record<string, E>, stutter: C, specPre: number}, loop?: {loop: Loop, tamper?: {what: string, loop: Loop}}, noFacts?: boolean} = {}): string {
  const hm = given.history ? {...given, history: {...given.history, prune: undefined}} : undefined
  const hplain = hm ? historyMachine(hm) : undefined, stepLaws = opts.stepLaws ?? [], rf = opts.refined, gv = opts.ghosts ?? []
  const m = hplain ? hplain.machine : given
  // Every claim about the machine past its laws goes through one pipeline: a claim brings the step laws it needs and
  // the requests it needs proven allowed in a region, the proofs are found and encoded once for all claims, and each
  // claim states its theorem from them (the Lean meaning of each is a theorem in Live.lean, Refine.lean or Ghost.lean).
  type Allow = {when: C, request: Record<string, E>}
  type Helpers = {step: (sl: StepLaw) => {pr: {tab: string, tree: string, hyps: string}, inst: Instances}, sproof: (sl: StepLaw) => string, allow: (a: Allow) => string | undefined}
  type Claim = {steps: StepLaw[], allows: Allow[], render: (h: Helpers) => string}
  const claims: Claim[] = []
  const claimSteps = () => claims.flatMap(cl => cl.steps)
  // The machine's own step laws, one step or k (Sets.lean's skstep_sound).
  if (!rf) stepLaws.forEach((sl, j) => claims.push({steps: [sl], allows: [], render: h => {
    const {pr, inst} = h.step(sl), kk = sl.steps ?? 1
    const whens = sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when]
    const ren = Array.from({length: kk}, (_, s2) => (s2 === 0 ? '[]' : list(ext.map(v => `(${ix(v)}, ${ix(`${v}@${s2 + 1}`)})`))))
    const mren = Array.from({length: kk}, (_, s2) => (s2 === 0 ? '[]' : list(carried.map(mp => `(${mx(mp)}, ${mx(`${mp}@${s2 + 1}`)})`))))
    return `-- Step law${kk > 1 ? ` over ${kk} steps` : ''}: ${sl.name}
def ${id}_step${j} : SKStep := ⟨⟨${list(Array.from({length: kk}, (_, s2) => (whens[s2] ? c(inline(whens[s2]!)) : TRUE)))},
  ${c(inline(sl.then))},
  ${list(ren)},
  ${list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`))},
  ${list(Object.keys(m.maps ?? {}).map(mp => `(${mx(mp)}, ${mx(`${mp}'`)})`))},
  ${list(insts(inst))},
  (${pr.tab}, ${pr.tree})⟩,
  ${list(mren)},
  ${list(qinsts(inst))},
  ${list(finsts(inst))},
  ${list(pinsts(inst))},
  ${list(pfinsts(inst))},
  ${pr.hyps},
  ${list(Array.from({length: kk - 1}, (_, s2) => list(Object.keys(m.state).map(n2 => `(${ix(n2)}, ${ix(stateName(n2, s2 + 1))})`))))}⟩
theorem ${id}_step${j}_holds : SKStepHolds ${id}_machine ${id}_step${j} :=
  skstep_sound ${id}_machine ${id}_proof ${id}_step${j} ${id}_check (by ${checkBy})`
  }}))
  // A refinement (Refine.lean's SRefined): its step law, that the spec stutters or allows the request it is sent; srefines
  // says what the whole means.
  if (rf) claims.push({steps: [stepLaws[0]!], allows: [], render: h => {
    const primesL = list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`)), primeMapsL = list(Object.keys(m.maps ?? {}).map(mp => `(${mx(mp)}, ${mx(`${mp}'`)})`))
    const proofL = h.sproof(stepLaws[0]!)
    return `theorem ${id}_allowed : checkSKStep ${id}_machine ${id}_proof (srStep ${id}_refined ${primesL} ${primeMapsL} ${proofL}) = true := by ${checkBy}
theorem ${id}_refines : ∀ ρ M, SReach ${id}_refined.impl ρ M → ∃ ρc Mc σ Ms, SReach ${id}_refined.full ρc Mc ∧ Agree ${id}_refined.SV ρc ρ
    ∧ (∀ mp, mp ∉ ${id}_refined.SM → Mc mp = M mp) ∧ SReach ${id}_refined.spec σ Ms ∧ Agree ${id}_refined.X σ ρc
    ∧ (∀ mp, mp ∉ ${id}_refined.IM → mp ∉ ${id}_refined.spec.carried → Ms mp = Mc mp) ∧ ∀ e ∈ ${id}_proof, e.Holds ρc Mc :=
  srefines ${id}_refined (by ${checkBy}) (by ${checkBy}) ${id}_proof ${id}_check ${rf.specPre} ⟨rfl, rfl⟩ ${primesL} ${primeMapsL} ${proofL} ${id}_allowed (by ${checkBy}) (by ${checkBy}) (by ${checkBy})`
  }})
  // Liveness (Live.lean's sleads_sound): its step laws (stay, cover, one per helpful request), and where each helpful
  // request is proven allowed in its region, the same under weak fairness (sleads_wf_sound).
  for (const [j, l] of (opts.liveness ?? []).entries()) {
    const {stay, cover, helps} = livenessParts(m, l), helpful = livenessHelpful(l), lid = `${id}_live${j}`
    const allows: Allow[] = helps.map((hs, i) => ({when: hs.when as C, request: helpful[i]!.request}))
    claims.push({steps: [stay, cover, ...helps], allows, render: h => {
      const al = allows.map(h.allow)
      const wf = al.every(a => a !== undefined) ? `
def ${lid}_ap : List (List (Nat × E) × SProof × List E) := ${list(al as string[])}
theorem ${lid}_allows : sliveAllowsOk ${id}_machine ${id}_proof ${lid} ${lid}_ap = true := by ${checkBy}
/-- ${l.name}, under weak fairness: along every run that takes each helpful request whenever, from some point on, it
stays allowed, \`from\` is followed by \`to\`. -/
theorem ${lid}_holds_wf (run : SRun ${id}_machine)
    (fair : ∀ h ∈ ${lid}.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView ${id}_machine (run.st m).1 (run.st m).2 ι κ).1 (sView ${id}_machine (run.st m).1 (run.st m).2 ι κ).2 ${id}_machine.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 ${lid}.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 ${lid}.to = true :=
  sleads_wf_sound ${id}_machine ${id}_proof ${lid} _ _ _ _ ${id}_check ${lid}_ok ${lid}_stay ${lid}_cover ${lid}_helps ${lid}_allows run fair` : ''
      return `-- Liveness: ${l.name}
def ${lid} : Live := ${liveLit(l, {e, c}, ix, list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`)), list(Object.keys(m.maps ?? {}).map(mp => `(${mx(mp)}, ${mx(`${mp}'`)})`)))}
def ${lid}_sp : SProof := ${h.sproof(stay)}
def ${lid}_cp : SProof := ${h.sproof(cover)}
def ${lid}_hp : List SProof := ${list(helps.map(h.sproof))}
theorem ${lid}_ok : sliveOk ${id}_machine ${lid} = true := by ${checkBy}
theorem ${lid}_stay : checkSKStep ${id}_machine ${id}_proof (sliveStep ${lid} ${lid}.pend (liveStayC ${lid}) ${lid}_sp) = true := by ${checkBy}
theorem ${lid}_cover : checkSKStep ${id}_machine ${id}_proof (sliveStep ${lid} ${lid}.pend (liveCoverC ${lid}) ${lid}_cp) = true := by ${checkBy}
theorem ${lid}_helps : sliveHelpsOk ${id}_machine ${id}_proof ${lid} ${lid}_hp = true := by ${checkBy}
/-- ${l.name}: along every run that takes each helpful request infinitely often, \`from\` is followed by \`to\`. -/
theorem ${lid}_holds (run : SRun ${id}_machine)
    (fair : ∀ h ∈ ${lid}.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 ${lid}.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 ${lid}.to = true :=
  sleads_sound ${id}_machine ${id}_proof ${lid} _ _ _ ${id}_check ${lid}_ok ${lid}_stay ${lid}_cover ${lid}_helps run fair${wf}`
    }})
  }
  // A loop (Live.lean's loop_halts_of): its machine is the loop's, and its liveness says the loop halts.
  const lp0 = opts.loop
  if (lp0) claims.push({steps: [], allows: [], render: () => `/-- ${lp0.loop.name} halts: for params meeting its precondition, no run of turns goes on forever. -/
theorem ${id}_halts : ∀ maps ρ0, evalC ρ0 maps ${id}_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS ${id}_loop.init ρ0 maps ∧ ∀ n, Turn ${id}_loop maps (f n) (f (n + 1)) :=
  loop_halts_of ${id}_loop ${id}_live0 rfl rfl (by intro h hh; simp only [${id}_live0, List.mem_singleton] at hh; subst hh; rfl) (by ${checkBy}) ${id}_live0_holds${lp0.tamper ? `
-- TAMPERED: ${lp0.tamper.what}. Lean computes the checks to false.
def ${id}_tampered : SMachine := Loop.machine ${loopLit(lp0.tamper.loop)}
example : (checkSMachine ${id}_tampered ${id}_proof && sliveOk ${id}_tampered ${id}_live0
    && checkSKStep ${id}_tampered ${id}_proof (sliveStep ${id}_live0 ${id}_live0.pend (liveStayC ${id}_live0) ${id}_live0_sp)
    && checkSKStep ${id}_tampered ${id}_proof (sliveStep ${id}_live0 ${id}_live0.pend (liveCoverC ${id}_live0) ${id}_live0_cp)
    && sliveHelpsOk ${id}_tampered ${id}_proof ${id}_live0 ${id}_live0_hp) = false := by ${checkBy}` : ''}`})
  // Ghosts (Ghost.lean's sghost_laws): the laws that read no ghost hold of the machine without its ghosts.
  if (gv.length) claims.push({steps: [], allows: [], render: () => `-- The laws that read no ghost hold of the machine without its ghosts.
theorem ${id}_orig_laws : ∀ ρ M, SReach ${id}_ghosted.orig ρ M → ∀ e ∈ ${id}_proof, avoids ${id}_ghosted.vars e.law.holds = true → e.Holds ρ M :=
  sghost_laws ${id}_ghosted ${id}_ghostOk ${id}_proof ${id}_check`})
  const allSteps = claimSteps()
  const r = proveStepLaws(m, laws, allSteps)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const lp = r.proof.laws, si = r.proof.instances
  const flags = Object.entries(m.step.flags ?? {}), quantified = flags.filter(([, c]) => c.op === 'all').map(([f]) => f)
  const qwits = (f: string) => witnessesOf(f, m.step.flags![f] as Extract<C, {op: 'all'}>)
  const carried = m.inputMaps ?? [], facts = m.facts ?? []
  const ext = [...m.inputs, ...quantified.flatMap(f => [`?${f}`, ...qwits(f)])]
  const instOf = (sl: StepLaw) => r.proof!.perStep?.[sl.name] ?? si
  const goalsL = obligations(m, laws, lp.instances), goalsS = allSteps.map(sl => stepLawObligations(m, laws, instOf(sl), sl)[0]!)
  // Weak fairness over sets: each helpful request allowed in its region carrying empty sets (Live.lean's sAllowGoal,
  // built here as Lean builds it: facts, laws, `when`, each quantified flag closed, the carried maps 0 at the keys read,
  // and the assumption's failing, its plain flags inlined as `if c then 1 else 0 = 1`).
  const zero1 = (k: number): E => ({op: 'const', value: k}), eqC = (a: E, b: E): C => ({op: '=', a, b})
  const fl0 = flagsOfM(m), allFlags = Object.entries(m.step.flags ?? {})
  const sInline = (c2: C): C => substC(c2, {vars: {}, maps: {}, flags: Object.fromEntries(allFlags.map(([f, fc]) =>
    [f, fc.op === 'all' ? eqC({op: 'var', name: `?${f}`}, zero1(1)) : eqC({op: 'if', c: fl0[f]!, then: zero1(1), else: zero1(0)}, zero1(1))]))})
  const sub1 = (c2: C, vars: Record<string, E>): C => substC(c2, {vars, maps: {}, flags: {}})
  const carriedKeys = (cs: C[]): E[] => {
    const out = new Map<string, E>()
    const inE = (x2: E): void => { if (x2.op === 'get') { if ((m.inputMaps ?? []).includes(x2.map)) out.set(JSON.stringify(x2.key), x2.key); inE(x2.key) } else if (x2.op === 'if') (inC(x2.c), inE(x2.then), inE(x2.else)); else if (x2.op === 'mul') inE(x2.a); else if ('a' in x2) (inE(x2.a), inE(x2.b)) }
    const inC = (c2: C): void => (c2.op === 'flag' || c2.op === 'all' ? undefined : c2.op === 'not' ? inC(c2.x) : c2.op === 'and' || c2.op === 'or' ? c2.xs.forEach(inC) : (inE(c2.a), inE(c2.b)))
    cs.forEach(inC)
    return [...out.values()]
  }
  const allowGoalS = (inst: Instances, w: C): Goal & {zkeys: E[]} => {
    const factsF = m.facts ?? []
    const base: C[] = [m.pre ?? trueC,
      ...factsF.filter(f => !f.forall).map(f => f.holds),
      ...Object.entries(inst).flatMap(([name, keys]) => { const f = factsF.find(f2 => f2.name === name); return f?.forall && !f.keys?.length ? keys.map(key => sub1(f.holds, {[f.forall!]: key})) : [] }),
      // A fact about several keys at each tuple (kept flattened), as Lean reads it: the further keys, then the first.
      ...Object.entries(inst).flatMap(([name, keys]) => {
        const f = factsF.find(f2 => f2.name === name)
        if (!f?.keys?.length) return []
        const k = f.keys.length + 1
        return Array.from({length: Math.floor(keys.length / k)}, (_, t) => sub1(sub1(f.holds, Object.fromEntries(f.keys!.map((kn, i) => [kn, keys[t * k + 1 + i]!]))), {[f.forall!]: keys[t * k]!}))
      }),
      ...laws.filter(lw => !lw.forall).map(lw => lw.holds),
      ...Object.entries(inst).flatMap(([name, keys]) => { const lw = laws.find(l2 => l2.name === name); return lw?.forall && !lw.keys?.length ? keys.map(key => sub1(lw.holds, {[lw.forall!]: key})) : [] }),
      ...Object.entries(inst).flatMap(([name, keys]) => {
        const lw = laws.find(l2 => l2.name === name)
        if (!lw?.keys?.length) return []
        const k = lw.keys.length + 1
        return Array.from({length: Math.floor(keys.length / k)}, (_, t) => sub1(sub1(lw.holds, Object.fromEntries(lw.keys!.map((kn, i) => [kn, keys[t * k + 1 + i]!]))), {[lw.forall!]: keys[t * k]!}))
      }),
      w,
      ...allFlags.flatMap(([f, fc]): C[] => {
        if (fc.op !== 'all') return []
        const names = boundOf(fc), n = names.length, at = (ts: E[]) => sub1(fc.c, Object.fromEntries(names.map((key, i) => [key, ts[i]!]))), qi = inst[`?${f}`] ?? []
        return [{op: '<=', a: {op: 'var', name: `?${f}`}, b: zero1(1)},
          ...Array.from({length: Math.floor(qi.length / n)}, (_, t): C => ({op: 'or', xs: [eqC({op: 'var', name: `?${f}`}, zero1(0)), at(qi.slice(t * n, (t + 1) * n))]})),
          {op: 'or', xs: [eqC({op: 'var', name: `?${f}`}, zero1(1)), {op: 'not', x: at(qwits(f).map((name): E => ({op: 'var', name})))}]}]
      })]
    const last: C = {op: 'not', x: sInline(m.assume ?? trueC)}, zkeys = carriedKeys([...base, last])
    return {name: 'allowed', hyps: [...base, ...(m.inputMaps ?? []).flatMap(mp => zkeys.map(t => eqC({op: 'get', map: mp, key: t}, zero1(0)))), last], zkeys}
  }
  const allowed = new Map(claims.flatMap(cl => cl.allows).map(a => [a, withWitness(m, a.request, wit => {
    const r2 = proveBuilt(m, laws, inst => allowGoalS(inst, {op: 'and', xs: [a.when, reqTS(wit)]}))
    return r2.proven ? r2 : undefined
  })] as const))
  const allowGoals = [...allowed.values()].flatMap(a => (a ? [a.out.goal!] : []))
  const named = machineNames(m, laws, allSteps, stepLaws, {...opts, ...(hm ? {record: hm.history.record} : {})})
  const vars = [...new Set([...named.vars, ...[...goalsL, ...goalsS, ...allowGoals, ...(hplain?.goals ?? [])].flatMap(g => g.hyps.flatMap(varsOf))])]
  const mapNames = [...new Set([...named.maps, ...[...JSON.stringify([...goalsL, ...goalsS, ...allowGoals]).matchAll(/"op":"get","map":"([^"]+)"/g)].map(x2 => x2[1]!)])]
  const enc = (g: Goal, tree: Tree) => encode({name: `${id}: ${g.name}`, goal: g, tree}, false, true, vars, mapNames)
  const {e, c} = leanTerms(vars, mapNames, id)
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = mapNames.indexOf(name); if (j < 0) throw new Error(`${id}: no map for ${name}`); return j }
  const inline = (c2: C): C => substC(c2, {vars: {}, maps: {}, flags: flagsOfM(m)})
  const lit = (mm: Machine) => machineLit(mm, {e, c}, ix, mx)
  // A loop as Live.lean's record: inputs, start, body, while, precondition, assumption.
  const loopLit = (lp: Loop) => `⟨${list(lp.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(lp.state).map(([name, e2]) => `(${ix(name)}, ${e(e2)})`))},
  ${list(Object.entries(lp.body).map(([name, e2]) => `(${ix(name)}, ${e(e2)})`))},
  ${c(lp.while)},
  ${lp.pre ? c(lp.pre) : TRUE},
  ${lp.assume ? c(lp.assume) : TRUE}⟩`
  // The history: the machine without it (its state without the sums, its assumption without the relations), what a
  // record keeps and the sums, queries and relations over it.
  const hlit = (rels: {when: C, holds: C}[]) => {
    const h = hm!.history, base: Machine = {...hm!, history: undefined}
    return `⟨${lit(base)},
  ${c(h.keep)},
  ${list(h.record.map(f => String(ix(f))))},
  ${list(h.record.map(f => String(ix(`r.${f}`))))},
  ${list(Object.entries(h.sums).map(([name, g]) => `(${ix(name)}, ${e(g)})`))},
  ${list(Object.entries(h.queries).map(([name, g]) => `(${ix(name)}, ${e(g)})`))},
  ${list(rels.map(rel => { if (rel.holds.op !== '<=') throw new Error(`${id}: a relation is a <= b`); return `(${c(rel.when)}, ${e(rel.holds.a)}, ${e(rel.holds.b)})` }))}⟩`
  }
  // Each relation's record goal and its tree, the history's check, and the laws over histories.
  const histBlock = () => {
    const records = hplain!.goals.map(g => { const out = grow(g); if (!('tree' in out)) throw new Error(`${id}: ${g.name} not proven`); const x2 = enc(g, out.tree); return `(${x2.tab}, ${x2.tree})` })
    const tampered = (opts.historyTampers ?? []).map((t, j) => `-- TAMPERED: ${t.what}. Lean computes the check to false.
def ${id}_tampered${j} : HMachine := ${hlit(t.relations)}
example : checkHMachine ${id}_tampered${j} ${id}_proof ${t.withRecordTrees ? `${id}_records` : '[]'} = false := by ${checkBy}`)
    return `def ${id}_records : List (List VDef × Tree) := ${list(records)}
theorem ${id}_hcheck : checkHMachine ${id}_hist ${id}_proof ${id}_records = true := by ${checkBy}
theorem ${id}_hlaws : ∀ ρ M hist, HReach ${id}_hist ρ M hist → ∀ e ∈ ${id}_proof, e.Holds ρ M :=
  hmachine_sound ${id}_hist ${id}_proof ${id}_records ${id}_hcheck
${readable(id, laws, vars, mapNames, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat) (hist : List (Nat → Nat))', hyp: `HReach ${id}_hist ρ μ hist`, call: `${id}_hlaws ρ μ hist h`})}${tampered.length ? `\n${tampered.join('\n')}` : ''}`
  }
  const lawIx = (name: string) => laws.findIndex(l => l.name === name)
  const insts = (inst: Instances) => Object.entries(inst).filter(([name]) => lawIx(name) >= 0 && !laws[lawIx(name)]!.keys?.length).flatMap(([name, keys]) => keys.map(key => `(${lawIx(name)}, ${e(key)})`))
  // A law about every two keys or more is assumed at tuples (kept flattened): the first key, and the rest.
  const pinsts = (inst: Instances) => Object.entries(inst).filter(([name]) => lawIx(name) >= 0 && laws[lawIx(name)]!.keys?.length).flatMap(([name, keys]) => {
    const n = laws[lawIx(name)]!.keys!.length + 1
    return Array.from({length: Math.floor(keys.length / n)}, (_, t) => `(${lawIx(name)}, ${e(keys[t * n]!)}, ${list(keys.slice(t * n + 1, t * n + n).map(e))})`)
  })
  // The facts about one key, and those about several (each instance a tuple, kept flattened: its first key, the rest).
  const facts1 = facts.filter(f => !f.keys?.length), factsN = facts.filter(f => f.keys?.length)
  const finsts = (inst: Instances) => Object.entries(inst).flatMap(([name, keys]) => { const j = facts1.findIndex(f => f.name === name); return j < 0 ? [] : keys.map(key => `(${j}, ${e(key)})`) })
  const pfinsts = (inst: Instances) => Object.entries(inst).flatMap(([name, keys]) => {
    const j = factsN.findIndex(f => f.name === name)
    if (j < 0) return []
    const n = factsN[j]!.keys!.length + 1
    return Array.from({length: Math.floor(keys.length / n)}, (_, t) => `(${j}, ${e(keys[t * n]!)}, ${list(keys.slice(t * n + 1, t * n + n).map(e))})`)
  })
  // Each quantified flag at its tuples (one key each, over one key).
  const qinsts = (inst: Instances) => Object.entries(inst).filter(([name]) => name.startsWith('?')).flatMap(([f, keys]) => {
    const q = m.step.flags?.[f.slice(1)], n = q?.op === 'all' ? boundOf(q).length : 1
    return Array.from({length: Math.floor(keys.length / n)}, (_, t) => `(${ix(f)}, ${list(keys.slice(t * n, (t + 1) * n).map(e))})`)
  })
  const entries = laws.map((law, j) => {
    const g0 = goalsL[2 * j]!, g1 = goalsL[2 * j + 1]!, a = enc(g0, lp.trees[g0.name]!), b = enc(g1, lp.trees[g1.name]!), inst = lp.instances[law.name] ?? {}
    return `def ${id}_l${j} : MLaw := ⟨${c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩
def ${id}_e${j} : SEntry := ⟨${id}_l${j}, ${ix(law.forall ? `${law.forall}#` : '#')}, ${list((law.keys ?? []).map(key => String(ix(key))))}, ${list(insts(inst))}, ${list(qinsts(inst))}, ${list(finsts(inst))}, ${list(pinsts(inst))}, ${list(pfinsts(inst))},
  (${a.tab}, ${a.hyps}, ${a.tree}),
  (${b.tab}, ${b.hyps}, ${b.tree})⟩`
  })
  // A ghosted machine (compose.ts's ghost): the original and its ghosts, the machine Lean checks built from them
  // (Ghost.lean), so the laws that read no ghost are laws of the original.
  const orig: Machine = {...m, state: Object.fromEntries(Object.entries(m.state).filter(([n2]) => !gv.includes(n2))), step: {...m.step, state: Object.fromEntries(Object.entries(m.step.state ?? {}).filter(([n2]) => !gv.includes(n2)))}}
  const h: Helpers = {
    step: sl => { const g = goalsS[allSteps.indexOf(sl)]!; return {pr: enc(g, r.proof!.trees[g.name]!), inst: instOf(sl)} },
    sproof: sl => { const {pr, inst} = h.step(sl); return `(${list(insts(inst))}, ${list(qinsts(inst))}, ${list(finsts(inst))}, ${list(pinsts(inst))}, ${list(pfinsts(inst))}, (${pr.tab}, ${pr.hyps}, ${pr.tree}))` },
    allow: a => {
      const f2 = allowed.get(a)
      if (!f2) return undefined
      const ar = f2.out, pr = enc(ar.goal!, ar.tree!), inst = ar.instances!
      return `(${list(f2.wit.map(([inp, t]) => `(${ix(inp)}, ${e(t)})`))}, (${list(insts(inst))}, ${list(qinsts(inst))}, ${list(finsts(inst))}, ${list(pinsts(inst))}, ${list(pfinsts(inst))}, (${pr.tab}, ${list(ar.goal!.hyps.map(c))}, ${pr.tree})), ${list((ar.goal as Goal & {zkeys: E[]}).zkeys.map(e))})`
    },
  }
  const records = claims.map(cl => cl.render(h)).filter(t => t.length)
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}, with sets (carried ${carried.join(', ') || 'none'}; quantified flags ${quantified.join(', ') || 'none'})
--   (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${mapNames.map((v2, j) => `${j} ${v2}`).join(', ')})
${rf ? `def ${id}_refined : SRefined := ⟨${lit(rf.impl)},
  ${lit(rf.spec)},
  ${list(Object.entries(rf.wit).map(([inp, t]) => `(${ix(`b_${inp}`)}, ${e(t)})`))},
  ${c(rf.stutter)}⟩
def ${id}_machine : SMachine := ${id}_refined.full` : gv.length ? `def ${id}_ghosted : SGhosted := ⟨${lit(orig)},
  ${list(gv.map(v2 => `(${ix(v2)}, ${e(m.state[v2]!)}, ${e(m.step.state?.[v2] ?? {op: 'var', name: v2})})`))}⟩
def ${id}_machine : SMachine := ${id}_ghosted.full
theorem ${id}_ghostOk : sghostOk ${id}_ghosted = true := by ${checkBy}` : hm ? `def ${id}_hist : HMachine := ${hlit(hm.history.relations ?? [])}
def ${id}_machine : SMachine := ${id}_hist.plain` : lp0 ? `def ${id}_loop : Loop := ${loopLit(lp0.loop)}
def ${id}_machine : SMachine := ${id}_loop.machine` : `def ${id}_machine : SMachine := ${lit(m)}`}
${entries.join('\n')}
def ${id}_proof : List SEntry := ${list(laws.map((_, j) => `${id}_e${j}`))}
theorem ${id}_check : checkSMachine ${id}_machine ${id}_proof = true := by ${checkBy}
theorem ${id}_laws : ∀ ρ M, SReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M :=
  smachine_sound ${id}_machine ${id}_proof ${id}_check
${hm ? histBlock() : readable(id, laws, vars, mapNames, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: `SReach ${id}_machine ρ μ`, call: `${id}_laws ρ μ h`})}${opts.noFacts ? '' : factsProof(id, m, mapNames, vars, opts.simp)}${opts.tamper ? `
-- TAMPERED: ${opts.tamper.what}. Lean computes the check to false.
def ${id}_tampered : SMachine := ${lit(opts.tamper.machine)}
example : checkSMachine ${id}_tampered ${id}_proof = false := by ${checkBy}` : ''}${records.length ? `\n\n${records.join('\n\n')}` : ''}${opts.after ? `\n\n${opts.after(ix)}` : ''}`
}

// --- the cyclic certificate's export (GDP_CERT=cyclic) -------------------------------------------------------------

// With GDP_CERT=cyclic (core/cyclic.ts's certOn: a covered proof's certificate is its cyclic proof; or toLean's
// `cyclic`), toLean exports each machine the cyclic route covers from one cyclic
// proof (kernel/cyclic.ts) of its laws and of every step law its claims bring (its own step laws and k-step laws, a
// liveness's), carried to the machine by Bridge.lean's cyc_machine_sound and BridgeRules.lean's cyc_kstep_sound,
// sleads_of_holds (liveness, loops), hreach_plain (histories) and cyc_ghost_holds (ghosts), and each theorem stated as the
// usual export states it: the same machine, laws, step laws and liveness (machineNames numbers them alike), the same
// `<id>.lawN`, `<id>_stepN_holds`, `<id>_liveN_holds`, `<id>_halts`. What the cyclic route doesn't cover goes the usual
// way: a flag that holds at every key, a law that reads a map at a key read from a map, a refinement, and a liveness's
// weak fairness (its helpful requests proven allowed: a claim about requests the run doesn't take).
const envOf = () => (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env
export const cyclicCerts = () => envOf()?.GDP_CERT === 'cyclic'
let certsOn = false, cycTexts = 0
// What the last toLean exported from cyclic certificates, and what went the usual way (and why).
export const certReport: {cyclic: string[], usual: {id: string, why: string}[], translatedSteps: string[]} = {cyclic: [], usual: [], translatedSteps: []}

// The cyclic proof of a machine's laws and of the step laws its claims bring: the laws' nodes (the usual proof
// translated, core/translate.ts; or searched), then each step law's (core/cyclic.ts's stepLawNodes, searched).
// Each liveness's helpful requests (`allows`, one list per liveness) allowed in their regions, for weak fairness: each
// with the first witness (withWitness's order, as the usual export tries them) whose node (core/cyclic.ts's allowNode) is
// proven; a liveness gets them only if every helpful request has one.
type AllowAt = {node: number, wit: [string, E][]}[] | undefined
function cycMachineProof(m: Machine, laws: Law[], allSteps: StepLaw[], allows: {when: C, request: Record<string, E>}[][] = []): {p: Cyclic, stepAt: number[], allowAt: AllowAt[]} | {why: string} {
  const r = proveStepLaws(m, laws, allSteps)
  if (!r.proven || !r.proof) return {why: 'not proven the usual way'}
  const lp = r.proof.laws, instOf = (sl: StepLaw) => r.proof!.perStep?.[sl.name] ?? r.proof!.instances
  // A machine with flags that hold at every key: its sk machine's nodes, the flags' closing facts read where each node
  // reads the run.
  const q = hasQuantified(m), mm = skMachine(m)
  const closing = (sp: NodeSpec, facts: Fact[], insts: Instances[], times: E[]): NodeSpec => {
    if (!q) return sp
    const more = closingInsts(m, facts, insts, times), add = (x: NodeSpec): NodeSpec => ({...x, insts: [...x.insts, ...more], ...(x.variants ? {variants: x.variants.map(add)} : {})})
    return add(sp)
  }
  // The certificates to try, in order: the usual proof translated with its step laws (core/cyclic.ts's machineNodes with
  // `steps`, the certificate GDP_CERT=cyclic makes), where each step law's node is the one BridgeRules.lean's cycKOk reads
  // (the same conclusion and hypotheses among its own); then the laws translated or searched, the step laws' nodes
  // searched (stepLawNodes).
  type Try = {facts: Fact[], specs: NodeSpec[], lawNodes: NodeSpec[], stepAt: number[], translated?: boolean}
  const L = laws.length, mine = (facts: Fact[], lawNodes: NodeSpec[]) => stepLawNodes(mm, laws, allSteps.map(sl => ({law: sl, instances: instOf(sl)})), facts, lawNodes)
    .map((sp, i) => closing(sp, facts, [instOf(allSteps[i]!)], Array.from({length: (allSteps[i]!.steps ?? 1) + 1}, (_, j) => tBack(j))))
  const tries: Try[] = []
  if (!q && routeOf() !== 'search' && allSteps.length) {
    const usualSteps = allSteps.map(sl => { const inst = instOf(sl), g = stepLawObligations(m, laws, inst, sl)[0]!; return {sl, inst, goal: g, tree: r.proof!.trees[g.name]!} })
    const tr = usualSteps.every(u => u.tree) ? machineNodes(m, laws, lp.instances, {trees: lp.trees, steps: usualSteps}) : undefined
    if (tr && !tr.why && tr.specs.length === 3 * L + 2 * allSteps.length) {
      const own = mine(tr.facts, tr.specs), id = (x: unknown) => JSON.stringify(x)
      const fits = allSteps.every((_, j) => {
        const a = tr.specs[3 * L + 2 * j + 1]!, b = own[j]!, hs = new Set(b.hyps.map(id))
        return id(a.concl) === id(b.concl) && a.hyps.every(h => hs.has(id(h)))
      })
      if (fits) tries.push({facts: tr.facts, specs: tr.specs, lawNodes: tr.specs, stepAt: allSteps.map((_, j) => 3 * L + 2 * j + 1), translated: true})
    }
  }
  for (const base of (q ? [qflagNodes(m, laws, lp.instances)]
    : [...(routeOf() !== 'search' ? [machineNodes(m, laws, lp.instances, {trees: lp.trees})] : []), machineNodes(m, laws, lp.instances)]).filter(b => !b.why)) {
    tries.push({facts: base.facts, specs: [...base.specs, ...mine(base.facts, base.specs)], lawNodes: base.specs, stepAt: allSteps.map((_, j) => base.specs.length + j)})
  }
  let last = 'no nodes'
  for (const {facts, specs: specs0, lawNodes, stepAt, translated} of tries) {
    let specs = specs0, v = proveCyclic(facts, specs)
    if (!(v.proven && v.checked)) { last = v.proven ? `not checked (${v.why})` : `${v.node}: ${v.goal}: ${v.stuck}`; continue }
    const allowAt = allows.map((group): AllowAt => {
      if ((lawNodes[0]?.rank.length ?? 2) < 2) return undefined
      const before = specs, out: {node: number, wit: [string, E][]}[] = []
      for (const a of group) {
        const found = withWitness(m, a.request, wit => {
          const spec = allowNode(mm, laws, r.proof!.instances, {op: 'and', xs: [a.when, reqTS(wit)]}, facts, lawNodes, `${m.name}: allowed`,
            q ? closingInsts(m, facts, [r.proof!.instances, ...Object.values(lp.instances)], [{op: 'var', name: 't$'}], laws) : [])
          const v2 = proveCyclic(facts, [...specs, spec])
          return v2.proven && v2.checked ? {spec, v2} : undefined
        })
        if (!found) { specs = before; return undefined }
        out.push({node: specs.length, wit: found.wit})
        specs = [...specs, found.out.spec]; v = found.out.v2
      }
      return out
    })
    if (v.proven && v.checked) { if (translated) certReport.translatedSteps.push(m.name); return {p: v.proof, stepAt, allowAt} }
  }
  return {why: last}
}

// A machine (with a history, ghosts, a liveness or as a loop's) from one cyclic proof, or why it can't be.
export function cycMachineToLean(id: string, given: Machine, laws: Law[], opts: {stepLaws?: StepLaw[], liveness?: Liveness[], simp?: string[], free?: string[],
    ghosts?: string[], after?: (ix: (name: string) => number) => string, loop?: {loop: Loop}, noFacts?: boolean,
    refined?: {impl: Machine, spec: Machine, wit: Record<string, E>, stutter: C, specPre: number, step: StepLaw}} = {}): {text: string} | {why: string} {
  const hm = given.history ? {...given, history: {...given.history, prune: undefined}} : undefined
  const hplain = hm ? historyMachine(hm) : undefined, m = hplain ? hplain.machine : given
  const stepLaws = opts.stepLaws ?? [], gv = opts.ghosts ?? [], lp0 = opts.loop
  if (!cyclicMachine(skMachine(m), laws)) return {why: 'a law reading a map at a key read from a map'}
  // With flags that hold at every key, the sk machine's encoding and BridgeRules.lean's q bridges.
  const mq = skMachine(m), Q = hasQuantified(m) ? 'Q' : '', q = hasQuantified(m) ? 'q' : ''
  const lives = (opts.liveness ?? []).map(l => ({l, ...livenessParts(m, l)}))
  // A refinement's step law: the spec stutters or allows the request it is sent, its `then` Lean's SRefined.allowed (the
  // spec's assumption at the witness, the composite's flags inlined).
  const rf = opts.refined
  const rfStep: StepLaw | undefined = rf && {...rf.step, when: undefined, then: {op: 'or', xs: [rf.stutter, substC(rf.spec.assume ?? trueC, {vars: Object.fromEntries(Object.entries(rf.wit).map(([inp, t2]) => [`b_${inp}`, t2])), maps: {},
    flags: Object.fromEntries(Object.keys(m.step.flags ?? {}).map(f => [f, {op: 'flag', name: f} as C]))})]}}
  const allSteps = [...(rfStep ? [rfStep] : stepLaws), ...lives.flatMap(x => [x.stay, x.cover, ...x.helps])]
  const made = cycMachineProof(m, laws, allSteps, lives.map(x => x.helps.map((hs, i) => ({when: hs.when as C, request: livenessHelpful(x.l)[i]!.request}))))
  if ('why' in made) return made
  const {p, stepAt, allowAt} = made
  const named = machineNames(m, laws, allSteps, stepLaws, {...(opts.free ? {free: opts.free} : {}), ...(hm ? {record: hm.history.record} : {})})
  const sc = cycScope([p], {machine: mq, laws})
  const vars = [...new Set([...named.vars, ...sc.vars])], maps = [...new Set([...named.maps, ...sc.maps])]
  const {e, c} = leanTerms(vars, maps, id)
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = maps.indexOf(name); if (j < 0) throw new Error(`${id}: no map for ${name}`); return j }
  const lit = (mm: Machine) => machineLit(mm, {e, c}, ix, mx)
  const inline = (c2: C): C => substC(c2, {vars: {}, maps: {}, flags: flagsOfM(m)})
  const keysOf = (l: Law) => [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])]
  const keysL = (l: Law) => list(keysOf(l).map(k2 => String(ix(k2))))
  const state = Object.keys(m.state), carried = m.inputMaps ?? []
  const primesL = () => list(state.map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`)), primeMapsL = () => list(Object.keys(m.maps ?? {}).map(mp => `(${mx(mp)}, ${mx(`${mp}'`)})`))
  const node = (i: number) => `${id}_node${i}`
  const kstep = (sk: string, i: number) => `cyc_${q}kstep_sound ${id}_machine ${id}_enc ${id}_facts ${id}_nodes ${id}_check ${sk} ${node(i)} ${node(i)}_mem`
  // The machine as the usual export defines it: with a history its plain machine, with ghosts the ghosted one, a loop's.
  const orig: Machine = {...m, state: Object.fromEntries(Object.entries(m.state).filter(([n2]) => !gv.includes(n2))), step: {...m.step, state: Object.fromEntries(Object.entries(m.step.state ?? {}).filter(([n2]) => !gv.includes(n2)))}}
  const hlit = () => {
    const h = hm!.history, base: Machine = {...hm!, history: undefined}
    return `⟨${lit(base)},
  ${c(h.keep)},
  ${list(h.record.map(f => String(ix(f))))},
  ${list(h.record.map(f => String(ix(`r.${f}`))))},
  ${list(Object.entries(h.sums).map(([name, g]) => `(${ix(name)}, ${e(g)})`))},
  ${list(Object.entries(h.queries).map(([name, g]) => `(${ix(name)}, ${e(g)})`))},
  ${list((h.relations ?? []).map(rel => { if (rel.holds.op !== '<=') throw new Error(`${id}: a relation is a <= b`); return `(${c(rel.when)}, ${e(rel.holds.a)}, ${e(rel.holds.b)})` }))}⟩`
  }
  const loopLit = (lp: Loop) => `⟨${list(lp.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(lp.state).map(([name, e2]) => `(${ix(name)}, ${e(e2)})`))},
  ${list(Object.entries(lp.body).map(([name, e2]) => `(${ix(name)}, ${e(e2)})`))},
  ${c(lp.while)},
  ${lp.pre ? c(lp.pre) : TRUE},
  ${lp.assume ? c(lp.assume) : TRUE}⟩`
  const machineDef = rf ? `def ${id}_refined : SRefined := ⟨${lit(rf.impl)},
  ${lit(rf.spec)},
  ${list(Object.entries(rf.wit).map(([inp, t2]) => `(${ix(`b_${inp}`)}, ${e(t2)})`))},
  ${c(rf.stutter)}⟩
def ${id}_machine : SMachine := ${id}_refined.full` : gv.length ? `def ${id}_ghosted : SGhosted := ⟨${lit(orig)},
  ${list(gv.map(v2 => `(${ix(v2)}, ${e(m.state[v2]!)}, ${e(m.step.state?.[v2] ?? {op: 'var', name: v2})})`))}⟩
def ${id}_machine : SMachine := ${id}_ghosted.full
theorem ${id}_ghostOk : sghostOk ${id}_ghosted = true := by ${checkBy}` : hm ? `def ${id}_hist : HMachine := ${hlit()}
def ${id}_machine : SMachine := ${id}_hist.plain` : lp0 ? `def ${id}_loop : Loop := ${loopLit(lp0.loop)}
def ${id}_machine : SMachine := ${id}_loop.machine` : `def ${id}_machine : SMachine := ${lit(m)}`
  const enc = `⟨${['u$', 'k$', 'T$', 'O$', 't$'].map(ix).join(', ')},
  ${list([...state, ...mq.inputs].map(x => `(${ix(x)}, ${mx(`${x}@`)})`))},
  ${list([...Object.keys(m.maps ?? {}), ...carried].map(x => `(${mx(x)}, ${mx(`${x}@`)})`))}⟩`
  // Each law: Bridge.lean's check and theorem, then all of them as the usual export's `<id>_laws` states them.
  const lawBlocks = laws.map((l, j) => `-- ${l.name}
def ${id}_law${j} : C := ${c(l.holds)}
def ${id}_l${j} : MLaw := ⟨${id}_law${j}, ${l.forall ? `some ${ix(l.forall)}` : 'none'}⟩
theorem ${id}_law${j}_ok : cyc${Q}MOk ${id}_machine ${id}_enc ${id}_facts ${id}_law${j} ${keysL(l)} ${node(j)} = true := by ${checkBy}
theorem ${id}_law${j}_holds : ∀ ρ M, SReach ${id}_machine ρ M → ∀ ρ' : Nat → Nat, (∀ i, i ∉ ${keysL(l)} → ρ' i = ρ i) → evalC ρ' M ${id}_law${j} = true :=
  cyc_${q}machine_sound ${id}_machine ${id}_enc ${id}_facts ${id}_nodes ${id}_check ${id}_law${j} ${keysL(l)} ${node(j)} ${node(j)}_mem ${id}_law${j}_ok`).join('\n')
  const keys2 = (l: Law) => list((l.keys ?? []).map(k2 => String(ix(k2))))
  const oneOf = (hyp: string) => `simp only [${id}_mlaws, List.mem_cons, List.not_mem_nil, or_false] at ${hyp}`
  const lawsThm = `def ${id}_mlaws : List (MLaw × List Nat) := ${list(laws.map((l, j) => `(${id}_l${j}, ${keys2(l)})`))}
theorem ${id}_laws : ∀ ρ M, SReach ${id}_machine ρ M → ∀ e ∈ ${id}_mlaws, holdsOver e.1 M e.2 ρ := by
  intro ρ M h e he
  ${laws.length ? `${oneOf('he')}
  rcases he with ${laws.map(() => 'rfl').join(' | ')}
  ${laws.map((_, j) => `· exact cyc_machine_holds (${id}_law${j}_holds ρ M h)`).join('\n  ')}` : `simp [${id}_mlaws] at he`}`
  // A history's record goals (leaf goals, as the usual export has them), and its laws over histories.
  const histBlock = () => {
    const records = hplain!.goals.map(g => { const out = grow(g); if (!('tree' in out)) throw new Error(`${id}: ${g.name} not proven`); const x2 = encode({name: `${id}: ${g.name}`, goal: g, tree: out.tree}, false, true, vars, maps); return `(${x2.tab}, ${x2.tree})` })
    const reach = (hyp: string) => `(hreach_plain ${id}_hist ${id}_records ${id}_hcheck ρ μ hist ${hyp})`
    return `def ${id}_records : List (List VDef × Tree) := ${list(records)}
theorem ${id}_hcheck : checkHMachine ${id}_hist [] ${id}_records = true := by ${checkBy}
theorem ${id}_hlaws : ∀ ρ M hist, HReach ${id}_hist ρ M hist → ∀ e ∈ ${id}_mlaws, holdsOver e.1 M e.2 ρ :=
  fun ρ M hist h => ${id}_laws ρ M (hreach_plain ${id}_hist ${id}_records ${id}_hcheck ρ M hist h)
${readable(id, laws, vars, maps, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat) (hist : List (Nat → Nat))', hyp: `HReach ${id}_hist ρ μ hist`, call: '',
  have: j => `have hl : holdsOver ${id}_l${j} μ ${keys2(laws[j]!)} ρ := cyc_machine_holds (${id}_law${j}_holds ρ μ ${reach('h')})`})}`
  }
  // The machine's own step laws, one step or k (BridgeRules.lean's cyc_kstep_sound): the SKStep as the usual export
  // writes it, with no certificate in it.
  const stepBlocks = (rf ? [] : stepLaws).map((sl, j) => {
    const kk = sl.steps ?? 1
    const ren = Array.from({length: kk}, (_, s2) => (s2 === 0 ? '[]' : list(extOf(m).map(v2 => `(${ix(v2)}, ${ix(`${v2}@${s2 + 1}`)})`))))
    const mren = Array.from({length: kk}, (_, s2) => (s2 === 0 ? '[]' : list(carried.map(mp => `(${mx(mp)}, ${mx(`${mp}@${s2 + 1}`)})`))))
    const names = Array.from({length: kk - 1}, (_, s2) => list(state.map(n2 => `(${ix(n2)}, ${ix(stateName(n2, s2 + 1))})`)))
    return `-- Step law${kk > 1 ? ` over ${kk} steps` : ''}: ${sl.name}
def ${id}_step${j} : SKStep := ⟨⟨${list(kWhens(mq, sl).map(c))},
  ${c(inline(sl.then))},
  ${list(ren)},
  ${primesL()},
  ${primeMapsL()},
  [],
  ([], .leaf [] [] [] [])⟩,
  ${list(mren)},
  [], [], [], [], [],
  ${list(names)}⟩
theorem ${id}_step${j}_ok : cyc${Q}KOk ${id}_machine ${id}_enc ${id}_facts ${id}_step${j} ${node(stepAt[j]!)} = true := by ${checkBy}
theorem ${id}_step${j}_holds : SKStepHolds ${id}_machine ${id}_step${j} :=
  ${kstep(`${id}_step${j}`, stepAt[j]!)} ${id}_step${j}_ok`
  })
  // Each liveness from its step laws (BridgeRules.lean's sleads_of_holds), as the usual export states it.
  let at = stepLaws.length
  const liveBlocks = lives.map(({l, helps}, j) => {
    const lid = `${id}_live${j}`, at0 = at, s0 = stepAt[at0]!, c0 = stepAt[at0 + 1]!, hAt = (i: number) => stepAt[at0 + 2 + i]!
    at += 2 + helps.length
    // Under weak fairness, where each helpful request is proven allowed in its region (BridgeRules.lean's cyc_allow_sound).
    const al = allowAt[j], wfp = al ? `
${al.map((a, i) => `def ${lid}_wit${i} : List (Nat × E) := ${list(a.wit.map(([inp, t2]) => `(${ix(inp)}, ${e(t2)})`))}`).join('\n')}
theorem ${lid}_allows : ∀ h ∈ ${lid}.helps, ∃ wit : List (Nat × E), distinct ((h.2 ++ wit).map (·.1)) = true
    ∧ (∀ p ∈ wit, (${id}_machine.f.m.inputs.contains p.1 = true ∧ avoids ${id}_machine.extVars (.eq p.2 p.2) = true) ∧ avoidsMaps ${id}_machine.carried (.eq p.2 p.2) = true)
    ∧ AllowHolds ${id}_machine (.and (liveHelpWhen ${lid} h) (reqC wit)) := by
  intro h hh
  simp only [${lid}, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with ${helps.map(() => 'rfl').join(' | ')}
  ${al.map((a, i) => `· exact ⟨${lid}_wit${i}, by ${checkBy}, by ${checkBy}, cyc_${q}allow_sound ${id}_machine ${id}_enc ${id}_facts ${id}_nodes ${id}_check _ ${node(a.node)} ${node(a.node)}_mem (by ${checkBy})⟩`).join('\n  ')}
/-- ${l.name}, under weak fairness: along every run that takes each helpful request whenever, from some point on, it
stays allowed, \`from\` is followed by \`to\`. -/
theorem ${lid}_holds_wf (run : SRun ${id}_machine)
    (fair : ∀ h ∈ ${lid}.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView ${id}_machine (run.st m).1 (run.st m).2 ι κ).1 (sView ${id}_machine (run.st m).1 (run.st m).2 ι κ).2 ${id}_machine.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 ${lid}.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 ${lid}.to = true :=
  sleads_wf_of_holds ${id}_machine ${lid} ${lid}_ok ${lid}_stay ${lid}_cover ${lid}_helps ${lid}_allows run fair` : ''
    return `-- Liveness: ${l.name}
def ${lid} : Live := ${liveLit(l, {e, c}, ix, primesL(), primeMapsL())}
theorem ${lid}_ok : sliveOk ${id}_machine ${lid} = true := by ${checkBy}
theorem ${lid}_stay : SKStepHolds ${id}_machine (liveK ${lid} ${lid}.pend (liveStayC ${lid})) := ${kstep('_', s0)} (by ${checkBy})
theorem ${lid}_cover : SKStepHolds ${id}_machine (liveK ${lid} ${lid}.pend (liveCoverC ${lid})) := ${kstep('_', c0)} (by ${checkBy})
theorem ${lid}_helps : ∀ h ∈ ${lid}.helps, SKStepHolds ${id}_machine (liveK ${lid} (liveHelpWhen ${lid} h) (liveHelpThen ${lid})) := by
  intro h hh
  simp only [${lid}, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with ${helps.map(() => 'rfl').join(' | ')}
  ${helps.map((_, i) => `· exact ${kstep('_', hAt(i))} (by ${checkBy})`).join('\n  ')}
/-- ${l.name}: along every run that takes each helpful request infinitely often, \`from\` is followed by \`to\`. -/
theorem ${lid}_holds (run : SRun ${id}_machine)
    (fair : ∀ h ∈ ${lid}.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 ${lid}.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 ${lid}.to = true :=
  sleads_of_holds ${id}_machine ${lid} ${lid}_ok ${lid}_stay ${lid}_cover ${lid}_helps run fair${wfp}`
  })
  const loopBlock = lp0 ? `/-- ${lp0.loop.name} halts: for params meeting its precondition, no run of turns goes on forever. -/
theorem ${id}_halts : ∀ maps ρ0, evalC ρ0 maps ${id}_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS ${id}_loop.init ρ0 maps ∧ ∀ n, Turn ${id}_loop maps (f n) (f (n + 1)) :=
  loop_halts_of ${id}_loop ${id}_live0 rfl rfl (by intro h hh; simp only [${id}_live0, List.mem_singleton] at hh; subst hh; rfl) (by ${checkBy}) ${id}_live0_holds` : ''
  const ghostBlock = gv.length ? `-- The laws that read no ghost hold of the machine without its ghosts.
theorem ${id}_orig_laws : ∀ ρ M, SReach ${id}_ghosted.orig ρ M → ∀ e ∈ ${id}_mlaws, avoids ${id}_ghosted.vars e.1.holds = true → holdsOver e.1 M e.2 ρ := by
  intro ρ M hr e he hav
  ${laws.length ? `${oneOf('he')}
  rcases he with ${laws.map(() => 'rfl').join(' | ')}
  ${laws.map((l, j) => `· exact cyc_machine_holds (cyc_ghost_holds ${id}_ghosted ${id}_ghostOk ${id}_law${j} ${keysL(l)} hav ${id}_law${j}_holds ρ M hr)`).join('\n  ')}` : `simp [${id}_mlaws] at he`}` : ''
  const refineBlock = rf ? `theorem ${id}_allowed : SKStepHolds ${id}_machine (srStep ${id}_refined ${primesL()} ${primeMapsL()} noSProof) := ${kstep('_', stepAt[0]!)} (by ${checkBy})
theorem ${id}_refines : ∀ ρ M, SReach ${id}_refined.impl ρ M → ∃ ρc Mc σ Ms, SReach ${id}_refined.full ρc Mc ∧ Agree ${id}_refined.SV ρc ρ
    ∧ (∀ mp, mp ∉ ${id}_refined.SM → Mc mp = M mp) ∧ SReach ${id}_refined.spec σ Ms ∧ Agree ${id}_refined.X σ ρc
    ∧ (∀ mp, mp ∉ ${id}_refined.IM → mp ∉ ${id}_refined.spec.carried → Ms mp = Mc mp) ∧ ∀ e ∈ ${id}_mlaws, holdsOver e.1 Mc e.2 ρc :=
  srefines_of_holds ${id}_refined (by ${checkBy}) (by ${checkBy}) _ ${id}_laws
    (fun ρ M h => by have hp := ${id}_law${rf.specPre}_holds ρ M h ρ (fun _ _ => rfl); exact hp)
    ${primesL()} ${primeMapsL()} noSProof ${id}_allowed (by ${checkBy}) (by ${checkBy}) (by ${checkBy})` : ''
  const records = [...stepBlocks, ...(refineBlock ? [refineBlock] : []), ...liveBlocks, ...(loopBlock ? [loopBlock] : []), ...(ghostBlock ? [ghostBlock] : [])]
  cycTexts++
  return {text: `-- ${m.name}: ${laws.map(l => l.name).join('; ')}, as one cyclic proof (its laws' nodes, then ${allSteps.length} step laws')
--   (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${maps.map((v2, j) => `${j} ${v2}`).join(', ')})
${machineDef}
def ${id}_enc : CycEnc := ${enc}
${cycProofText(id, p, [], vars, maps)}
${lawBlocks}
${lawsThm}
${hm ? histBlock() : readable(id, laws, vars, maps, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: `SReach ${id}_machine ρ μ`, call: '',
  have: j => `have hl : holdsOver ${id}_l${j} μ ${keys2(laws[j]!)} ρ := cyc_machine_holds (${id}_law${j}_holds ρ μ h)`})}${opts.noFacts ? '' : factsProof(id, m, maps, vars, opts.simp)}${records.length ? `\n\n${records.join('\n\n')}` : ''}${opts.after ? `\n\n${opts.after(ix)}` : ''}`}
}

// A fold from its cyclic proof (Bridge.lean's cyc_fold_sound): the fold numbered as foldToLean numbers it, each law's
// theorem over trees, and all of them as the usual export's `<id>_laws` states them.
function cycFoldToLean(id: string, f: Fold, laws: Law[]): {text: string} | {why: string} {
  const gs = foldObligations(f, laws), trees: Record<string, Tree> = {}
  for (const g of gs) { const o = grow(g); if (!('tree' in o)) return {why: `${g.name}: not proven the usual way`}; trees[g.name] = o.tree }
  let p: Cyclic | undefined, why = 'no nodes'
  for (const base of [...(routeOf() !== 'search' ? [foldNodes(f, laws, trees)] : []), foldNodes(f, laws)].filter(b => !b.why)) {
    const v = proveCyclic(base.facts, base.specs)
    if (v.proven && v.checked) { p = v.proof; break }
    why = v.proven ? `not checked (${v.why})` : `${v.node}: ${v.goal}: ${v.stuck}`
  }
  if (!p) return {why}
  const st = Object.keys(f.leaf), v = (name: string): E => ({op: 'var', name})
  const sc = cycScope([p], undefined, [...[...f.params, ...f.inputs, ...st, ...st.map(x => `l_${x}`), ...st.map(x => `r_${x}`), 'n$', 'N$'].map(v),
    ...Object.values(f.leaf), ...Object.values(f.node), ...laws.map((l): E => ({op: 'if', c: l.holds, then: v('n$'), else: v('n$')})),
    ...['Kind', 'Left', 'Right', ...st, ...f.inputs].map((x): E => ({op: 'get', map: `${x}@`, key: v('n$')}))])
  const vars = [...new Set([...f.params, ...f.inputs, ...st, ...st.map(n2 => `l_${n2}`), ...st.map(n2 => `r_${n2}`), ...sc.vars])], maps = sc.maps
  const t = leanTerms(vars, maps, id)
  cycTexts++
  return {text: `-- ${f.name}: ${laws.map(law => law.name).join('; ')}, as one cyclic proof  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${maps.map((v2, j) => `${j} ${v2}`).join(', ')})
${cycProofText(id, p, [], vars, maps)}
${cycFoldLean(id, f, laws, vars, maps, t)}
def ${id}_flaws : List C := ${list(laws.map((_, j) => `${id}_law${j}`))}
theorem ${id}_laws : ∀ maps ρ, evalC ρ maps ${id}_fold.pre = true → ∀ t, Allowed ${id}_fold ρ maps t →
    ∀ l ∈ ${id}_flaws, evalC (foldT ${id}_fold ρ maps t) maps l = true := by
  intro maps ρ hp t ht l hl
  simp only [${id}_flaws, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ${laws.map(() => 'rfl').join(' | ')}
  ${laws.map((_, j) => `· exact ${id}_law${j}_holds maps ρ hp t ht`).join('\n  ')}`}
}

// A function defined by a recurrence (core/dsl.ts recur): its Lean definition by the same recurrence, and its lemmas
// proven together by induction (each case by omega, its min, max and ifs split first), and its laws between two points
// by induction on the distance. A function of several arguments is `<name>_rec`, its further arguments first, and the
// function the machine reads is its key's (`<name>`, through Recur.unpair: the arguments paired as the builders pair
// them, (a + b)² + b, which Recur.pair_inj proves injective). The kernel proved the lemmas by the same inductions; Lean
// proves them again of the definition.
const recurArg = (a: string) => `«${a}»`
// The arguments a key was paired from (the builders' argsKey: left-nested (k + a)² + a), if it was.
const unpairKey = (key: E, n: number): E[] | undefined => {
  if (n === 1) return [key]
  if (key.op !== 'add' || key.a.op !== 'prod' || key.a.a.op !== 'add') return undefined
  const s = key.a.a, b = key.b
  if (JSON.stringify(key.a.b) !== JSON.stringify(s) || JSON.stringify(s.b) !== JSON.stringify(b)) return undefined
  const rest = unpairKey(s.a, n - 1)
  return rest ? [...rest, b] : undefined
}
// f at x (and the further arguments), as Lean reads it.
const recurCall = (lean: string, r: Recurrence, x: string, args: string[] = r.args.map(recurArg)) => (r.args.length ? `(${lean}_rec ${[...args, x].join(' ')})` : `(${lean} ${x})`)
type Uses = Record<string, {lean?: string, recur?: Recurrence, arity: number}>
// A read of a function the recurrence uses: a recurrence by its definition at the unpaired arguments, any other by its
// Lean term at the key.
const useRead = (uses: Uses, where: string) => (map: string, key: E, e: (t: E) => string): string => {
  const u = uses[map]
  if (!u?.lean) throw new Error(`${where}: ${map} has no Lean definition`)
  if (u.recur) { const args = unpairKey(key, u.arity); if (!args) throw new Error(`${where}: ${map} read at a key not paired by its arguments`); return recurCall(u.lean, u.recur, e(args[0]!), args.slice(1).map(e)) }
  return `((${u.lean}) ${e(key)})`
}
// The lemmas of the recurrences a term reads, at the keys it reads them, with the names as given.
const useLemmas = (uses: Uses, t: E | C, names: Record<string, string>, where: string): string[] => {
  const out: string[] = []
  const walk = (x: unknown): void => {
    if (!x || typeof x !== 'object') return
    const o = x as {op?: string, map?: string, key?: E}
    if (o.op === 'get' && o.map) {
      const u = uses[o.map]
      if (u?.recur?.lemmas.length) {
        const args = unpairKey(o.key!, u.arity)!, s = leanSurface(names, where, useRead(uses, where)).e
        out.push(`have := ${u.lean}_lemmas ${[...args.slice(1).map(s), s(args[0]!)].join(' ')}`)
      }
    }
    for (const v of Object.values(o)) walk(v)
  }
  walk(t)
  return [...new Set(out)]
}
// The kernel's own proof of a recurrence's lemmas (or of its laws between two points), for Lean to check: the machine
// it was proven by, exported with its trees (smachine_sound gives its laws at every reachable state), and the run of
// that machine that reaches x and f(x) (or y = x + d and f(y) from x and f(x)), so each law, read there, is the lemma.
// The proof needs no tactic beyond simp's arithmetic of the machine's terms: what the kernel proved (products of two
// terms among it) Lean checks as the kernel's own tree.
function recurKernel(lean: string, r: Recurrence, uses: Uses, which: 'lemmas' | 'between'): {pre: string, proof: (from: string) => string} | undefined {
  const pr = r.proofs?.[which]
  if (!pr) return undefined
  const m = pr.machine, two = which === 'between', id = `${lean.replace(/[^A-Za-z0-9_]/g, '_')}_${two ? 'two' : 'ind'}`
  const vars = [...m.params, ...m.inputs, ...Object.keys(m.state)], col = (n: string) => { const j = vars.indexOf(n); if (j < 0) throw new Error(`${id}: no column for ${n}`); return j }
  const fnNames = Object.keys(m.fns ?? {}), args = r.args.map(recurArg), argNames = Object.fromEntries(r.args.map(a => [a, recurArg(a)]))
  const F = (x: string) => recurCall(lean, r, x)
  const surface = leanSurface(argNames, lean, useRead(uses, lean))
  const binders = [...r.args.map(a => `(${recurArg(a)} : Nat)`), ...(two ? ['(x : Nat)'] : [])].join(' '), ps = [...args, ...(two ? ['x'] : [])].join(' ')
  const start: [string, string][] = [...r.args.map(a => [a, recurArg(a)] as [string, string]), ...(m.params.includes('fx0') ? [['fx0', surface.e(r.zero)] as [string, string]] : []),
    ...(two ? [['x', 'x'], ['fx', F('x')]] as [string, string][] : [])]
  const chain = (pairs: [number, string][], dflt: string, v: string) => pairs.reduceRight((acc, [c, e]) => `if ${v} = ${c} then ${e} else ${acc}`, dflt)
  // What the run holds after n steps, column by column.
  const at = (n: string): [number, string][] => two
    ? [[col('y'), `x + ${n}`], [col('fy'), F(`(x + ${n})`)], [col('x'), 'x'], [col('fx'), F('x')], ...r.args.map(a => [col(a), recurArg(a)] as [number, string])]
    : [[col('x'), n], [col('fx'), F(n)], ...r.args.map(a => [col(a), recurArg(a)] as [number, string])]
  const hs = at('n').map((_, i) => `h${i}`)
  const recurDefs = [r.args.length ? `${lean}_rec` : lean, ...Object.values(uses).flatMap(u => (u.recur ? (u.recur.args.length ? [`${u.lean}_rec`, `${u.lean}_key`] : [u.lean!]) : []))]
  const one = (m.facts ?? []).some(f => !f.keys?.length), several = (m.facts ?? []).some(f => f.keys?.length)
  // A fact of the params at the start of the laws between: the lemma at x and f(x), its own conjunct.
  const proj = (j: number, k: number) => (k === 1 ? '' : j < k - 1 ? `${'.2'.repeat(j)}.1` : '.2'.repeat(k - 1))
  const cite = (f: Law) => { const j = r.lemmas.findIndex(l => f.name === `${l.name} at x`); return two && j >= 0 ? `(${lean}_lemmas ${args.join(' ')} x)${proj(j, r.lemmas.length)}` : undefined }
  const factsAt = factsProof(id, m, fnNames, vars, [`${id}_ρ`, `${id}_μ`, ...recurDefs], {binders, rho: `(${id}_ρ ${ps})`, mu: `${id}_μ`, cite})
  const unfold = [`${id}_machine`, `${id}_μ`, 'applyS', 'assoc', 'lookup', 'evalE', 'evalC', ...recurDefs].join(', ')
  // (with cyclic certificates, the machine's laws from its cyclic proof, where it has one)
  const cyc = certsOn ? cycMachineToLean(id, m, pr.laws, {noFacts: true}) : undefined
  const pre = `
${cyc && 'text' in cyc ? cyc.text : smachineToLean(id, m, pr.laws, {noFacts: true})}
def ${id}_ρ ${binders} : Nat → Nat := fun i => ${chain(start.map(([n, e]) => [col(n), e]), '0', 'i')}
noncomputable def ${id}_μ : Nat → Nat → Nat := fun j => ${chain(fnNames.map((n, j) => [j, `(${m.fns![n]!.lean})`]), 'fun _ => 0', 'j')}${factsAt}
-- The run of ${m.name} that ${two ? 'counts y up from x' : 'counts x up from 0'}: reachable, and holding ${two ? 'y = x + n and f(y)' : 'x = n and f(x)'}.
theorem ${id}_run ${binders} : ∀ n, ∃ ρ, SReach ${id}_machine ρ ${id}_μ ∧ ${at('n').map(([c, e]) => `ρ ${c} = ${e}`).join(' ∧ ')} := by
  intro n
  induction n with
  | zero =>
    refine ⟨_, SReach.start (${id}_ρ ${ps}) ${id}_μ ?_ ?_ ?_ ?_, ${at('0').map(() => '?_').join(', ')}⟩
    · intro p hp; simp [${id}_machine] at hp
    · simp [${id}_machine, evalC, evalE]
    · ${one ? `exact ${id}_facts_at ${ps}` : `intro l hl; simp [${id}_machine] at hl`}
    · ${several ? `exact ${id}_pfacts_at ${ps}` : `intro p hp; simp [${id}_machine] at hp`}
    all_goals simp [${id}_ρ, ${unfold}]
  | succ n ih =>
    obtain ⟨ρ, hr, ${hs.join(', ')}⟩ := ih
    refine ⟨_, SReach.step ρ ${id}_μ (fun _ => 0) (fun _ _ => 0) hr ?_, ${at('0').map(() => '?_').join(', ')}⟩
    · simp [sView, ${id}_machine, evalC, evalE]
    all_goals (try rw [show x + (n + 1) = x + n + 1 from by omega])
    all_goals simp [sNext, sView, decideFlags, decideQ, flagSub, withInputs, withCarried, ${hs.join(', ')}, ${unfold}]`
  // The lemmas (or the laws between, after the lemmas at y): each the machine's law read on the run.
  const own = two ? r.between.map((_, j) => r.lemmas.length + j) : r.lemmas.map((_, j) => j)
  const each = (j: number) => (cyc && 'text' in cyc
    ? `by have h := ${id}_law${j}_holds ρ ${id}_μ hr ρ (fun _ _ => rfl); simp [${id}_law${j}, evalC, evalE, ${hs.join(', ')}] at h; simpa using h`
    : `by have h := ${id}_laws ρ ${id}_μ hr ${id}_e${j} (by simp [${id}_proof]); simp [SEntry.Holds, holdsOver, ${id}_e${j}, ${id}_l${j}, MLaw.Holds, evalC, evalE, ${hs.join(', ')}] at h; simpa using h`)
  const proof = (from: string) => `(obtain ⟨ρ, hr, ${hs.join(', ')}⟩ := ${id}_run ${from}; exact ${own.length === 1 ? `(${each(own[0]!)})` : `⟨${own.map(j => `(${each(j)})`).join(', ')}⟩`})`
  return {pre, proof}
}
export function recurToLean(lean: string, r: Recurrence, uses: Uses = {}): string {
  const binders = r.args.map(a => `(${recurArg(a)} : Nat)`).join(' '), argNames = Object.fromEntries(r.args.map(a => [a, recurArg(a)]))
  const self = r.args.length ? `${lean}_rec` : lean
  const read = useRead(uses, lean)
  const surface = (names: Record<string, string>) => leanSurface({...argNames, ...names}, lean, read)
  const text = JSON.stringify(r), unfold = [self, ...(text.includes('"op":"min"') ? ['Nat.min_def'] : []), ...(text.includes('"op":"max"') ? ['Nat.max_def'] : [])].join(', ')
  const lemmaAt = (x: string) => r.lemmas.map(l => `(${surface({x, fx: recurCall(lean, r, x)}).c(l.holds)})`).join(' ∧ ')
  const close = (haves: string[]) => `${haves.map(h => `${h}; `).join('')}(repeat' split) <;> omega`
  const step = (n: string) => useLemmas(uses, r.next, {...argNames, x: n, prev: recurCall(lean, r, n)}, lean)
  // Each theorem by the kernel's proof (its machine and the run), or by induction with omega where that fails.
  const kl = recurKernel(lean, r, uses, 'lemmas'), kb = recurKernel(lean, r, uses, 'between')
  const lemmas = r.lemmas.length ? `${kl?.pre ?? ''}
-- ${r.lemmas.map(l => l.name).join('; ')}
theorem ${lean}_lemmas ${binders} (x : Nat) : ${lemmaAt('x')} := by
  first
  | ${kl ? kl.proof(`${[...r.args.map(recurArg), 'x'].join(' ')}`) : 'fail'}
  | (induction x with
    | zero => (try simp only [${unfold}]); ${close(useLemmas(uses, {op: 'and', xs: r.lemmas.map(l => l.holds)}, {...argNames, x: '0', fx: recurCall(lean, r, '0')}, lean))}
    | succ n ih => (try simp only [${unfold}] at ih ⊢); ${close([...step('n'), ...useLemmas(uses, {op: 'and', xs: r.lemmas.map(l => l.holds)}, {...argNames, x: '(n + 1)', fx: recurCall(lean, r, '(n + 1)')}, lean)])})` : ''
  const args = r.args.map(recurArg).join(' ')
  const pairAt = (x: string, y: string) => r.between.map(l => `(${surface({x, fx: recurCall(lean, r, x), y, fy: recurCall(lean, r, y)}).c(l.holds)})`).join(' ∧ ')
  const between = r.between.length ? `${kb?.pre ?? ''}
-- ${r.between.map(l => l.name).join('; ')}, for every x <= y
theorem ${lean}_between_by ${binders} (x d : Nat) : ${pairAt('x', '(x + d)')} := by
  first
  | ${kb ? kb.proof(`${[...r.args.map(recurArg), 'x', 'd'].join(' ')}`) : 'fail'}
  | (induction d with
    | zero => simp only [Nat.add_zero]; (repeat' split) <;> omega
    | succ n ih =>
      rw [show x + (n + 1) = (x + n) + 1 from by omega]
      ${r.lemmas.length ? `have := ${lean}_lemmas ${args} (x + n); ` : ''}(try simp only [${unfold}] at ih this ⊢); ${close(step('(x + n)'))})
theorem ${lean}_between ${binders} (x y : Nat) (h : x ≤ y) : ${pairAt('x', 'y')} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ${lean}_between_by ${args} x d` : ''
  const zero = surface({}).e(r.zero), next = surface({x: 'x', prev: recurCall(lean, r, 'x')}).e(r.next)
  if (!r.args.length) return `def ${lean} : Nat → Nat\n  | 0 => ${zero}\n  | x + 1 => ${next}${lemmas}${between}`
  // The key's function: the arguments unpaired, innermost first.
  const u = (i: number): string => (i === r.args.length ? '(Recur.unpair k)' : `(Recur.unpair ${u(i + 1)}.1)`)
  const keyOf = (x: string) => r.args.map(recurArg).reduce((k, a) => `((${k} + ${a}) * (${k} + ${a}) + ${a})`, x)
  return `def ${self} ${binders} : Nat → Nat
  | 0 => ${zero}
  | x + 1 => ${next}
noncomputable def ${lean} (k : Nat) : Nat := ${self} ${r.args.map((_, i) => `${u(i + 1)}.2`).join(' ')} ${u(1)}.1
theorem ${lean}_key ${binders} (x : Nat) : ${lean} ${keyOf('x')} = ${self} ${args} x := by
  simp only [${lean}, Recur.unpair_pair]${lemmas}${between}`
}
// The pairing the builders read a function of several arguments by, and Lean's inverse of it (choice over the pairs:
// Recur.pair_inj makes it the pair).
export const recurPairing = `theorem Recur.pair_inj {a b c d : Nat} (h : (a + b) * (a + b) + b = (c + d) * (c + d) + d) : a = c ∧ b = d := by
  have sq : ∀ s t : Nat, s < t → s * s + s < t * t := by
    intro s t hst
    have h1 : (s + 1) * (s + 1) ≤ t * t := Nat.mul_le_mul hst hst
    have h2 : (s + 1) * (s + 1) = s * s + s + s + 1 := by simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
    omega
  have hb : b ≤ a + b := Nat.le_add_left b a
  have hd : d ≤ c + d := Nat.le_add_left d c
  rcases Nat.lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
  · have := sq _ _ hlt; omega
  · rw [heq] at h; omega
  · have := sq _ _ hgt; omega
noncomputable def Recur.unpair (k : Nat) : Nat × Nat :=
  Classical.epsilon fun p : Nat × Nat => (p.1 + p.2) * (p.1 + p.2) + p.2 = k
theorem Recur.unpair_pair (a b : Nat) : Recur.unpair ((a + b) * (a + b) + b) = (a, b) := by
  have h := Classical.epsilon_spec (p := fun p : Nat × Nat => (p.1 + p.2) * (p.1 + p.2) + p.2 = (a + b) * (a + b) + b) ⟨(a, b), rfl⟩
  obtain ⟨h1, h2⟩ := Recur.pair_inj h
  exact Prod.ext h1 h2`

// The facts, proven in Lean of the functions' Lean definitions, when every function has one: a run that starts with
// those functions starts where SReach asks the facts to hold. A recurrence's equations unfold its definition (a function
// of several arguments read at its key first); its lemmas and laws between two points are its theorems at the keys.
// With `at`, the facts at one state and maps (a machine's start, its params given as the facts say), each with the
// theorem `cite` names for it, if any, cited first.
type FactsAt = {binders: string, rho: string, mu: string, cite?: (fact: Law) => string | undefined}
function factsProof(id: string, m: Machine, maps: string[], vars: string[], simp: string[] = [], at?: FactsAt): string {
  const fns = Object.entries(m.fns ?? {}), facts = m.facts ?? []
  if (!facts.length || (!at && !fns.length) || fns.some(([, f]) => !f.lean)) return ''
  const recurs = fns.filter(([, f]) => f.recur)
  simp = [...simp, ...recurs.flatMap(([, f]) => (f.recur!.args.length ? [`${f.lean}_rec`, `${f.lean}_key`] : [f.lean!]))]
  // Each recurrence's key lemma rewrites the function at its key before anything else simplifies the key.
  const keyed = recurs.filter(([, f]) => f.recur!.args.length).map(([, f]) => `${f.lean}_key`)
  const hs = fns.map((_, j) => `h${j}`)
  // A fact's proof, its keys named: the first `v`, the further ones `w1`, `w2`...: the recurrence theorem it is an
  // instance of cited first (so that it and the goal simplify alike), then the facts' terms read and omega.
  const tactic = (fact: Law): string => {
    const keys = fact.forall ? [fact.forall, ...(fact.keys ?? [])] : [], arg = keys.map((_, i) => (i === 0 ? 'v' : `w${i}`))
    const owner = recurs.find(([n]) => fact.name.startsWith(`${n}: `)), what = owner ? fact.name.slice(owner[0].length + 2) : ''
    const r = owner?.[1].recur, lean = owner?.[1].lean
    const cite = at?.cite?.(fact) ?? (!r || !keys.length ? undefined : r.lemmas.some(l => l.name === what) ? `${lean}_lemmas ${[...arg.slice(1), arg[0]!].join(' ')}`
      : r.between.some(l => l.name === what) ? `${lean}_between ${[...arg.slice(2), arg[0]!, arg[1]!].join(' ')}` : undefined)
    const intro = keys.length > 1 ? `simp only [holdsOver]; intro ${arg.slice(1).join(' ')}; ` : ''
    return `${intro}simp only [MLaw.Holds]; (try intro v); ${cite ? `have hc := ${cite}; ` : ''}simp only [${['evalC', 'evalE', 'upd', ...hs].join(', ')}]${keyed.length ? `; (try simp only [${keyed.join(', ')}])` : ''}; (try simp [${[...hs, ...simp].join(', ')}]${cite ? ' at hc ⊢' : ''}); all_goals ${cite ? 'first | omega | (simpa using hc)' : 'omega'}`
  }
  const one = facts.filter(f => !f.keys?.length), several = facts.filter(f => f.keys?.length)
  const binders = at ? at.binders : `(ρ : Nat → Nat) (μ : Nat → Nat → Nat) ${fns.map(([n, f], j) => `(h${j} : μ ${maps.indexOf(n)} = ${f.lean})`).join(' ')}`
  const rho = at ? at.rho : 'ρ', mu = at ? at.mu : 'μ', name = at ? 'at' : 'hold'
  // At one state and maps, each function's equation is the maps' own definition.
  const given = at ? fns.map(([n, f], j) => `have h${j} : ${mu} ${maps.indexOf(n)} = (${f.lean}) := rfl\n  `).join('') : ''
  const cases = (fs: Law[], h: string) => `rcases ${h} with ${fs.map(() => 'rfl').join(' | ')}\n${fs.map(f => `  · ${tactic(f)}`).join('\n')}`
  return `
-- The facts hold of the functions' Lean definitions: ${fns.map(([n, f]) => `${n} := ${f.lean}`).join('; ')}.${one.length ? `
theorem ${id}_facts_${name} ${binders} :
    ∀ l ∈ ${id}_machine.facts, l.Holds ${rho} ${mu} := by
  ${given}intro l hl
  simp only [${id}_machine, List.mem_cons, List.not_mem_nil, or_false] at hl
  ${cases(one, 'hl')}` : ''}${several.length ? `
-- The facts about several keys, at every value of their further keys.
theorem ${id}_pfacts_${name} ${binders} :
    ${id}_machine.PFacts ${rho} ${mu} := by
  ${given}intro p hp
  simp only [${id}_machine, List.mem_cons, List.not_mem_nil, or_false] at hp
  ${cases(several, 'hp')}` : ''}`
}

// Machines with a history through Kern.hmachine_sound (History.lean): Lean builds the plain machine (sums as state,
// relations in the assumption) and each relation's record goal; the trees and the instance keys are the kernel's.
// Pruning is left out: its goals are about the runtimes (dropping a record changes no query), the laws and relations
// are proven over the whole history either way, and Lean's HMachine has no pruning; the TypeScript kernel checks them.
// A machine with a history: its laws over histories (History.lean's hmachine_sound), through smachineToLean.
export function hmachineToLean(id: string, m: Machine, laws: Law[], tampers: {what: string, relations: {when: C, holds: C}[], withRecordTrees: boolean}[] = [], corollary?: (ix: (name: string) => number) => string): string {
  return smachineToLean(id, m, laws, {historyTampers: tampers, ...(corollary ? {after: corollary} : {})})
}


// --- the package's entry point: gdp-wired/lean -----------------------------------------------------------------------

// What to export: a machine (a rule's `.machine`, with or without a history) and its laws and step laws, a loop (a loop
// rule's `.loop` with its ranks) and its laws, or a decision's goal (a decision's `.goal`).
export type LeanItem =
  // `lean`: Lean definitions the functions' `lean` terms name (written before the item), and simp lemmas that prove the
  // facts of them (the definitions' equations, say).
  // `ghosts`: the machine's ghost variables (compose.ts's ghost), so the export proves its ghost-free laws of the machine
  // without them; `lean.after`: Lean written after the item (a corollary of its theorems, say).
  | {id: string, machine: Machine, laws: Law[], stepLaws?: StepLaw[], liveness?: Liveness[], ghosts?: string[], lean?: {defs?: string, simp?: string[], after?: (ix: (name: string) => number) => string}}
  // A refinement (compose.ts's), exported with what it means: its relation and the spec's precondition proven of the
  // composite, the spec allowing every request it is sent, and Refine.lean's `refines`.
  | {id: string, refinement: {impl: Machine, spec: Machine, relation: Law[], witness: Record<string, E>, stutter?: C}}
  | {id: string, loop: Loop, rank: E | E[], laws?: Law[]}
  // A fold over trees (a fold rule's `.fold`) and its laws, through Kern.fold_sound.
  | {id: string, fold: Fold, laws: Law[]}
  | {id: string, goal: Goal}
  // A cyclic proof (kernel/cyclic.ts) through Cyclic.lean's cyclic_sound; each tampered one computed to false.
  // `bridge`: the machine and laws the proof was made from (core/cyclic.ts's machineNodes), so that Bridge.lean's
  // cyc_machine_sound gives each law of the machine (`<id>_lawN_holds`, and `<id>.lawN` plainly); each tampered machine's
  // check against the proof computed to false.
  | {id: string, cyclic: Cyclic, tampered?: {what: string, proof: Cyclic}[], after?: (ix: (name: string) => number, mx: (map: string) => number) => string,
    bridge?: CycBridge, recur?: CycRecur, fold?: {fold: Fold, laws: Law[]}, data?: true}

// A Lean file proving each item, to compile against the twin (`leanLibrary`, or `leanProject` for a ready Lake project).
// Each machine's laws come with `<id>_laws` (the twin's theorem) and `<id>.lawN` (the law as a plain Lean statement
// over named variables); step laws with `<id>_stepN_holds` (on the plain machine, `<id>s`, for a machine with a history);
// loops with `<id>_halts`; decisions with `<id>`. A machine with sets has its step laws as `<id>_stepN_holds`.
// Throws if the kernel can't prove one.
//
// `native`: each check by `native_decide` (compiled Lean, several times faster on a large certificate), not by
// `decide +kernel` (Lean's kernel alone). Every such theorem then also rests on an axiom of its own that `#print axioms`
// names (`…_native.native_decide.ax_…`): it trusts Lean's compiler, its runtime and the C compiler. Defaults to off, or
// to GDP_LEAN_NATIVE=1 (the suite's quick runs); a release's proofs stay on Lean's kernel and its core axioms.
// `cyclic`: each machine, loop and fold the cyclic route covers from cyclic certificates (see cycMachineToLean); defaults
// to GDP_CERT=cyclic. `certReport` then says which items went which way.
export function toLean(items: LeanItem[], opts: {title?: string, native?: boolean, cyclic?: boolean} = {}): string {
  const outer = checkBy, outerCerts = certsOn
  const env = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env
  checkBy = (opts.native ?? env?.GDP_LEAN_NATIVE === '1') ? 'native_decide' : 'decide +kernel'
  certsOn = opts.cyclic ?? cyclicCerts()
  certReport.cyclic = []; certReport.usual = []; certReport.translatedSteps = []; cycTexts = 0
  // The proofs found with only the instances their leaves use: the same laws, from fewer hypotheses for Lean to build.
  const wasMinimal = minimal.on
  minimal.on = true
  try { return toLeanWith(items, opts) } finally { checkBy = outer; certsOn = outerCerts; minimal.on = wasMinimal }
}
function toLeanWith(items: LeanItem[], opts: {title?: string}): string {
  const ident = (id: string) => { const s = id.replace(/[^A-Za-z0-9_]/g, '_'); return /^[A-Za-z]/.test(s) ? s : `x_${s}` }
  const parts: string[] = [], theorems: string[] = []
  let goals = 0
  // Each recurrence defined once, before the first item that reads it.
  const recurs = new Map<string, string>()
  const recurDefs = (m: Machine): string => Object.entries(m.fns ?? {}).filter(([, f]) => f.recur).map(([n, f]) => {
    // The functions it reads are the machine's <n>.<use>, defined before it (flatFns puts them first).
    const uses = Object.fromEntries(Object.entries(f.recur!.uses).map(([u, d]) => { const g = m.fns?.[`${n}.${u}`]; return [u, {...d, ...(g?.recur ? {recur: g.recur} : {})}] }))
    const text = recurToLean(f.lean!, f.recur!, uses), had = recurs.get(f.lean!)
    if (had !== undefined) { if (had !== text) throw new Error(`${f.lean}: two recurrences of one name`); return '' }
    const pairing = f.recur!.args.length && !recurs.has('') ? (recurs.set('', recurPairing), `${recurPairing}\n`) : ''
    recurs.set(f.lean!, text)
    if (f.recur!.lemmas.length) theorems.push(`${f.lean}_lemmas`)
    if (f.recur!.between.length) theorems.push(`${f.lean}_between`)
    return `${pairing}${text}\n`
  }).join('')
  for (let item of items) {
    const id = ident(item.id)
    if ('machine' in item) {
      const m = item.machine
      // Laws with some key go in as the prover proved them: with its witness in place (the stronger law).
      const someKey = (c: C) => JSON.stringify(c).includes('"op":"all"')
      if ([...item.laws.map(l => l.holds), ...(item.stepLaws ?? []).map(sl => sl.then)].some(someKey)) {
        const r = proveStepLaws(m, item.laws, item.stepLaws ?? [])
        if (!r.proven) throw new Error(`${item.id}: not proven (${r.failed?.stuck ?? ''})`)
        item = {...item, laws: r.laws ?? item.laws, ...(item.stepLaws ? {stepLaws: r.stepLaws ?? item.stepLaws} : {})}
      }
      // One twin: every machine goes to Lean as a machine with sets (one with none, if it has none): its laws, step laws,
      // liveness and ghosts in one export; a machine with a history as its plain machine, and its laws over histories.
      // With cyclic certificates, from one cyclic proof where the cyclic route covers it.
      const mopts = {stepLaws: item.stepLaws, ...(item.liveness?.length ? {liveness: item.liveness} : {}),
        ...(item.ghosts?.length ? {ghosts: item.ghosts} : {}), ...(item.lean?.simp ? {simp: item.lean.simp} : {}), ...(item.lean?.after ? {after: item.lean.after} : {})}
      const defs = `${recurDefs(m)}${item.lean?.defs ? `${item.lean.defs}\n` : ''}`
      const cyc = certsOn ? cycMachineToLean(id, m, item.laws, mopts) : undefined
      if (cyc && 'text' in cyc) certReport.cyclic.push(item.id); else if (cyc) certReport.usual.push({id: item.id, why: cyc.why})
      parts.push(`-- ${item.id}\n${defs}${cyc && 'text' in cyc ? cyc.text : smachineToLean(id, m, item.laws, mopts)}`)
      theorems.push(`${id}_laws`, ...(m.history ? [`${id}_hlaws`] : []), ...(item.stepLaws ?? []).map((_, j) => `${id}_step${j}_holds`), ...(item.liveness ?? []).map((_, j) => `${id}_live${j}_holds`))
      if (item.lean?.after) theorems.push(...[...item.lean.after(() => 0).matchAll(/^theorem (\S+)/gm)].map(x2 => x2[1]!))
    } else if ('refinement' in item) {
      const {impl, spec, relation, witness} = item.refinement
      const stutter: C = item.refinement.stutter ?? {op: '<', a: n(0), b: n(0)}
      const R = refinement(impl, spec, {relation, witness, stutter}), S = refinementSides(impl, spec)
      const laws: Law[] = [...relation, {name: `${spec.name}'s precondition`, holds: spec.pre ?? atMost(n(0), n(0))}]
      const sl: StepLaw = R.stepLaws[0] ?? {name: `${spec.name} allows the request it is sent`, then: {op: 'or', xs: [stutter, atMost(n(0), n(0))]}}
      const refined = {impl: S.impl, spec: S.spec, wit: witness, stutter, specPre: relation.length}, free = spec.inputs.map(i => `b_${i}`)
      // With cyclic certificates: the composite's laws and its step law (Lean's SRefined.allowed, built here as Lean builds
      // it) from one cyclic proof, through BridgeRules.lean's srefines_of_holds.
      const cyc = certsOn ? cycMachineToLean(id, R.machine, laws, {free, refined: {...refined, step: sl}}) : undefined
      if (cyc && 'text' in cyc) certReport.cyclic.push(item.id); else if (cyc) certReport.usual.push({id: item.id, why: cyc.why})
      parts.push(`-- ${item.id}\n${cyc && 'text' in cyc ? cyc.text : smachineToLean(id, R.machine, laws, {stepLaws: [sl], free, refined})}`)
      theorems.push(`${id}_laws`, `${id}_refines`)
    } else if ('loop' in item) {
      loopObligations(item.loop, item.laws ?? [], item.rank)
      const cyc = certsOn ? cycMachineToLean(id, loopMachine(item.loop), item.laws ?? [], {liveness: [loopLiveness(item.loop, item.rank)], loop: {loop: item.loop}}) : undefined
      if (cyc && 'text' in cyc) certReport.cyclic.push(item.id); else if (cyc) certReport.usual.push({id: item.id, why: cyc.why})
      parts.push(`-- ${item.id}\n${cyc && 'text' in cyc ? cyc.text : loopToLean(id, item.loop, item.laws ?? [], item.rank)}`)
      theorems.push(`${id}_halts`)
    } else if ('cyclic' in item) {
      parts.push(`-- ${item.id}\n${cyclicToLean(id, item.cyclic, item.tampered ?? [], item.after, item.bridge, item.recur, item.fold)}`)
      theorems.push(`${id}_sound`, ...(item.bridge?.laws ?? item.fold?.laws ?? []).map((_, j) => `${id}_law${j}_holds`), ...(item.recur ? [`${id}_values`] : []),
        ...(item.recur ? [...item.recur.lemmas.map((_, j) => `${id}_lemma${j}`), ...item.recur.between.map((_, j) => `${id}_between${j}`)] : []),
        // A datatype law's theorem is in a namespace of the item's (its datatypes and functions are named as declared).
        ...(item.after ? (ts => (item.data ? ts.slice(-1).map(t => `${id}.${t}`) : ts))([...item.after(() => 0, () => 0).matchAll(/^theorem (\S+)/gm)].map(x2 => x2[1]!)) : []))
    } else if ('fold' in item) {
      const cyc = certsOn ? cycFoldToLean(id, item.fold, item.laws) : undefined
      if (cyc && 'text' in cyc) certReport.cyclic.push(item.id); else if (cyc) certReport.usual.push({id: item.id, why: cyc.why})
      parts.push(`-- ${item.id}\n${cyc && 'text' in cyc ? cyc.text : foldToLean(id, item.fold, item.laws)}`)
      theorems.push(`${id}_laws`)
    } else {
      // goalToLean names its theorem t<i>; here it is the item's id.
      const n = goals++
      parts.push(goalToLean({name: item.id, goal: item.goal, tree: grown(item.goal)}, n, false).replace(new RegExp(`\\bt${n}(_goal|_tree)?\\b`, 'g'), (_, suffix: string | undefined) => `${id}${suffix ?? ''}`))
      theorems.push(id)
    }
  }
  // The file the items need: Live.lean for a liveness or a loop, Sets.lean (which imports Steps.lean) for any machine.
  return `import History
${cycTexts ? 'import BridgeRules\n' : ''}${items.some(item => 'cyclic' in item) ? (items.some(item => 'cyclic' in item && (item.bridge || item.recur || item.fold)) ? 'import Bridge\n' : 'import Cyclic\n') : ''}${items.some(item => 'cyclic' in item && item.data) ? 'import Data\n' : ''}import ${items.some(item => 'refinement' in item) ? 'Refine' : items.some(item => 'machine' in item && item.ghosts?.length) ? 'Ghost' : items.some(item => ('machine' in item && item.liveness?.length) || 'loop' in item) ? 'Live' : items.some(item => 'machine' in item) ? 'Sets' : 'Steps'}
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ${opts.title ?? 'Laws proven by gdp-wired'}: the kernel's proofs, checked by Lean against the twin (Kernel.lean and the
files it imports), whose soundness theorems are proven there. -/

${parts.join('\n\n')}

${theorems.map(t => `#print axioms ${t}`).join('\n')}
`
}

// A Lake project that builds the twin and the file: `lake build` in its folder checks every proof.
export function leanProject(file: string, opts: {name?: string} = {}): Record<string, string> {
  const name = opts.name ?? 'Proofs'
  const modules = [...Object.keys(leanLibrary).map(f => f.replace(/\.lean$/, '')), name]
  return {
    ...leanLibrary,
    [`${name}.lean`]: file,
    'lean-toolchain': 'leanprover/lean4:v4.34.0\n',
    'lakefile.lean': `import Lake
open Lake DSL

package ${name.toLowerCase()}

@[default_target]
lean_lib ${name} where
  roots := #[${modules.map(mod => `\`${mod}`).join(', ')}]
`,
  }
}

// A cyclic proof through Kern.cyclic_sound: the facts and the nodes, each goal's table and tree (Lean builds the goals
// from the nodes), one theorem for every node; each tampered proof's check computed to false. `after` writes Lean
// after it (a corollary in plain terms), given the variables' and maps' numbers.
export type CycBridge = {machine: Machine, laws: Law[], tampered?: {what: string, machine: Machine}[]}
// A recurrence the proof was made from (core/cyclic.ts's recurNodes, no function read): Bridge.lean's cyc_recur_sound
// gives each node of the recurrence's values, and each lemma and law between plainly of its Lean definition.
export type CycRecur = {name: string, args: string[], zero: E, next: E, lemmas: {name: string, holds: C}[], between: {name: string, holds: C}[]}
export function cyclicToLean(id: string, p: Cyclic, tampered: {what: string, proof: Cyclic}[] = [], after?: (ix: (name: string) => number, mx: (map: string) => number) => string,
    bridge?: CycBridge, recur?: CycRecur, fold?: {fold: Fold, laws: Law[]}): string {
  const all = [p, ...tampered.map(t => t.proof)]
  const v = (name: string): E => ({op: 'var', name})
  const fnames = fold ? Object.keys(fold.fold.leaf) : []
  const {vars, maps} = cycScope(all, bridge, [...(recur ? [recur.zero, recur.next, v('x'), v('prev'), v('k$'), ...recur.args.map(v)] : []),
    ...(fold ? [...fold.fold.params, ...fold.fold.inputs, ...fnames, ...fnames.map(x => `l_${x}`), ...fnames.map(x => `r_${x}`), 'n$', 'N$'].map(v) : []),
    ...(fold ? [...Object.values(fold.fold.leaf), ...Object.values(fold.fold.node), ...fold.laws.map((l): E => ({op: 'if', c: l.holds, then: v('n$'), else: v('n$')}))] : []),
    ...(fold ? ['Kind', 'Left', 'Right', ...fnames, ...fold.fold.inputs].map((x): E => ({op: 'get', map: `${x}@`, key: v('n$')})) : [])])
  const {e, c} = leanTerms(vars, maps, id)
  const ix = (name: string) => vars.indexOf(name), mx = (map: string) => maps.indexOf(map)
  return `-- ${p.nodes.map(n => n.name).join('; ')}  (variables ${vars.map((name, j) => `${j} ${name}`).join(', ')}; maps ${maps.map((name, j) => `${j} ${name}`).join(', ')})
${cycProofText(id, p, tampered, vars, maps)}${bridge ? `\n${cycBridgeLean(id, p, bridge, vars, maps, {e, c})}` : ''}${recur ? `\n${cycRecurLean(id, p, recur, vars, maps, {e, c})}` : ''}${fold ? `\n${cycFoldLean(id, fold.fold, fold.laws, vars, maps, {e, c})}` : ''}${after ? `\n${after(ix, mx)}` : ''}`
}
// A cyclic proof as Lean: its facts and nodes (each goal's table and tree, Lean building the goals from the nodes), each
// node's membership, the check and cyclic_sound's theorem; each tampered proof's check computed to false.
function cycProofText(id: string, p: Cyclic, tampered: {what: string, proof: Cyclic}[], vars: string[], maps: string[]): string {
  const {e, c} = leanTerms(vars, maps, id)
  const ix = (name: string) => vars.indexOf(name)
  const facts = list(p.facts.map(f => `⟨${list(f.keys.map(key => String(ix(key))))}, ${c(f.holds)}⟩`))
  // A tampered proof keeps the proof's tables and trees (made for the proof's own goals) under its changed nodes.
  const enc = (g: Goal, tree: Tree) => { const x = encode({name: `${id}: ${g.name}`, goal: g, tree}, false, true, vars, maps); return `(${x.tab}, ${x.tree})` }
  const nodeLits = (q: Cyclic) => q.nodes.map((n, i) => {
    const o = p.nodes[i]!
    const uses = n.uses.map((u, j) => {
      const ou = o.uses[j]!, om = p.nodes[ou.node]!
      return `⟨${u.node}, ${list(Object.entries(u.subst).map(([name, t]) => `(${ix(name)}, ${e(t)})`))}, ${c(u.guard)},\n  ${list(om.hyps.map((h, k2) => enc(premiseGoal(p.facts, o, ou, h, k2), ou.premises[k2]!)))},\n  ${enc(descentGoal(p.facts, o, ou, om), ou.descent)}⟩`
    })
    return {hyps: list(n.hyps.map(c)), concl: c(n.concl), rest: `${list(n.rank.map(e))}, ${list(n.insts.map(t => `(${t.fact}, ${list(t.at.map(e))})`))},\n  ${list(uses)},\n  ${enc(mainGoal(p.facts, p.nodes, o), o.main)}`}
  })
  const nodes = (q: Cyclic) => list(nodeLits(q).map(x => `⟨${x.hyps}, ${x.concl}, ${x.rest}⟩`))
  return `def ${id}_facts : List Fact := ${facts}
${nodeLits(p).map((x, i) => `def ${id}_hyps${i} : List C := ${x.hyps}
def ${id}_concl${i} : C := ${x.concl}
def ${id}_node${i} : CNode := ⟨${id}_hyps${i}, ${id}_concl${i}, ${x.rest}⟩
theorem ${id}_node${i}_hyps : ${id}_node${i}.hyps = ${id}_hyps${i} := rfl
theorem ${id}_node${i}_concl : ${id}_node${i}.concl = ${id}_concl${i} := rfl`).join('\n')}
def ${id}_nodes : List CNode := ${list(p.nodes.map((_, i) => `${id}_node${i}`))}
${p.nodes.map((_, i) => `theorem ${id}_node${i}_mem : ${id}_node${i} ∈ ${id}_nodes := by simp only [${id}_nodes, List.mem_cons, true_or, or_true]`).join('\n')}
theorem ${id}_check : checkCyclic ${id}_facts ${id}_nodes = true := by ${checkBy}
theorem ${id}_sound : ∀ (maps : Nat → Nat → Nat) env, FactsHold ${id}_facts env maps → ∀ n ∈ ${id}_nodes, (∀ c ∈ n.hyps, evalC env maps c = true) → evalC env maps n.concl = true :=
  cyclic_sound ${id}_facts ${id}_nodes ${id}_check
${tampered.map((t, j) => `-- TAMPERED: ${t.what}. Lean computes the check to false.
def ${id}_tampered${j} : List CNode := ${nodes(t.proof)}
example : checkCyclic ${id}_facts ${id}_tampered${j} = false := by ${checkBy}`).join('\n')}`
}

// The variables and maps a cyclic proof names. With a machine it was made from, the machine's own names too (core/cyclic.ts's
// encoding adds u$, k$, T$, O$, t$ and a map x@ over time for each state variable, input and map), for its SMachine and
// the encoding Bridge.lean checks the proof against.
type CycShape = {facts: {keys: string[], holds: C}[], nodes: {hyps: C[], concl: C, rank: E[], insts: unknown[], uses: {subst: Record<string, E>, guard: C}[]}[]}
function cycScope(all: CycShape[], bridge?: CycBridge, extra: E[] = []): {vars: string[], maps: string[]} {
  const names = (t: unknown) => [...JSON.stringify(t).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!)
  const ms = bridge ? [bridge.machine, ...(bridge.tampered ?? []).map(t => t.machine)] : []
  const keysOf = (l: Law) => [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])]
  const traced = (m: Machine) => [...Object.keys(m.state), ...m.inputs], tracedMaps = (m: Machine) => [...Object.keys(m.maps ?? {}), ...(m.inputMaps ?? [])]
  const machineVars = ms.flatMap(m => [...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.step.flags ?? {}).map(f => `?${f}`),
    ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : [])), ...(m.facts ?? []).flatMap(keysOf), ...names([m.state, m.step, m.pre, m.assume, m.facts])])
  const vars = [...new Set([...all.flatMap(q => [...q.facts.flatMap(f => [...f.keys, ...names(f.holds)]), ...q.nodes.flatMap(n => [...names([n.hyps, n.concl, n.rank, n.insts]), ...n.uses.flatMap(u => [...Object.keys(u.subst), ...names([u.subst, u.guard])])])]),
    ...machineVars, ...(bridge ? [...bridge.laws.flatMap(l => [...keysOf(l), ...names(l.holds)]), 'u$', 'k$', 'T$', 'O$', 't$'] : []), ...names(extra)])]
  const maps = [...new Set([...[...JSON.stringify([all, ms, bridge?.laws ?? []]).matchAll(/"op":"get","map":"([^"]+)"/g)].map(m => m[1]!),
    ...ms.flatMap(m => [...tracedMaps(m), ...Object.keys(m.fns ?? {}), ...traced(m).map(x => `${x}@`), ...tracedMaps(m).map(x => `${x}@`)])])]
  return {vars, maps}
}

// Bridge.lean's cycMOk alone, part by part, for each law of a machine (the sweep research/cyclic/bridge.ts runs over the
// examples): the facts and nodes machineNodes makes, each node with no proof (cycMOk reads only its hypotheses and
// conclusion), against the machine's encoding. Each part an example, named in a comment before it.
export function cycEncodingLean(id: string, facts: {name: string, keys: string[], holds: C}[], nodes: {name: string, hyps: C[], concl: C}[], b: CycBridge): string {
  const shape: CycShape = {facts, nodes: nodes.map(n => ({hyps: n.hyps, concl: n.concl, rank: [], insts: [], uses: []}))}
  const {vars, maps} = cycScope([shape], b)
  const t = leanTerms(vars, maps, id)
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = maps.indexOf(name); if (j < 0) throw new Error(`${id}: no map for ${name}`); return j }
  const m = b.machine, keysOf = (l: Law) => list([...(l.forall ? [l.forall] : []), ...(l.keys ?? [])].map(k2 => String(ix(k2))))
  const by = checkBy
  return `-- ${id}: ${m.name}
def ${id}_machine : SMachine := ${machineLit(m, t, ix, mx)}
def ${id}_enc : CycEnc := ⟨${['u$', 'k$', 'T$', 'O$', 't$'].map(ix).join(', ')},
  ${list([...Object.keys(m.state), ...m.inputs].map(x => `(${ix(x)}, ${mx(`${x}@`)})`))},
  ${list([...Object.keys(m.maps ?? {}), ...(m.inputMaps ?? [])].map(x => `(${mx(x)}, ${mx(`${x}@`)})`))}⟩
${facts.map((f, i) => `-- CHECK ${id} fact ${i}: ${f.name}
example : (natC (${t.c(f.holds)}) || (cycCanon ${id}_machine ${id}_enc).any (factBeq ⟨${list(f.keys.map(k2 => String(ix(k2))))}, ${t.c(f.holds)}⟩)) = true := by ${by}`).join('\n')}
${b.laws.map((l, j) => `-- CHECK ${id} law ${j}: shape: ${l.name}
example : cycShapeOk ${id}_machine ${id}_enc ${keysOf(l)} = true := by ${by}
-- CHECK ${id} law ${j}: terms: ${l.name}
example : cycTermsOk ${id}_machine ${id}_enc ${keysOf(l)} = true := by ${by}
-- CHECK ${id} law ${j}: law: ${l.name}
example : cycLawOk ${id}_machine ${id}_enc (${t.c(l.holds)}) = true := by ${by}
-- CHECK ${id} law ${j}: node: ${l.name}
example : cycNodeOk ${id}_machine ${id}_enc (${t.c(l.holds)}) ⟨${list(nodes[j]!.hyps.map(t.c))}, ${t.c(nodes[j]!.concl)}, [], [], [], ([], .leaf [] [] [] [])⟩ = true := by ${by}`).join('\n')}`
}

// Bridge.lean's recOk and foldOk alone, for the sweep (research/cyclic/bridge.ts): recurNodes' and foldNodes' facts (and
// a fold's nodes, with no proof: foldOk reads only their hypotheses and conclusions) against the recurrence's equations
// and the fold's table. Each an example, named in a comment before it.
export function cycRecurCheckLean(id: string, facts: {name: string, keys: string[], holds: C}[], r: CycRecur): string {
  const v = (name: string): E => ({op: 'var', name})
  const {vars, maps} = cycScope([{facts, nodes: []}], undefined, [r.zero, r.next, v('x'), v('prev'), v('k$'), ...r.args.map(v), {op: 'get', map: `${r.name}$`, key: v('x')}])
  const t = leanTerms(vars, maps, id), ix = (n2: string) => vars.indexOf(n2), mx = (n2: string) => maps.indexOf(n2)
  return `-- CHECK ${id} recurrence: ${r.name}
example : recOk ⟨${mx(`${r.name}$`)}, ${ix('x')}, ${ix('prev')}, ${ix('k$')}⟩ (${t.e(r.zero)}) (${t.e(r.next)}) []
    ${list(facts.map(f => `⟨${list(f.keys.map(k2 => String(ix(k2))))}, ${t.c(f.holds)}⟩`))} = true := by ${checkBy}`
}
export function cycFoldCheckLean(id: string, facts: {name: string, keys: string[], holds: C}[], nodes: {name: string, hyps: C[], concl: C}[], f: Fold, laws: Law[]): string {
  const v = (name: string): E => ({op: 'var', name}), st = Object.keys(f.leaf)
  const shape: CycShape = {facts, nodes: nodes.map(n => ({hyps: n.hyps, concl: n.concl, rank: [], insts: [], uses: []}))}
  const {vars, maps} = cycScope([shape], undefined, [...[...f.params, ...f.inputs, ...st, ...st.map(x => `l_${x}`), ...st.map(x => `r_${x}`), 'n$', 'N$'].map(v),
    ...Object.values(f.leaf), ...Object.values(f.node), ...['Kind', 'Left', 'Right', ...st, ...f.inputs].map((x): E => ({op: 'get', map: `${x}@`, key: v('n$')}))])
  const t = leanTerms(vars, maps, id)
  return `${cycFoldLean(id, f, [], vars, maps, t)}
def ${id}_facts : List Fact := ${list(facts.map(g => `⟨${list(g.keys.map(k2 => String(vars.indexOf(k2))))}, ${t.c(g.holds)}⟩`))}
${laws.map((l, j) => `-- CHECK ${id} fold law ${j}: ${l.name}
example : foldOk ${id}_fold ${id}_fenc ${id}_facts (${t.c(l.holds)}) ⟨${list(nodes[j]!.hyps.map(t.c))}, ${t.c(nodes[j]!.concl)}, [], [], [], ([], .leaf [] [] [] [])⟩ = true := by ${checkBy}`).join('\n')}`
}

// Bridge.lean's cyc_fold_sound for each law of a cyclic proof made by foldNodes: the fold as Kernel.lean's Fold, the
// table (its added variables and maps), each law's check and its theorem over trees, as fold_sound states the usual one.
function cycFoldLean(id: string, f: Fold, laws: Law[], vars: string[], maps: string[], t: {e: (x: E) => string, c: (x: C) => string}): string {
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = maps.indexOf(name); if (j < 0) throw new Error(`${id}: no map for ${name}`); return j }
  const st = Object.keys(f.leaf)
  return `def ${id}_fold : Fold := ⟨${list(f.inputs.map(name => String(ix(name))))},
  ${list(st.map(n2 => `(${ix(n2)}, ${ix(`l_${n2}`)}, ${ix(`r_${n2}`)})`))},
  ${list(Object.entries(f.leaf).map(([name, e2]) => `(${ix(name)}, ${t.e(e2)})`))},
  ${list(Object.entries(f.node).map(([name, e2]) => `(${ix(name)}, ${t.e(e2)})`))},
  ${f.pre ? t.c(f.pre) : TRUE},
  ${f.assume ? t.c(f.assume) : TRUE}⟩
def ${id}_fenc : FoldEnc := ⟨${ix('n$')}, ${ix('N$')}, ${mx('Kind@')}, ${mx('Left@')}, ${mx('Right@')}, ${list([...st, ...f.inputs].map(x => `(${ix(x)}, ${mx(`${x}@`)})`))}⟩
${laws.map((l, j) => `-- ${l.name}
def ${id}_law${j} : C := ${t.c(l.holds)}
theorem ${id}_law${j}_ok : foldOk ${id}_fold ${id}_fenc ${id}_facts ${id}_law${j} ${id}_node${j} = true := by ${checkBy}
theorem ${id}_law${j}_holds : ∀ (maps : Nat → Nat → Nat) ρ, evalC ρ maps ${id}_fold.pre = true → ∀ t, Allowed ${id}_fold ρ maps t →
    evalC (foldT ${id}_fold ρ maps t) maps ${id}_law${j} = true :=
  cyc_fold_sound ${id}_fold ${id}_fenc ${id}_facts ${id}_nodes ${id}_check ${id}_law${j} ${id}_node${j} ${id}_node${j}_mem ${id}_law${j}_ok`).join('\n')}`
}

// Bridge.lean's cyc_recur_sound for a cyclic proof made by recurNodes: the recurrence's equations checked against the
// proof's facts, the nodes of its values (recF), its Lean definition (as recurToLean writes it) shown to be those values,
// and each lemma and law between two points plainly of the definition.
function cycRecurLean(id: string, p: Cyclic, r: CycRecur, vars: string[], maps: string[], t: {e: (x: E) => string, c: (x: C) => string}): string {
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = maps.indexOf(name); if (j < 0) throw new Error(`${id}: no map for ${name}`); return j }
  const fn = `${id}_fn`, args = r.args.map(recurArg), binders = args.map(a => `(${a} : Nat)`).join(' ')
  const call = (x: string) => `(${[fn, ...args, x].join(' ')})`
  const surface = (names: Record<string, string>) => leanSurface({...Object.fromEntries(r.args.map((a, i) => [a, args[i]!])), ...names}, id)
  const renc = `⟨${mx(`${r.name}$`)}, ${ix('x')}, ${ix('prev')}, ${ix('k$')}⟩`
  const recF = `recF ${id}_zero ${id}_next ${ix('x')} ${ix('prev')}`
  const envAt = (pts: [string, string][]) => `(fun i => ${[...pts, ...r.args.map((a, i): [string, string] => [a, args[i]!])].map(([v, val]) => `if i = ${ix(v)} then ${val} else `).join('')}0)`
  const node = (j: number) => `${id}_node${j}`
  const n = r.lemmas.length
  return `def ${id}_renc : RecEnc := ${renc}
def ${id}_zero : E := ${t.e(r.zero)}
def ${id}_next : E := ${t.e(r.next)}
theorem ${id}_rok : recOk ${id}_renc ${id}_zero ${id}_next [] ${id}_facts = true := by ${checkBy}
theorem ${id}_values : ∀ maps env, ∀ n ∈ ${id}_nodes, (∀ c ∈ n.hyps, evalC env (withMap maps ${mx(`${r.name}$`)} (${recF} env maps)) c = true) →
    evalC env (withMap maps ${mx(`${r.name}$`)} (${recF} env maps)) n.concl = true :=
  fun maps env => cyc_recur_sound ${id}_renc ${id}_zero ${id}_next [] ${id}_facts ${id}_nodes ${id}_check ${id}_rok maps env (by intro f hf; simp at hf)
-- ${r.name} as Lean defines it (recurToLean's recursion), and the same as the values the proof is about.
def ${fn} ${binders} : Nat → Nat
  | 0 => ${surface({}).e(r.zero)}
  | x + 1 => ${surface({x: 'x', prev: call('x')}).e(r.next)}
theorem ${fn}_eq (maps : Nat → Nat → Nat) (env : Nat → Nat) : ∀ n, ${recF} env maps n = ${[fn, ...r.args.map(a => `(env ${ix(a)})`)].join(' ')} n := by
  intro n
  induction n with
  | zero => simp [recF, ${id}_zero, ${fn}, evalE]
  | succ n ih => simp only [recF]; rw [ih]; simp [${id}_next, ${fn}, evalE, upd]
${r.lemmas.map((l, j) => `/-- ${r.name}: ${l.name} -/
theorem ${id}_lemma${j} ${binders} (x : Nat) : ${surface({x: 'x', fx: call('x')}).c(l.holds)} := by
  have h := ${id}_values (fun _ _ => 0) ${envAt([['x', 'x']])} _ ${node(j)}_mem (by rw [${node(j)}_hyps]; simp [${id}_hyps${j}])
  rw [${node(j)}_concl] at h
  simpa [${id}_concl${j}, evalC, evalE, withMap, ${fn}_eq] using h`).join('\n')}
${r.between.map((b, j) => `/-- ${r.name}: ${b.name}, for every x ≤ y -/
theorem ${id}_between${j} ${binders} (x y : Nat) (hxy : x ≤ y) : ${surface({x: 'x', fx: call('x'), y: 'y', fy: call('y')}).c(b.holds)} := by
  have h := ${id}_values (fun _ _ => 0) ${envAt([['x', 'x'], ['y', 'y']])} _ ${node(n + j)}_mem (by rw [${node(n + j)}_hyps]; simp [${id}_hyps${n + j}])
  rw [${node(n + j)}_concl] at h
  simp [${id}_concl${n + j}, evalC, evalE, withMap, ${fn}_eq] at h
  first | exact h hxy | omega | exact h.resolve_left (by omega)`).join('\n')}`
}

// Bridge.lean's cyc_machine_sound for each law of a cyclic proof made by machineNodes: the machine as Sets.lean's
// SMachine, the encoding (its added variables and maps over time), each law's check and theorem, and the laws plainly.
function cycBridgeLean(id: string, p: Cyclic, b: CycBridge, vars: string[], maps: string[], t: {e: (x: E) => string, c: (x: C) => string}): string {
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = maps.indexOf(name); if (j < 0) throw new Error(`${id}: no map for ${name}`); return j }
  if (b.laws.length > p.nodes.length) throw new Error(`${id}: more laws than nodes`)
  const keysOf = (l: Law) => [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])]
  const enc = (m: Machine) => `⟨${['u$', 'k$', 'T$', 'O$', 't$'].map(ix).join(', ')},
  ${list([...Object.keys(m.state), ...m.inputs].map(x => `(${ix(x)}, ${mx(`${x}@`)})`))},
  ${list([...Object.keys(m.maps ?? {}), ...(m.inputMaps ?? [])].map(x => `(${mx(x)}, ${mx(`${x}@`)})`))}⟩`
  const keysL = (l: Law) => list(keysOf(l).map(k2 => String(ix(k2))))
  return `def ${id}_machine : SMachine := ${machineLit(b.machine, t, ix, mx)}
def ${id}_enc : CycEnc := ${enc(b.machine)}
${b.laws.map((l, j) => `-- ${l.name}
def ${id}_law${j} : C := ${t.c(l.holds)}
def ${id}_l${j} : MLaw := ⟨${id}_law${j}, ${l.forall ? `some ${ix(l.forall)}` : 'none'}⟩
theorem ${id}_law${j}_ok : cycMOk ${id}_machine ${id}_enc ${id}_facts ${id}_law${j} ${keysL(l)} ${id}_node${j} = true := by ${checkBy}
theorem ${id}_law${j}_holds : ∀ ρ M, SReach ${id}_machine ρ M → ∀ ρ' : Nat → Nat, (∀ i, i ∉ ${keysL(l)} → ρ' i = ρ i) → evalC ρ' M ${id}_law${j} = true :=
  cyc_machine_sound ${id}_machine ${id}_enc ${id}_facts ${id}_nodes ${id}_check ${id}_law${j} ${keysL(l)} ${id}_node${j} ${id}_node${j}_mem ${id}_law${j}_ok`).join('\n')}
${(b.tampered ?? []).map((tm, j) => `-- TAMPERED: ${tm.what}. Lean computes the check against the proof to false.
def ${id}_tamperedm${j} : SMachine := ${machineLit(tm.machine, t, ix, mx)}
example : cycMOk ${id}_tamperedm${j} ${id}_enc ${id}_facts ${id}_law0 ${keysL(b.laws[0]!)} ${id}_node0 = false := by ${checkBy}`).join('\n')}
${readable(id, b.laws, vars, maps, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: `SReach ${id}_machine ρ μ`, call: '',
  have: j => `have hl : holdsOver ${id}_l${j} μ ${list((b.laws[j]!.keys ?? []).map(k2 => String(ix(k2))))} ρ := cyc_machine_holds (${id}_law${j}_holds ρ μ h)`})}`
}
