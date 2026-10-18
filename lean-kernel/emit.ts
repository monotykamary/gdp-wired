// Kernel proofs as Lean: the machine, its laws and the kernel's trees as Lean.Kern data, each law a theorem by the twin's
// soundness theorems (Kernel.lean, Progress.lean, StepLaw.lean, Steps.lean, History.lean, Sets.lean) with `decide +kernel`. The
// emitter is untrusted: it names columns, orders rows and claims cell equalities; Lean checks every claim. Pure string
// building, so it ships in the package (`gdp-wired/lean`); export-kernel.ts is the repo's script around it.
import type {C, E, Law, Machine} from '../core/machine.ts'
import {atMost, n, not, pointWrite} from '../core/machine.ts'
import {type Lin, type Step, add, k, scale, sub} from '../core/solver.ts'
import {type Fold, type Goal, type Instances, type Liveness, type Loop, type Path, type StepLaw, type Tree, canon, columnTerm, stateName, termColumn, historyMachine, foldObligations, leafConstraints, linear, livenessHelpful, livenessParts, livenessRanks, loopObligations, trueC, obligations, progressObligations, stepLawObligations, substC, withProducts} from '../kernel/kernel.ts'
import {grow, proveBuilt, proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {refinement, refinementSides} from '../core/compose.ts'
import {leanTerms} from './lean-terms.ts'
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

export function leaves(t: Tree, path: Path, visit: (t: Tree & {leaf: Step[], products?: [number, number][]}, path: Path) => void) {
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
  const addCell = (name: string) => { if (cells.has(name)) return; cells.add(name); for (const key of Object.keys(cellKey(name))) if (key.includes('[')) addCell(key); else if (key.startsWith('⟦')) terms.add(key) }
  // Monomials: every one a leaf's rows or products use, or that a product term has under the leaf's path.
  const monos = new Set<string>()
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
    for (const r of withProducts(leafConstraints(goal, path), leaf.products ?? [])) for (const key of Object.keys(r.lin)) {
      if (key.includes('[')) addCell(key)
      else if (key.startsWith('⟦')) terms.add(key)
      else if (key.includes('*')) monos.add(key)
    }
    for (const h of goal.hyps) for (const e of subterms(h)) if (e.op === 'prod') for (const key of Object.keys(linear(e, path) ?? {})) if (key.includes('*')) monos.add(key)
  })
  const depth = (name: string) => name.split('[').length
  // Term columns (open choices, each standing for its term's value) before the cells, whose keys may read them.
  const cols = [...vars, ...[...monos].sort((a, b) => a.split('*').length - b.split('*').length), ...[...terms].sort((a, b) => Number(a.slice(1, -1)) - Number(b.slice(1, -1))), ...[...cells].sort((a, b) => depth(a) - depth(b))]
  const col = new Map(cols.map((name, j) => [name, j]))
  const maps = globalMaps ?? [...new Set([...[...cells].map(cellMap), ...goal.hyps.flatMap(h => [...JSON.stringify(h).matchAll(/"op":"get","map":"([^"]+)"/g)].map(m => m[1]!))])]
  const dense = (lin: Lin) => {
    const coefs = new Array(cols.length).fill(0)
    for (const [key, c] of Object.entries(lin)) if (key !== '1') { const j = col.get(key); if (j === undefined) throw new Error(`${ex.name}: no column for ${key}`); coefs[j] = c }
    while (coefs.length && coefs.at(-1) === 0) coefs.pop()
    return coefs as number[]
  }
  const row = (lin: Lin) => `⟨${list(dense(lin).map(int))}, ${int(lin['1'] ?? 0)}⟩`
  const {e, c} = leanTerms(vars, maps, ex.name)
  const tab = cols.map(name => (name.includes('[') ? `.cell ${maps.indexOf(cellMap(name))} ${row(cellKey(name))}`
    : name.startsWith('⟦') ? `.term (${e(columnTerm(name)!)})`
    : name.includes('*') ? `.mono ${list(name.split('*').map(f => { const j = vars.indexOf(f); if (j < 0) throw new Error(`${ex.name}: factor ${f}`); return j }).sort((a, b) => a - b).map(String))}`
    : `.var ${vars.indexOf(name)}`))

  let leafNo = 0
  const lean = (t: Tree, path: Path): string => {
    if (!('leaf' in t)) {
      const id = canon(t.split)
      return `.split ${row(t.split)}\n  (${lean(t.yes, new Map(path).set(id, {lin: t.split, holds: true}))})\n  (${lean(t.no, new Map(path).set(id, {lin: t.split, holds: false}))})`
    }
    const base = leafConstraints(goal, path), prods = t.products ?? []
    const rows = withProducts(base, prods).map(r => r.lin), n0 = base.length
    // Only the rows the derivation and the products read, renumbered (products follow them, in order); cuts carry
    // their quotient row (Cert's format).
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
      return `.cut ${s.of} ${int(s.g)} ${list(dense(q).map(int))} ${int(cc)}`
    })
    if (tamper && dropStep && leafNo++ === 0) steps = steps.slice(0, -1) // the first leaf loses its last step
    // Cell pairs the path proves equal (Lean re-checks each).
    const eqs: string[] = []
    const cellCols = cols.map((name, j) => ({name, j})).filter(c2 => c2.name.includes('['))
    for (const [a, p] of cellCols.entries()) for (const q of cellCols.slice(a + 1)) {
      if (cellMap(p.name) !== cellMap(q.name)) continue
      const d = sub(cellKey(p.name), cellKey(q.name))
      if (decide(d, path) === true && decide(scale(d, -1), path) === true) eqs.push(`(${p.j}, ${q.j})`)
    }
    return `.leaf ${list(used.map(u => row(rows[u]!)))} ${list(steps)} ${list(eqs)} ${list(prods.map(([i, j]) => `(${idx(i)}, ${idx(j)})`))}`
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
example : checkGoal ${name}_goal ${name}_tree = false := by decide +kernel`
    : `-- ${ex.name}  (${cols.length} columns)
${body}
theorem ${name} : ∀ env maps, ¬ ∀ c ∈ ${name}_goal.hyps, evalC env maps c = true :=
  sound ${name}_goal ${name}_tree (by decide +kernel)`
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
  fmachine_sound ${id}_machine ${id}_proof (by decide +kernel)${corollary ? `\n${corollary}` : ''}`
  }
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_machine : Machine := ${machine}
def ${id}_proof : MachineProof := ${list(proof)}
theorem ${id}_laws : ∀ maps ρ, Reach ${id}_machine maps ρ → ∀ l ∈ ${id}_proof.map (·.1), evalC ρ maps l = true :=
  machine_sound ${id}_machine ${id}_proof (by decide +kernel)${corollary ? `\n${corollary}` : ''}`
}
export const TRUE = '.le (.const 0) (.const 0)'
export const grown = (g: Goal) => { const o = grow(g); if (!('tree' in o)) throw new Error(`${g.name}: stuck`); return o.tree }

// Loops through Kern.loop_sound: Lean builds the invariant and rank goals from the loop; the trees are the kernel's.
export function loopToLean(id: string, l: Loop, laws: Law[], rank: E | E[], tamper?: {what: string, loop: Loop}): string {
  const vars = [...l.params, ...l.inputs, ...Object.keys(l.state)]
  const gs = loopObligations(l, laws, rank)
  const enc = (g: Goal, tree = grown(g)) => encode({name: `${id}: ${g.name}`, goal: g, tree}, false, true, vars)
  const any0 = enc(gs[0]!, {leaf: []})
  const ix = (name: string) => vars.indexOf(name)
  const lit = (lp: Loop) => `⟨${list(lp.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(lp.state).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(lp.body).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${any0.c(lp.while)},
  ${lp.pre ? any0.c(lp.pre) : TRUE},
  ${lp.assume ? any0.c(lp.assume) : TRUE}⟩`
  const proof = laws.map((law, j) => {
    const s2 = enc(gs[2 * j]!), t = enc(gs[2 * j + 1]!)
    return `(${any0.c(law.holds)},\n  (${s2.tab}, ${s2.tree}),\n  (${t.tab}, ${t.tree}))`
  })
  const r = enc(gs.at(-1)!)
  const ranks = Array.isArray(rank) ? rank : [rank]
  return `-- ${l.name}: halts with ranks ${JSON.stringify(ranks.length)}${laws.length ? `, invariants ${laws.map(law => law.name).join('; ')}` : ''}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_loop : Loop := ${lit(l)}
def ${id}_proof : LoopProof := ⟨${list(proof)},
  ${list(ranks.map(any0.e))},
  (${r.tab}, ${r.tree})⟩
theorem ${id}_halts : ∀ maps ρ0, evalC ρ0 maps ${id}_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS ${id}_loop.init ρ0 maps ∧ ∀ n, Turn ${id}_loop maps (f n) (f (n + 1)) :=
  loop_sound ${id}_loop ${id}_proof (by decide +kernel)${tamper ? `
-- TAMPERED: ${tamper.what}. Lean computes the check to false.
def ${id}_tampered : Loop := ${lit(tamper.loop)}
example : checkLoop ${id}_tampered ${id}_proof = false := by decide +kernel` : ''}`
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
  fold_sound ${id}_fold ${id}_proof (by decide +kernel)${extra}`
}

// Machines with maps (and flags) through Kern.fmmachine_sound: Lean inlines the flags, then builds the start and step
// goals (read-over-write, ∀-laws at the proof's keys and at a skolem); the trees and the instance keys are the kernel's.
// Progress laws through Kern.progress_sound: Lean builds "the request is allowed" and "the step it causes"; a false
// variant is offered the true one's proof, and Lean computes the check to false.
// Readable corollaries: each law as a plain Lean statement over named variables (ρ the state, μ the maps, each name an
// abbreviation for its column), proven from the machine's theorem by unfolding the law's own definition. The statement
// is what a Lean development cites; the column numbers stay inside the namespace.
export function readable(id: string, laws: Law[], vars: string[], maps: string[], reach: {binders: string, hyp: string, call: string}): string {
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
  ${law.keys?.length ? `have hl : ${id}_e${j}.Holds ρ μ := ${reach.call} ${id}_e${j} (by simp [${id}_proof])
  exact fun k ${law.keys.map((_, i) => `k${i + 2}`).join(' ')} => (evalC_iff (upd (${law.keys.reduce((acc, key, i) => `upd (${acc}) ${vars.indexOf(key)} k${i + 2}`, 'ρ')}) ${vars.indexOf(law.forall!)} k) μ ${id}_l${j}.holds).mp (hl ${law.keys.map((_, i) => `k${i + 2}`).join(' ')} k)` : `have hl : ${id}_l${j}.Holds ρ μ := ${reach.call} ${id}_e${j} (by simp [${id}_proof])
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
  progress_sound ${id}_machine ${id}_proof ${pc.id} ${id}_check (by decide +kernel)${pc.tamper ? `
-- TAMPERED: ${pc.tamper.what}: the proof above offered for it. Lean computes the check to false.
def ${pc.id}_tampered : Progress := ${record(pc.tamper.when)}
example : checkProgress ${id}_machine ${id}_proof ${pc.id}_tampered = false := by decide +kernel` : ''}`
  })
  // Step laws through Kern.steplaw_sound: `when` and `then` sent with the flags inlined (as kernel.ts's goal has them).
  const sp = opts.stepLaws?.length ? proveStepLaws(m, laws, opts.stepLaws) : undefined
  if (opts.stepLaws?.length && (!sp?.proven || !sp.proof)) throw new Error(`${id}: step laws not proven`)
  const inlineFlags = (c: C): C => substC(c, {vars: {}, maps: {}, flags: m.step.flags ?? {}})
  const stepRecords = (opts.stepLaws ?? []).map((sl, j) => {
    const goal = stepLawObligations(m, laws, sp!.proof!.instances, sl)[0]!
    const pr = enc(goal, sp!.proof!.trees[goal.name]!)
    const insts = laws.flatMap((l, li) => (l.forall ? (sp!.proof!.instances[l.name] ?? []).map(key => `(${li}, ${any0.e(key)})`) : []))
    const primes = list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`)), primeMaps = list(baseMaps.map(mp => `(${mapNames.indexOf(mp)}, ${mapNames.indexOf(`${mp}'`)})`))
    const k = sl.steps ?? 1
    if (k === 1 && !Array.isArray(sl.when)) return `-- Step law: ${sl.name}
def ${id}_step${j} : StepLaw := ⟨${sl.when ? any0.c(inlineFlags(sl.when as C)) : TRUE},
  ${any0.c(inlineFlags(sl.then))},
  ${primes},
  ${primeMaps},
  ${list(insts)},
  (${pr.tab}, ${pr.tree})⟩
theorem ${id}_step${j}_holds : StepLawHolds ${id}_machine ${id}_step${j} :=
  steplaw_sound ${id}_machine ${id}_proof ${id}_step${j} ${id}_check (by decide +kernel)`
    // Through Kern.kstep_sound (Steps.lean): one `when` per step (0 <= 0 where none), the j-th request's inputs renamed.
    const whens = sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when]
    const ren = Array.from({length: k}, (_, s2) => (s2 === 0 ? '[]' : list(m.inputs.map(i => `(${ix(i)}, ${ix(`${i}@${s2 + 1}`)})`))))
    return `-- Step law over ${k} steps: ${sl.name}
def ${id}_step${j} : KStep := ⟨${list(Array.from({length: k}, (_, s2) => (whens[s2] ? any0.c(inlineFlags(whens[s2]!)) : TRUE)))},
  ${any0.c(inlineFlags(sl.then))},
  ${list(ren)},
  ${primes},
  ${primeMaps},
  ${list(insts)},
  (${pr.tab}, ${pr.tree})⟩
theorem ${id}_step${j}_holds : KStepHolds ${id}_machine ${id}_step${j} :=
  kstep_sound ${id}_machine ${id}_proof ${id}_step${j} ${id}_check (by decide +kernel)`
  })
  const machineDef = `def ${id}_machine : FMMachine := ${lit(m)}`
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}${flagNames.length ? `, with flags ${flagNames.join(', ')}` : ''}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${mapNames.map((v2, j) => `${j} ${v2}`).join(', ')})
${machineDef}
${entries.join('\n')}
def ${id}_proof : List MEntry := ${list(laws.map((_, j) => `${id}_e${j}`))}
theorem ${id}_check : checkFMMachine ${id}_machine ${id}_proof = true := by decide +kernel
theorem ${id}_laws : ∀ ρ M, FMReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.law.Holds ρ M :=
  fmmachine_sound ${id}_machine ${id}_proof ${id}_check
${readable(id, laws, vars, mapNames, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: `FMReach ${id}_machine ρ μ`, call: `${id}_laws ρ μ h`})}${opts.corollary ? `\n${opts.corollary}` : ''}${opts.tamper ? `
-- TAMPERED: ${opts.tamper.what}. Lean computes the check to false.
def ${id}_tampered : FMMachine := ${lit(opts.tamper.machine)}
example : checkFMMachine ${id}_tampered ${id}_proof = false := by decide +kernel` : ''}${progress.length ? `\n\n${progress.join('\n\n')}` : ''}${stepRecords.length ? `\n\n${stepRecords.join('\n\n')}` : ''}`
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
const boundKeys = (m: Machine) => [...Object.values(m.step.flags ?? {}).flatMap(c => (c.op === 'all' ? [c.key] : [])), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.each] : []))]
// A machine with a history goes as its plain machine (kernel.ts's historyMachine: sums as state, queries as inputs,
// the relations assumed), built in Lean from the machine and its history (History.lean's HMachine.plain), so every claim
// below is about it; with the relations' record goals, its laws hold over histories too (hmachine_sound).
// `historyTampers`: the history with other relations, each refused.
export function smachineToLean(id: string, given: Machine, laws: Law[], opts: {stepLaws?: StepLaw[], liveness?: Liveness[], tamper?: {what: string, machine: Machine}, simp?: string[], free?: string[],
    ghosts?: string[], after?: (ix: (name: string) => number) => string, historyTampers?: {what: string, relations: {when: C, holds: C}[], withRecordTrees: boolean}[],
    refined?: {impl: Machine, spec: Machine, wit: Record<string, E>, stutter: C, specPre: number}} = {}): string {
  const hm = given.history ? {...given, history: {...given.history, prune: undefined}} : undefined
  const hplain = hm ? historyMachine(hm) : undefined, m = hplain ? hplain.machine : given
  const stepLaws = opts.stepLaws ?? [], rf = opts.refined, gv = opts.ghosts ?? []
  // Every claim about the machine past its laws goes through one pipeline: a claim brings the step laws it needs and
  // the requests it needs proven allowed in a region, the proofs are found and encoded once for all claims, and each
  // claim states its theorem from them (the Lean meaning of each is a theorem in Live.lean, Refine.lean or Ghost.lean).
  type Allow = {when: C, request: Record<string, E>}
  type Helpers = {step: (sl: StepLaw) => {pr: {tab: string, tree: string}, inst: Instances}, sproof: (sl: StepLaw) => string, allow: (a: Allow) => string | undefined}
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
  [],
  ${list(Array.from({length: kk - 1}, (_, s2) => list(Object.keys(m.state).map(n2 => `(${ix(n2)}, ${ix(stateName(n2, s2 + 1))})`))))}⟩
theorem ${id}_step${j}_holds : SKStepHolds ${id}_machine ${id}_step${j} :=
  skstep_sound ${id}_machine ${id}_proof ${id}_step${j} ${id}_check (by decide +kernel)`
  }}))
  // A refinement (Refine.lean's SRefined): its step law, that the spec stutters or allows the request it is sent; srefines
  // says what the whole means.
  if (rf) claims.push({steps: [stepLaws[0]!], allows: [], render: h => {
    const primesL = list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`)), primeMapsL = list(Object.keys(m.maps ?? {}).map(mp => `(${mx(mp)}, ${mx(`${mp}'`)})`))
    const proofL = h.sproof(stepLaws[0]!)
    return `theorem ${id}_allowed : checkSKStep ${id}_machine ${id}_proof (srStep ${id}_refined ${primesL} ${primeMapsL} ${proofL}) = true := by decide +kernel
theorem ${id}_refines : ∀ ρ M, SReach ${id}_refined.impl ρ M → ∃ ρc Mc σ Ms, SReach ${id}_refined.full ρc Mc ∧ Agree ${id}_refined.SV ρc ρ
    ∧ (∀ mp, mp ∉ ${id}_refined.SM → Mc mp = M mp) ∧ SReach ${id}_refined.spec σ Ms ∧ Agree ${id}_refined.X σ ρc
    ∧ (∀ mp, mp ∉ ${id}_refined.IM → mp ∉ ${id}_refined.spec.carried → Ms mp = Mc mp) ∧ ∀ e ∈ ${id}_proof, e.Holds ρc Mc :=
  srefines ${id}_refined (by decide +kernel) (by decide +kernel) ${id}_proof ${id}_check ${rf.specPre} ⟨rfl, rfl⟩ ${primesL} ${primeMapsL} ${proofL} ${id}_allowed (by decide +kernel) (by decide +kernel) (by decide +kernel)`
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
theorem ${lid}_allows : sliveAllowsOk ${id}_machine ${id}_proof ${lid} ${lid}_ap = true := by decide +kernel
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
theorem ${lid}_ok : sliveOk ${id}_machine ${lid} = true := by decide +kernel
theorem ${lid}_stay : checkSKStep ${id}_machine ${id}_proof (sliveStep ${lid} ${lid}.pend (liveStayC ${lid}) ${lid}_sp) = true := by decide +kernel
theorem ${lid}_cover : checkSKStep ${id}_machine ${id}_proof (sliveStep ${lid} ${lid}.pend (liveCoverC ${lid}) ${lid}_cp) = true := by decide +kernel
theorem ${lid}_helps : sliveHelpsOk ${id}_machine ${id}_proof ${lid} ${lid}_hp = true := by decide +kernel
/-- ${l.name}: along every run that takes each helpful request infinitely often, \`from\` is followed by \`to\`. -/
theorem ${lid}_holds (run : SRun ${id}_machine)
    (fair : ∀ h ∈ ${lid}.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 ${lid}.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 ${lid}.to = true :=
  sleads_sound ${id}_machine ${id}_proof ${lid} _ _ _ ${id}_check ${lid}_ok ${lid}_stay ${lid}_cover ${lid}_helps run fair${wf}`
    }})
  }
  // Ghosts (Ghost.lean's sghost_laws): the laws that read no ghost hold of the machine without its ghosts.
  if (gv.length) claims.push({steps: [], allows: [], render: () => `-- The laws that read no ghost hold of the machine without its ghosts.
theorem ${id}_orig_laws : ∀ ρ M, SReach ${id}_ghosted.orig ρ M → ∀ e ∈ ${id}_proof, avoids ${id}_ghosted.vars e.law.holds = true → e.Holds ρ M :=
  sghost_laws ${id}_ghosted ${id}_ghostOk ${id}_proof ${id}_check`})
  const allSteps = claimSteps()
  const r = proveStepLaws(m, laws, allSteps)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const lp = r.proof.laws, si = r.proof.instances
  const flags = Object.entries(m.step.flags ?? {}), quantified = flags.filter(([, c]) => c.op === 'all').map(([f]) => f)
  const carried = m.inputMaps ?? [], facts = m.facts ?? [], keysOf = [...new Set([...laws, ...facts].flatMap(l => [l.forall, ...(l.keys ?? [])].filter((k): k is string => !!k)))]
  const k = Math.max(1, ...allSteps.map(sl => sl.steps ?? 1))
  const ext = [...m.inputs, ...quantified.flatMap(f => [`?${f}`, `w?${f}`])]
  const later = Array.from({length: k - 1}, (_, j) => ext.map(v => `${v}@${j + 2}`)).flat()
  const laterMaps = Array.from({length: k - 1}, (_, j) => carried.map(mp => `${mp}@${j + 2}`)).flat()
  const primes = allSteps.length ? Object.keys(m.state).map(s2 => `${s2}'`) : []
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
      ...Object.entries(inst).flatMap(([name, keys]) => { const f = factsF.find(f2 => f2.name === name); return f?.forall ? keys.map(key => sub1(f.holds, {[f.forall!]: key})) : [] }),
      ...laws.filter(lw => !lw.forall).map(lw => lw.holds),
      ...Object.entries(inst).flatMap(([name, keys]) => { const lw = laws.find(l2 => l2.name === name); return lw?.forall && !lw.keys?.length ? keys.map(key => sub1(lw.holds, {[lw.forall!]: key})) : [] }),
      ...Object.entries(inst).flatMap(([name, keys]) => {
        const lw = laws.find(l2 => l2.name === name)
        if (!lw?.keys?.length) return []
        const k = lw.keys.length + 1
        return Array.from({length: Math.floor(keys.length / k)}, (_, t) => sub1(sub1(lw.holds, Object.fromEntries(lw.keys!.map((kn, i) => [kn, keys[t * k + 1 + i]!]))), {[lw.forall!]: keys[t * k]!}))
      }),
      w,
      ...allFlags.flatMap(([f, fc]): C[] => (fc.op === 'all' ? [{op: '<=', a: {op: 'var', name: `?${f}`}, b: zero1(1)},
        ...(inst[`?${f}`] ?? []).map((key): C => ({op: 'or', xs: [eqC({op: 'var', name: `?${f}`}, zero1(0)), sub1(fc.c, {[fc.key]: key})]})),
        {op: 'or', xs: [eqC({op: 'var', name: `?${f}`}, zero1(1)), {op: 'not', x: sub1(fc.c, {[fc.key]: {op: 'var', name: `w?${f}`}})}]}] : []))]
    const last: C = {op: 'not', x: sInline(m.assume ?? trueC)}, zkeys = carriedKeys([...base, last])
    return {name: 'allowed', hyps: [...base, ...(m.inputMaps ?? []).flatMap(mp => zkeys.map(t => eqC({op: 'get', map: mp, key: t}, zero1(0)))), last], zkeys}
  }
  const allowed = new Map(claims.flatMap(cl => cl.allows).map(a => [a, withWitness(m, a.request, wit => {
    const r2 = proveBuilt(m, laws, inst => allowGoalS(inst, {op: 'and', xs: [a.when, reqTS(wit)]}))
    return r2.proven ? r2 : undefined
  })] as const))
  const allowGoals = [...allowed.values()].flatMap(a => (a ? [a.out.goal!] : []))
  const vars = [...new Set([...m.params, ...m.inputs, ...Object.keys(m.state), ...keysOf, ...keysOf.map(k2 => `${k2}#`), '#', ...flags.map(([f]) => `?${f}`),
    ...quantified.map(f => `w?${f}`), ...boundKeys(m), ...(opts.tamper ? boundKeys(opts.tamper.machine) : []), ...stepLaws.flatMap(sl => (sl.forall ? [sl.forall] : [])), ...(opts.free ?? []),
    ...primes, ...later, ...Array.from({length: k - 1}, (_, j) => Object.keys(m.state).map(n2 => stateName(n2, j + 1))).flat(),
    ...(hm ? hm.history.record.map(f => `r.${f}`) : []), ...[...goalsL, ...goalsS, ...allowGoals, ...(hplain?.goals ?? [])].flatMap(g => g.hyps.flatMap(varsOf))])]
  const baseMaps = [...new Set([...Object.keys(m.maps ?? {}), ...Object.keys(m.step.maps ?? {}), ...Object.keys(m.fns ?? {})])]
  const mapNames = [...new Set([...baseMaps, ...carried, ...(allSteps.length ? Object.keys(m.maps ?? {}).map(mp => `${mp}'`) : []), ...laterMaps,
    ...[...JSON.stringify([...goalsL, ...goalsS, ...allowGoals]).matchAll(/"op":"get","map":"([^"]+)"/g)].map(x2 => x2[1]!)])]
  const enc = (g: Goal, tree: Tree) => encode({name: `${id}: ${g.name}`, goal: g, tree}, false, true, vars, mapNames)
  const {e, c} = leanTerms(vars, mapNames, id)
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable for ${name}`); return j }
  const mx = (name: string) => { const j = mapNames.indexOf(name); if (j < 0) throw new Error(`${id}: no map for ${name}`); return j }
  const inline = (c2: C): C => substC(c2, {vars: {}, maps: {}, flags: flagsOfM(m)})
  const lit = (mm: Machine) => {
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
  ${list(fs.flatMap(([f, c2]) => (c2.op === 'all' ? [`(${ix(`?${f}`)}, ${ix(c2.key)}, ${c(c2.c)})`] : [])))},
  ${list(fs.flatMap(([f, c2]) => (c2.op === 'all' ? [`(${ix(`?${f}`)}, ${ix(`w?${f}`)})`] : [])))},
  ${list((mm.facts ?? []).map(l => `⟨${c(l.holds)}, ${l.forall ? `some ${ix(l.forall)}` : 'none'}⟩`))}⟩`
  }
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
example : checkHMachine ${id}_tampered${j} ${id}_proof ${t.withRecordTrees ? `${id}_records` : '[]'} = false := by decide +kernel`)
    return `def ${id}_records : List (List VDef × Tree) := ${list(records)}
theorem ${id}_hcheck : checkHMachine ${id}_hist ${id}_proof ${id}_records = true := by decide +kernel
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
  const finsts = (inst: Instances) => Object.entries(inst).flatMap(([name, keys]) => { const j = facts.findIndex(f => f.name === name); return j < 0 ? [] : keys.map(key => `(${j}, ${e(key)})`) })
  const qinsts = (inst: Instances) => Object.entries(inst).filter(([name]) => name.startsWith('?')).flatMap(([f, keys]) => keys.map(key => `(${ix(f)}, ${e(key)})`))
  const entries = laws.map((law, j) => {
    const g0 = goalsL[2 * j]!, g1 = goalsL[2 * j + 1]!, a = enc(g0, lp.trees[g0.name]!), b = enc(g1, lp.trees[g1.name]!), inst = lp.instances[law.name] ?? {}
    return `def ${id}_l${j} : MLaw := ⟨${c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩
def ${id}_e${j} : SEntry := ⟨${id}_l${j}, ${ix(law.forall ? `${law.forall}#` : '#')}, ${list((law.keys ?? []).map(key => String(ix(key))))}, ${list(insts(inst))}, ${list(qinsts(inst))}, ${list(finsts(inst))}, ${list(pinsts(inst))},
  (${a.tab}, [], ${a.tree}),
  (${b.tab}, [], ${b.tree})⟩`
  })
  // A ghosted machine (compose.ts's ghost): the original and its ghosts, the machine Lean checks built from them
  // (Ghost.lean), so the laws that read no ghost are laws of the original.
  const orig: Machine = {...m, state: Object.fromEntries(Object.entries(m.state).filter(([n2]) => !gv.includes(n2))), step: {...m.step, state: Object.fromEntries(Object.entries(m.step.state ?? {}).filter(([n2]) => !gv.includes(n2)))}}
  const h: Helpers = {
    step: sl => { const g = goalsS[allSteps.indexOf(sl)]!; return {pr: enc(g, r.proof!.trees[g.name]!), inst: instOf(sl)} },
    sproof: sl => { const {pr, inst} = h.step(sl); return `(${list(insts(inst))}, ${list(qinsts(inst))}, ${list(finsts(inst))}, ${list(pinsts(inst))}, (${pr.tab}, [], ${pr.tree}))` },
    allow: a => {
      const f2 = allowed.get(a)
      if (!f2) return undefined
      const ar = f2.out, pr = enc(ar.goal!, ar.tree!), inst = ar.instances!
      return `(${list(f2.wit.map(([inp, t]) => `(${ix(inp)}, ${e(t)})`))}, (${list(insts(inst))}, ${list(qinsts(inst))}, ${list(finsts(inst))}, ${list(pinsts(inst))}, (${pr.tab}, ${list(ar.goal!.hyps.map(c))}, ${pr.tree})), ${list((ar.goal as Goal & {zkeys: E[]}).zkeys.map(e))})`
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
theorem ${id}_ghostOk : sghostOk ${id}_ghosted = true := by decide +kernel` : hm ? `def ${id}_hist : HMachine := ${hlit(hm.history.relations ?? [])}
def ${id}_machine : SMachine := ${id}_hist.plain` : `def ${id}_machine : SMachine := ${lit(m)}`}
${entries.join('\n')}
def ${id}_proof : List SEntry := ${list(laws.map((_, j) => `${id}_e${j}`))}
theorem ${id}_check : checkSMachine ${id}_machine ${id}_proof = true := by decide +kernel
theorem ${id}_laws : ∀ ρ M, SReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M :=
  smachine_sound ${id}_machine ${id}_proof ${id}_check
${hm ? histBlock() : readable(id, laws, vars, mapNames, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: `SReach ${id}_machine ρ μ`, call: `${id}_laws ρ μ h`})}${factsProof(id, m, mapNames, opts.simp)}${opts.tamper ? `
-- TAMPERED: ${opts.tamper.what}. Lean computes the check to false.
def ${id}_tampered : SMachine := ${lit(opts.tamper.machine)}
example : checkSMachine ${id}_tampered ${id}_proof = false := by decide +kernel` : ''}${records.length ? `\n\n${records.join('\n\n')}` : ''}${opts.after ? `\n\n${opts.after(ix)}` : ''}`
}

// The facts, proven in Lean of the functions' Lean definitions, when every function has one: a run that starts with
// those functions starts where SReach asks the facts to hold.
function factsProof(id: string, m: Machine, maps: string[], simp: string[] = []): string {
  const fns = Object.entries(m.fns ?? {}), facts = m.facts ?? []
  if (!facts.length || !fns.length || fns.some(([, f]) => !f.lean)) return ''
  return `
-- The facts hold of the functions' Lean definitions: ${fns.map(([n, f]) => `${n} := ${f.lean}`).join('; ')}.
theorem ${id}_facts_hold (ρ : Nat → Nat) (μ : Nat → Nat → Nat) ${fns.map(([n, f], j) => `(h${j} : μ ${maps.indexOf(n)} = ${f.lean})`).join(' ')} :
    ∀ l ∈ ${id}_machine.facts, l.Holds ρ μ := by
  intro l hl
  simp only [${id}_machine, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ${facts.map(() => 'rfl').join(' | ')} <;> (simp only [MLaw.Holds]; try intro v); all_goals (simp [evalC, evalE, upd, ${[...fns.map((_, j) => `h${j}`), ...simp].join(', ')}]; try omega)`
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
  | {id: string, goal: Goal}

// A Lean file proving each item, to compile against the twin (`leanLibrary`, or `leanProject` for a ready Lake project).
// Each machine's laws come with `<id>_laws` (the twin's theorem) and `<id>.lawN` (the law as a plain Lean statement
// over named variables); step laws with `<id>_stepN_holds` (on the plain machine, `<id>s`, for a machine with a history);
// loops with `<id>_halts`; decisions with `<id>`. A machine with sets has its step laws as `<id>_stepN_holds`.
// Throws if the kernel can't prove one.
export function toLean(items: LeanItem[], opts: {title?: string} = {}): string {
  const ident = (id: string) => { const s = id.replace(/[^A-Za-z0-9_]/g, '_'); return /^[A-Za-z]/.test(s) ? s : `x_${s}` }
  const parts: string[] = [], theorems: string[] = []
  let goals = 0
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
      parts.push(`-- ${item.id}\n${item.lean?.defs ? `${item.lean.defs}\n` : ''}${smachineToLean(id, m, item.laws, {stepLaws: item.stepLaws, ...(item.liveness?.length ? {liveness: item.liveness} : {}),
        ...(item.ghosts?.length ? {ghosts: item.ghosts} : {}), ...(item.lean?.simp ? {simp: item.lean.simp} : {}), ...(item.lean?.after ? {after: item.lean.after} : {})})}`)
      theorems.push(`${id}_laws`, ...(m.history ? [`${id}_hlaws`] : []), ...(item.stepLaws ?? []).map((_, j) => `${id}_step${j}_holds`), ...(item.liveness ?? []).map((_, j) => `${id}_live${j}_holds`))
      if (item.lean?.after) theorems.push(...[...item.lean.after(() => 0).matchAll(/^theorem (\S+)/gm)].map(x2 => x2[1]!))
    } else if ('refinement' in item) {
      const {impl, spec, relation, witness} = item.refinement
      const stutter: C = item.refinement.stutter ?? {op: '<', a: n(0), b: n(0)}
      const R = refinement(impl, spec, {relation, witness, stutter}), S = refinementSides(impl, spec)
      const laws: Law[] = [...relation, {name: `${spec.name}'s precondition`, holds: spec.pre ?? atMost(n(0), n(0))}]
      const sl: StepLaw = R.stepLaws[0] ?? {name: `${spec.name} allows the request it is sent`, then: {op: 'or', xs: [stutter, atMost(n(0), n(0))]}}
      const refined = {impl: S.impl, spec: S.spec, wit: witness, stutter, specPre: relation.length}, free = spec.inputs.map(i => `b_${i}`)
      parts.push(`-- ${item.id}\n${smachineToLean(id, R.machine, laws, {stepLaws: [sl], free, refined})}`)
      theorems.push(`${id}_laws`, `${id}_refines`)
    } else if ('loop' in item) {
      parts.push(`-- ${item.id}\n${loopToLean(id, item.loop, item.laws ?? [], item.rank)}`)
      theorems.push(`${id}_halts`)
    } else {
      // goalToLean names its theorem t<i>; here it is the item's id.
      const n = goals++
      parts.push(goalToLean({name: item.id, goal: item.goal, tree: grown(item.goal)}, n, false).replace(new RegExp(`\\bt${n}(_goal|_tree)?\\b`, 'g'), (_, suffix: string | undefined) => `${id}${suffix ?? ''}`))
      theorems.push(id)
    }
  }
  // Sets.lean (which imports Steps.lean) only when a machine has sets.
  return `import History
import ${items.some(item => 'refinement' in item) ? 'Refine' : items.some(item => 'machine' in item && item.ghosts?.length) ? 'Ghost' : items.some(item => 'machine' in item && item.liveness?.length) ? 'Live' : items.some(item => 'machine' in item) ? 'Sets' : 'Steps'}
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
