// Kernel proofs as Lean: the machine, its laws and the kernel's trees as Lean.Kern data, each law a theorem by the twin's
// soundness theorems (Kernel.lean, Progress.lean, StepLaw.lean, Steps.lean, History.lean, Sets.lean) with `decide +kernel`. The
// emitter is untrusted: it names columns, orders rows and claims cell equalities; Lean checks every claim. Pure string
// building, so it ships in the package (`gdp-wired/lean`); export-kernel.ts is the repo's script around it.
import type {C, E, Law, Machine} from '../core/machine.ts'
import {atMost, n, not, pointWrite} from '../core/machine.ts'
import {type Lin, type Step, add, k, scale, sub} from '../core/solver.ts'
import {type Fold, type Goal, type Instances, type Liveness, type Loop, type Path, type StepLaw, type Tree, canon, historyMachine, foldObligations, leafConstraints, linear, livenessParts, loopObligations, obligations, progressObligations, stepLawObligations, substC, withProducts} from '../kernel/kernel.ts'
import {grow, proveLaws, proveProgress, proveStepLaws} from '../kernel/prove.ts'
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
  const cells = new Set<string>()
  const addCell = (name: string) => { if (cells.has(name)) return; cells.add(name); for (const key of Object.keys(cellKey(name))) if (key.includes('[')) addCell(key) }
  // Monomials: every one a leaf's rows or products use, or that a product term has under the leaf's path.
  const monos = new Set<string>()
  const subterms = (c: C): E[] => {
    const out2: E[] = []
    const we = (e: E): void => { out2.push(e); if (e.op === 'if') { wc(e.c); we(e.then); we(e.else) } else if (e.op === 'get') we(e.key); else if ('a' in e) { we(e.a); if ('b' in e) we(e.b) } }
    const wc = (c2: C): void => (c2.op === 'flag' ? undefined : c2.op === 'all' ? wc(c2.c) : c2.op === 'not' ? wc(c2.x) : c2.op === 'and' || c2.op === 'or' ? c2.xs.forEach(wc) : (we(c2.a), we(c2.b)))
    wc(c)
    return out2
  }
  leaves(tree, new Map(), (leaf, path) => {
    for (const r of withProducts(leafConstraints(goal, path), leaf.products ?? [])) for (const key of Object.keys(r.lin)) {
      if (key.includes('[')) addCell(key)
      else if (key.includes('*')) monos.add(key)
    }
    for (const h of goal.hyps) for (const e of subterms(h)) if (e.op === 'prod') for (const key of Object.keys(linear(e, path) ?? {})) if (key.includes('*')) monos.add(key)
  })
  const depth = (name: string) => name.split('[').length
  const cols = [...vars, ...[...monos].sort((a, b) => a.split('*').length - b.split('*').length), ...[...cells].sort((a, b) => depth(a) - depth(b))]
  const col = new Map(cols.map((name, j) => [name, j]))
  const maps = globalMaps ?? [...new Set([...[...cells].map(cellMap), ...goal.hyps.flatMap(h => [...JSON.stringify(h).matchAll(/"op":"get","map":"([^"]+)"/g)].map(m => m[1]!))])]
  const dense = (lin: Lin) => {
    const coefs = new Array(cols.length).fill(0)
    for (const [key, c] of Object.entries(lin)) if (key !== '1') { const j = col.get(key); if (j === undefined) throw new Error(`${ex.name}: no column for ${key}`); coefs[j] = c }
    while (coefs.length && coefs.at(-1) === 0) coefs.pop()
    return coefs as number[]
  }
  const row = (lin: Lin) => `⟨${list(dense(lin).map(int))}, ${int(lin['1'] ?? 0)}⟩`
  const tab = cols.map(name => (name.includes('[') ? `.cell ${maps.indexOf(cellMap(name))} ${row(cellKey(name))}`
    : name.includes('*') ? `.mono ${list(name.split('*').map(f => { const j = vars.indexOf(f); if (j < 0) throw new Error(`${ex.name}: factor ${f}`); return j }).sort((a, b) => a - b).map(String))}`
    : `.var ${vars.indexOf(name)}`))

  const {e, c} = leanTerms(vars, maps, ex.name)

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
        case 'var': return e.name === law.forall ? 'k' : e.name === law.forall2 ? 'k2' : `ρ ${q(e.name)}`
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
    return law.forall2 ? `∀ k k2 : Nat, ${p(law.holds)}` : law.forall ? `∀ k : Nat, ${p(law.holds)}` : p(law.holds)
  }
  const used = new Set(laws.flatMap(l => [...JSON.stringify(l.holds).matchAll(/"name":"([^"]+)"|"map":"([^"]+)"/g)].map(m => m[1] ?? m[2]!).filter(name => name !== l.forall && name !== l.forall2)))
  return `namespace ${id}
${[...vars.filter(v => used.has(v)).map(v => `abbrev ${q(v)} : Nat := ${vars.indexOf(v)}`), ...maps.filter(mp => used.has(mp)).map(mp => `abbrev ${q(mp)} : Nat := ${maps.indexOf(mp)}`)].join('\n')}
${laws.map((law, j) => (law.stated ? `-- ${law.name}: as written, with some key; proven (below) with the prover's witness in place\n` : '') + (JSON.stringify(law.holds).includes('"op":"if"') ? `-- ${law.name}: its terms read an if, so no plain statement here (${id}_laws holds it)` : `/-- ${law.name.replace(/-\//g, '- /')} -/
theorem law${j} ${reach.binders} (h : ${reach.hyp}) : ${statement(law)} := by
  ${law.forall2 ? `have hl : ${id}_e${j}.Holds ρ μ := ${reach.call} ${id}_e${j} (by simp [${id}_proof])
  exact fun k k2 => (evalC_iff (upd (upd ρ ${vars.indexOf(law.forall2)} k2) ${vars.indexOf(law.forall!)} k) μ ${id}_l${j}.holds).mp (hl k2 k)` : `have hl : ${id}_l${j}.Holds ρ μ := ${reach.call} ${id}_e${j} (by simp [${id}_proof])
  ${law.forall ? `exact fun k => (evalC_iff (upd ρ ${vars.indexOf(law.forall)} k) μ ${id}_l${j}.holds).mp (hl k)` : `exact (evalC_iff ρ μ ${id}_l${j}.holds).mp hl`}`}`)).join('\n')}
end ${id}`
}

export type ProgressCase = {id: string, name: string, when: C, then: C, request: Record<string, E>, instances: Instances, tamper?: {what: string, when: C}}
export function mmachineToLean(id: string, m: Machine, laws: Law[], opts: {corollary?: string, tamper?: {what: string, machine: Machine}, progress?: ProgressCase[], free?: string[], stepLaws?: StepLaw[], liveness?: Liveness[], ghosts?: string[], after?: (ix: (name: string) => number) => string} = {}): string {
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const keysOf = [...new Set(laws.flatMap(l => (l.forall ? [l.forall] : [])))]
  const flagNames = Object.keys(m.step.flags ?? {})
  const primed = !!(opts.progress || opts.stepLaws?.length || opts.liveness?.length)
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
  // Liveness through Kern.leads_sound (Live.lean): Lean builds the step law and the progress goal from the liveness.
  const liveRecords = (opts.liveness ?? []).map((l, j) => {
    const {stay, helpful} = livenessParts(m, l)
    const a = proveStepLaws(m, laws, [stay]), b = proveProgress(m, laws, helpful)
    if (!a.proven || !a.proof || !b.proven || !b.instances || !b.trees) throw new Error(`${id}: liveness ${l.name} not proven`)
    const sg = stepLawObligations(m, laws, a.proof.instances, stay)[0]!, ps2 = enc(sg, a.proof.trees[sg.name]!)
    const sinsts = laws.flatMap((lw, li) => (lw.forall ? (a.proof!.instances[lw.name] ?? []).map(key => `(${li}, ${any0.e(key)})`) : []))
    const gs2 = progressObligations(m, laws, b.instances, helpful), causes = gs2.at(-1)!
    const allowed = m.assume ? gs2[0]! : {name: `${helpful.name}: the request is allowed`, hyps: [...causes.hyps.slice(0, -1), not(atMost(n(0), n(0)))]}
    const ea = enc(allowed, b.trees[allowed.name] ?? grown(allowed)), ec = enc(causes, b.trees[causes.name]!)
    const pinsts = laws.flatMap((lw, li) => (lw.forall ? (b.instances![lw.name] ?? []).map(key => `(${li}, ${any0.e(key)})`) : []))
    const lid = `${id}_live${j}`
    return `-- Liveness: ${l.name}
def ${lid} : Live := ⟨${any0.c(l.from)}, ${any0.c(l.to)}, ${any0.e(l.rank)},
  ${list(Object.entries(l.request).map(([inp, e]) => `(${ix(inp)}, ${any0.e(e)})`))},
  ${list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`))},
  ${list(baseMaps.map(mp => `(${mapNames.indexOf(mp)}, ${mapNames.indexOf(`${mp}'`)})`))}⟩
theorem ${lid}_ok : liveOk ${id}_machine ${lid} = true := by decide +kernel
theorem ${lid}_stay : checkStepLaw ${id}_machine ${id}_proof (liveStay ${lid} ${list(sinsts)} (${ps2.tab}, ${ps2.tree})) = true := by decide +kernel
theorem ${lid}_help : checkProgress ${id}_machine ${id}_proof (liveHelp ${lid} ${list(pinsts)} (${ea.tab}, ${ea.tree}) (${ec.tab}, ${ec.tree})) = true := by decide +kernel
/-- ${l.name}: along every run that takes the helpful request infinitely often, \`from\` is followed by \`to\`. -/
theorem ${lid}_holds (run : FRun ${id}_machine)
    (fair : ∀ n, ∃ m, n ≤ m ∧ ∀ i ∈ ${id}_machine.m.inputs, run.req m i = applyS ${lid}.req (run.st m).1 (run.st m).2 i) :
    ∀ n, evalC (run.st n).1 (run.st n).2 ${lid}.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 ${lid}.to = true :=
  leads_sound ${id}_machine ${id}_proof ${lid} _ _ _ _ _ ${id}_check ${lid}_ok ${lid}_stay ${lid}_help run fair`
  })
  // A ghosted machine (compose.ts's ghost): the original and its ghosts, the machine Lean checks built from them
  // (Ghost.lean), so the laws that read no ghost are laws of the original.
  const gv = opts.ghosts ?? []
  const orig: Machine = {...m, state: Object.fromEntries(Object.entries(m.state).filter(([n2]) => !gv.includes(n2))), step: {...m.step, state: Object.fromEntries(Object.entries(m.step.state ?? {}).filter(([n2]) => !gv.includes(n2)))}}
  const machineDef = gv.length ? `def ${id}_ghosted : Ghosted := ⟨${lit(orig)},
  ${list(gv.map(v2 => `(${ix(v2)}, ${any0.e(m.state[v2]!)}, ${any0.e(m.step.state?.[v2] ?? {op: 'var', name: v2})})`))}⟩
def ${id}_machine : FMMachine := ${id}_ghosted.full
theorem ${id}_ghostOk : ghostOk ${id}_ghosted = true := by decide +kernel` : `def ${id}_machine : FMMachine := ${lit(m)}`
  const ghostLaws = gv.length ? `
-- The laws that read no ghost hold of the machine without its ghosts.
theorem ${id}_orig_laws : ∀ ρ M, FMReach ${id}_ghosted.orig ρ M → ∀ e ∈ ${id}_proof, avoids ${id}_ghosted.vars e.law.holds = true → e.law.Holds ρ M :=
  ghost_laws ${id}_ghosted ${id}_ghostOk ${id}_proof ${id}_check` : ''
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
example : checkFMMachine ${id}_tampered ${id}_proof = false := by decide +kernel` : ''}${progress.length ? `\n\n${progress.join('\n\n')}` : ''}${stepRecords.length ? `\n\n${stepRecords.join('\n\n')}` : ''}${liveRecords.length ? `\n\n${liveRecords.join('\n\n')}` : ''}${ghostLaws}${opts.after ? `\n\n${opts.after(ix)}` : ''}`
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
export function smachineToLean(id: string, m: Machine, laws: Law[], opts: {stepLaws?: StepLaw[], tamper?: {what: string, machine: Machine}, simp?: string[]} = {}): string {
  const stepLaws = opts.stepLaws ?? []
  const r = proveStepLaws(m, laws, stepLaws)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const lp = r.proof.laws, si = r.proof.instances
  const flags = Object.entries(m.step.flags ?? {}), quantified = flags.filter(([, c]) => c.op === 'all').map(([f]) => f)
  const carried = m.inputMaps ?? [], facts = m.facts ?? [], keysOf = [...new Set([...laws, ...facts].flatMap(l => [l.forall, l.forall2].filter((k): k is string => !!k)))]
  const k = Math.max(1, ...stepLaws.map(sl => sl.steps ?? 1))
  const ext = [...m.inputs, ...quantified.flatMap(f => [`?${f}`, `w?${f}`])]
  const later = Array.from({length: k - 1}, (_, j) => ext.map(v => `${v}@${j + 2}`)).flat()
  const laterMaps = Array.from({length: k - 1}, (_, j) => carried.map(mp => `${mp}@${j + 2}`)).flat()
  const primes = stepLaws.length ? Object.keys(m.state).map(s2 => `${s2}'`) : []
  const instOf = (sl: StepLaw) => r.proof!.perStep?.[sl.name] ?? si
  const goalsL = obligations(m, laws, lp.instances), goalsS = stepLaws.map(sl => stepLawObligations(m, laws, instOf(sl), sl)[0]!)
  const vars = [...new Set([...m.params, ...m.inputs, ...Object.keys(m.state), ...keysOf, ...keysOf.map(k2 => `${k2}#`), '#', ...flags.map(([f]) => `?${f}`),
    ...quantified.map(f => `w?${f}`), ...boundKeys(m), ...(opts.tamper ? boundKeys(opts.tamper.machine) : []), ...stepLaws.flatMap(sl => (sl.forall ? [sl.forall] : [])),
    ...primes, ...later, ...[...goalsL, ...goalsS].flatMap(g => g.hyps.flatMap(varsOf))])]
  const baseMaps = [...new Set([...Object.keys(m.maps ?? {}), ...Object.keys(m.step.maps ?? {}), ...Object.keys(m.fns ?? {})])]
  const mapNames = [...new Set([...baseMaps, ...carried, ...(stepLaws.length ? Object.keys(m.maps ?? {}).map(mp => `${mp}'`) : []), ...laterMaps,
    ...[...JSON.stringify([...goalsL, ...goalsS]).matchAll(/"op":"get","map":"([^"]+)"/g)].map(x2 => x2[1]!)])]
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
  const lawIx = (name: string) => laws.findIndex(l => l.name === name)
  const insts = (inst: Instances) => Object.entries(inst).filter(([name]) => lawIx(name) >= 0 && !laws[lawIx(name)]!.forall2).flatMap(([name, keys]) => keys.map(key => `(${lawIx(name)}, ${e(key)})`))
  // A law about every two keys is assumed at pairs (kept flattened).
  const pinsts = (inst: Instances) => Object.entries(inst).filter(([name]) => lawIx(name) >= 0 && laws[lawIx(name)]!.forall2).flatMap(([name, keys]) => keys.flatMap((key, i) => (i % 2 === 0 && keys[i + 1] ? [`(${lawIx(name)}, ${e(key)}, ${e(keys[i + 1]!)})`] : [])))
  const finsts = (inst: Instances) => Object.entries(inst).flatMap(([name, keys]) => { const j = facts.findIndex(f => f.name === name); return j < 0 ? [] : keys.map(key => `(${j}, ${e(key)})`) })
  const qinsts = (inst: Instances) => Object.entries(inst).filter(([name]) => name.startsWith('?')).flatMap(([f, keys]) => keys.map(key => `(${ix(f)}, ${e(key)})`))
  const entries = laws.map((law, j) => {
    const g0 = goalsL[2 * j]!, g1 = goalsL[2 * j + 1]!, a = enc(g0, lp.trees[g0.name]!), b = enc(g1, lp.trees[g1.name]!), inst = lp.instances[law.name] ?? {}
    return `def ${id}_l${j} : MLaw := ⟨${c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩
def ${id}_e${j} : SEntry := ⟨${id}_l${j}, ${ix(law.forall ? `${law.forall}#` : '#')}, ${law.forall2 ? `some ${ix(law.forall2)}` : 'none'}, ${list(insts(inst))}, ${list(qinsts(inst))}, ${list(finsts(inst))}, ${list(pinsts(inst))},
  (${a.tab}, ${a.tree}),
  (${b.tab}, ${b.tree})⟩`
  })
  const stepRecords = stepLaws.map((sl, j) => {
    const g = goalsS[j]!, pr = enc(g, r.proof!.trees[g.name]!), kk = sl.steps ?? 1
    const whens = sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when]
    const ren = Array.from({length: kk}, (_, s2) => (s2 === 0 ? '[]' : list(ext.map(v => `(${ix(v)}, ${ix(`${v}@${s2 + 1}`)})`))))
    const mren = Array.from({length: kk}, (_, s2) => (s2 === 0 ? '[]' : list(carried.map(mp => `(${mx(mp)}, ${mx(`${mp}@${s2 + 1}`)})`))))
    return `-- Step law${kk > 1 ? ` over ${kk} steps` : ''}: ${sl.name}
def ${id}_step${j} : SKStep := ⟨⟨${list(Array.from({length: kk}, (_, s2) => (whens[s2] ? c(inline(whens[s2]!)) : TRUE)))},
  ${c(inline(sl.then))},
  ${list(ren)},
  ${list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`))},
  ${list(Object.keys(m.maps ?? {}).map(mp => `(${mx(mp)}, ${mx(`${mp}'`)})`))},
  ${list(insts(instOf(sl)))},
  (${pr.tab}, ${pr.tree})⟩,
  ${list(mren)},
  ${list(qinsts(instOf(sl)))},
  ${list(finsts(instOf(sl)))},
  ${list(pinsts(instOf(sl)))}⟩
theorem ${id}_step${j}_holds : SKStepHolds ${id}_machine ${id}_step${j} :=
  skstep_sound ${id}_machine ${id}_proof ${id}_step${j} ${id}_check (by decide +kernel)`
  })
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}, with sets (carried ${carried.join(', ') || 'none'}; quantified flags ${quantified.join(', ') || 'none'})
--   (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${mapNames.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_machine : SMachine := ${lit(m)}
${entries.join('\n')}
def ${id}_proof : List SEntry := ${list(laws.map((_, j) => `${id}_e${j}`))}
theorem ${id}_check : checkSMachine ${id}_machine ${id}_proof = true := by decide +kernel
theorem ${id}_laws : ∀ ρ M, SReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M :=
  smachine_sound ${id}_machine ${id}_proof ${id}_check
${readable(id, laws, vars, mapNames, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat)', hyp: `SReach ${id}_machine ρ μ`, call: `${id}_laws ρ μ h`})}${factsProof(id, m, mapNames, opts.simp)}${opts.tamper ? `
-- TAMPERED: ${opts.tamper.what}. Lean computes the check to false.
def ${id}_tampered : SMachine := ${lit(opts.tamper.machine)}
example : checkSMachine ${id}_tampered ${id}_proof = false := by decide +kernel` : ''}${stepRecords.length ? `\n\n${stepRecords.join('\n\n')}` : ''}`
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
export function hmachineToLean(id: string, pruned: Machine, laws: Law[], tampers: {what: string, relations: {when: C, holds: C}[], withRecordTrees: boolean}[] = [], corollary?: (ix: (name: string) => number) => string): string {
  const m: Machine = {...pruned, history: {...pruned.history!, prune: undefined}}
  const h = m.history!
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const keysOf = [...new Set(laws.flatMap(l => (l.forall ? [l.forall] : [])))]
  const flagNames = Object.keys(m.step.flags ?? {})
  const sums = Object.keys(h.sums), fields = h.record.map(f => `r.${f}`)
  const vars = [...m.params, ...m.inputs, ...Object.keys(m.state), ...sums, ...keysOf, ...keysOf.map(k2 => `${k2}#`), '#', ...flagNames.map(f => `?${f}`), ...fields]
  const mapNames = [...new Set([...Object.keys(m.maps ?? {}), ...Object.keys(m.step.maps ?? {}), ...[...JSON.stringify(laws).matchAll(/"op":"get","map":"([^"]+)"/g)].map(x2 => x2[1]!)])]
  const gs = obligations(m, laws, r.proof.instances)
  const enc = (g: Goal, tree = r.proof!.trees[g.name]!) => encode({name: `${id}: ${g.name}`, goal: g, tree}, false, true, vars, mapNames)
  const any0 = enc(gs[0]!, {leaf: []})
  const ix = (name: string) => { const j = vars.indexOf(name); if (j < 0) throw new Error(`${id}: no variable ${name}`); return j }
  const rels = (rs: {when: C, holds: C}[]) => list(rs.map(rel => {
    if (rel.holds.op !== '<=') throw new Error(`${id}: a relation is a <= b`)
    return `(${any0.c(rel.when)}, ${any0.e(rel.holds.a)}, ${any0.e(rel.holds.b)})`
  }))
  const lit = (rs: {when: C, holds: C}[]) => `⟨⟨⟨${list(m.inputs.map(name => String(ix(name))))},
  ${list(Object.entries(m.state).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(m.maps ?? {}).map(([name, c2]) => `(${mapNames.indexOf(name)}, ${c2})`))},
  ${list(Object.entries(m.step.state ?? {}).map(([name, e]) => `(${ix(name)}, ${any0.e(e)})`))},
  ${list(Object.entries(m.step.maps ?? {}).map(([name, w]) => { const pw = pointWrite(w, 'Lean (for now)'); return `(${mapNames.indexOf(name)}, ${any0.e(pw.key)}, ${any0.e(pw.value)})` }))},
  ${m.pre ? any0.c(m.pre) : TRUE},
  ${m.assume ? any0.c(m.assume) : TRUE}⟩,
  ${list(flagNames.map(f => `(${ix(`?${f}`)}, ${any0.c(m.step.flags![f]!)})`))}⟩,
  ${any0.c(h.keep)},
  ${list(h.record.map(f => String(ix(f))))},
  ${list(fields.map(f => String(ix(f))))},
  ${list(Object.entries(h.sums).map(([name, g]) => `(${ix(name)}, ${any0.e(g)})`))},
  ${list(Object.entries(h.queries).map(([name, g]) => `(${ix(name)}, ${any0.e(g)})`))},
  ${rels(rs)}⟩`
  const entries = laws.map((law, j) => {
    const a = enc(gs[2 * j]!), b = enc(gs[2 * j + 1]!)
    const insts = Object.entries(r.proof!.instances[law.name] ?? {}).flatMap(([lname, keys]) => keys.map(key => `(${laws.findIndex(l => l.name === lname)}, ${any0.e(key)})`))
    return `def ${id}_l${j} : MLaw := ⟨${any0.c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩\ndef ${id}_e${j} : MEntry := ⟨${id}_l${j}, ${ix(law.forall ? `${law.forall}#` : '#')}, ${list(insts)},\n  (${a.tab}, ${a.tree}),\n  (${b.tab}, ${b.tree})⟩`
  })
  const records = gs.slice(2 * laws.length).map(g => { const x2 = enc(g); return `(${x2.tab}, ${x2.tree})` })
  const tamperText = tampers.map((t, j) => `-- TAMPERED: ${t.what}. Lean computes the check to false.
def ${id}_tampered${j} : HMachine := ${lit(t.relations)}
example : checkHMachine ${id}_tampered${j} ${id}_proof ${t.withRecordTrees ? `${id}_records` : '[]'} = false := by decide +kernel`)
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}, with a history (sums ${sums.join(', ')}; queries ${Object.keys(h.queries).join(', ')}; ${(h.relations ?? []).length} relation(s))
--   (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${mapNames.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_machine : HMachine := ${lit(h.relations ?? [])}
${entries.join('\n')}
def ${id}_proof : List MEntry := ${list(laws.map((_, j) => `${id}_e${j}`))}
def ${id}_records : List (List VDef × Tree) := ${list(records)}
theorem ${id}_check : checkHMachine ${id}_machine ${id}_proof ${id}_records = true := by decide +kernel
theorem ${id}_laws : ∀ ρ M hist, HReach ${id}_machine ρ M hist → ∀ e ∈ ${id}_proof, e.law.Holds ρ M :=
  hmachine_sound ${id}_machine ${id}_proof ${id}_records ${id}_check
${readable(id, laws, vars, mapNames, {binders: '(ρ : Nat → Nat) (μ : Nat → Nat → Nat) (hist : List (Nat → Nat))', hyp: `HReach ${id}_machine ρ μ hist`, call: `${id}_laws ρ μ hist h`})}${corollary ? `\n${corollary(ix)}` : ''}
${tamperText.join('\n')}`
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
      if (m.history && (m.fns || m.facts)) throw new Error(`${item.id}: functions on a machine with a history aren't exported to Lean yet`)
      if (hasSets(m) || item.laws.some(l => l.forall2)) {
        // Sets (or functions, or laws about two keys): the laws and the step laws in one export (one proof of both).
        parts.push(`-- ${item.id}\n${item.lean?.defs ? `${item.lean.defs}\n` : ''}${smachineToLean(id, m, item.laws, {stepLaws: item.stepLaws, ...(item.lean?.simp ? {simp: item.lean.simp} : {})})}`)
        theorems.push(`${id}_laws`, ...(item.stepLaws ?? []).map((_, j) => `${id}_step${j}_holds`))
        continue
      }
      if (item.liveness?.length && (m.history || hasSets(m))) throw new Error(`${item.id}: liveness is exported for machines without sets, functions or a history`)
      const ghosted = item.ghosts?.length ? {ghosts: item.ghosts, stepLaws: item.stepLaws ?? [], ...(item.lean?.after ? {after: item.lean.after} : {})} : {}
      parts.push(`-- ${item.id}\n${m.history ? hmachineToLean(id, m, item.laws) : mmachineToLean(id, m, item.laws, {...(item.liveness?.length ? {liveness: item.liveness} : {}), ...ghosted})}`)
      theorems.push(`${id}_laws`, ...(item.liveness ?? []).map((_, j) => `${id}_live${j}_holds`))
      if (item.ghosts?.length) item.stepLaws?.forEach((_, j) => theorems.push(`${id}_step${j}_holds`))
      if (item.lean?.after) theorems.push(...[...item.lean.after(() => 0).matchAll(/^theorem (\S+)/gm)].map(x2 => x2[1]!))
      else if (item.stepLaws?.length) {
        const plain = m.history ? historyMachine(m).machine : m, sid = m.history ? `${id}s` : `${id}_steps`
        parts.push(`-- ${item.id}: step laws\n${mmachineToLean(sid, plain, item.laws, {stepLaws: item.stepLaws})}`)
        item.stepLaws.forEach((_, j) => theorems.push(`${sid}_step${j}_holds`))
      }
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
import ${items.some(item => 'machine' in item && item.ghosts?.length) ? 'Ghost' : items.some(item => 'machine' in item && item.liveness?.length) ? 'Live' : items.some(item => 'machine' in item && (hasSets(item.machine) || item.laws.some(l => l.forall2))) ? 'Sets' : 'Steps'}
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
