// Real kernel trees as Lean data, each a theorem by Kern.sound with `decide +kernel`: the TypeScript kernel's verdicts,
// re-checked by a Lean twin whose soundness is proven. Usage: bun export-kernel.ts > Trees.lean
// The exporter is untrusted: it names columns, orders rows and claims cell equalities; Lean checks every claim.
import type {C, E, Law, Machine} from '../core/machine.ts'
import {all, any, atMost, bit, get, ite, less, max, min, minus, n, not, plus, prod, same, times, x} from '../core/machine.ts'
import {type Lin, type Step, add, k, scale, sub} from '../core/solver.ts'
import {admit, admitFlagged, boundedLoss, capLaws, inflight, inflightLoss, loss, windowCeiling, windowLimit} from '../core/models.ts'
import {agree, product} from '../next/relational.ts'
import {type Fold, type Goal, type Instances, type Loop, type Path, type StepLaw, type Tree, canon, foldObligations, historyMachine, leafConstraints, linear, loopObligations, obligations, progressObligations, stepLawObligations, substC, withProducts} from '../kernel/kernel.ts'
import {grow, proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {leanTerms} from './lean-terms.ts'

type Exported = {name: string, goal: Goal, tree: Tree}
const out: Exported[] = []
function machine(what: string, m: Machine, laws: Law[]) {
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${what}: not proven`)
  for (const g of obligations(m, laws, r.proof.instances)) out.push({name: `${what}: ${g.name}`, goal: g, tree: r.proof.trees[g.name]!})
}
function goals(what: string, gs: Goal[]) {
  for (const g of gs) {
    const o = grow(g)
    if (!('tree' in o)) throw new Error(`${what}: ${g.name} stuck`)
    out.push({name: `${what}: ${g.name}`, goal: g, tree: o.tree})
  }
}

machine('budget rule', loss(), [boundedLoss])
const strong: Law = {name: 's + 50p <= b + 150', holds: atMost(plus(x('s'), times(50, x('p'))), plus(x('b'), n(150)))}
machine('in-flight', inflight, [inflightLoss, strong])
const perAccount: Machine = (() => {
  const base = {...admit(), step: {maps: {Acct: {key: x('acct'), value: ite(all(same(x('ok'), n(1)), less(get('Acct', x('acct')), n(1))), plus(get('Acct', x('acct')), n(1)), get('Acct', x('acct')))}}}}
  const mine = all(same(x('who'), n(0)), same(x('acct'), x('Bacct')), same(x('day'), x('Bday')), same(x('hour'), x('Bhour')), same(x('dom'), x('Bdom')))
  const others = all(same(x('who'), n(1)), not(same(x('acct'), x('Bacct'))))
  return product(base, base, {name: 'isolation', params: ['Bacct', 'Bday', 'Bhour', 'Bdom'], inputs: ['who'], bInputs: {ok: ite(same(x('who'), n(1)), n(0), x('ok'))}, assume: all(bit('who'), any(mine, others))})
})()
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
const int = (v: number) => (v < 0 ? `(${v})` : String(v))
const list = (xs: string[]) => `[${xs.join(', ')}]`

function leaves(t: Tree, path: Path, visit: (t: Tree & {leaf: Step[], products?: [number, number][]}, path: Path) => void) {
  if ('leaf' in t) return visit(t, path)
  const id = canon(t.split)
  leaves(t.yes, new Map(path).set(id, {lin: t.split, holds: true}), visit)
  leaves(t.no, new Map(path).set(id, {lin: t.split, holds: false}), visit)
}

function encode(ex: Exported, tamper = false, dropStep = true, globalVars?: string[], globalMaps?: string[]) {
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
    const wc = (c2: C): void => (c2.op === 'flag' ? undefined : c2.op === 'not' ? wc(c2.x) : c2.op === 'and' || c2.op === 'or' ? c2.xs.forEach(wc) : (we(c2.a), we(c2.b)))
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

function toLean(ex: Exported, i: number, tamper = false, dropStep = true): string {
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
function machineToLean(id: string, m: Machine, laws: Law[], corollary?: string): string {
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
const TRUE = '.le (.const 0) (.const 0)'
const grown = (g: Goal) => { const o = grow(g); if (!('tree' in o)) throw new Error(`${g.name}: stuck`); return o.tree }

// Loops through Kern.loop_sound: Lean builds the invariant and rank goals from the loop; the trees are the kernel's.
function loopToLean(id: string, l: Loop, laws: Law[], rank: E | E[], tamper?: {what: string, loop: Loop}): string {
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
function foldToLean(id: string, f: Fold, laws: Law[], extra = ''): string {
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
type ProgressCase = {id: string, name: string, when: C, then: C, request: Record<string, E>, instances: Instances, tamper?: {what: string, when: C}}
function mmachineToLean(id: string, m: Machine, laws: Law[], opts: {corollary?: string, tamper?: {what: string, machine: Machine}, progress?: ProgressCase[], free?: string[], stepLaws?: StepLaw[]} = {}): string {
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${id}: not proven`)
  const keysOf = [...new Set(laws.flatMap(l => (l.forall ? [l.forall] : [])))]
  const flagNames = Object.keys(m.step.flags ?? {})
  const primed = !!(opts.progress || opts.stepLaws?.length)
  const primes = primed ? Object.keys(m.state).map(s2 => `${s2}'`) : []
  const vars = [...m.params, ...m.inputs, ...Object.keys(m.state), ...keysOf, ...keysOf.map(k2 => `${k2}#`), '#', ...flagNames.map(f => `?${f}`), ...(opts.free ?? []), ...(opts.stepLaws ?? []).flatMap(sl => (sl.forall ? [sl.forall] : [])), ...primes]
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
  ${list(Object.entries(mm.step.maps ?? {}).map(([name, w]) => `(${mapNames.indexOf(name)}, ${any0.e(w.key)}, ${any0.e(w.value)})`))},
  ${mm.pre ? any0.c(mm.pre) : TRUE},
  ${mm.assume ? any0.c(mm.assume) : TRUE}⟩,
  ${list(Object.entries(mm.step.flags ?? {}).map(([f, c2]) => `(${ix(`?${f}`)}, ${any0.c(c2)})`))}⟩`
  const entries = laws.map((law, j) => {
    const a = enc(gs[2 * j]!), b = enc(gs[2 * j + 1]!)
    const insts = Object.entries(r.proof!.instances[law.name] ?? {}).flatMap(([lname, keys]) => keys.map(key => `(${laws.findIndex(l => l.name === lname)}, ${any0.e(key)})`))
    return `⟨⟨${any0.c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩, ${ix(law.forall ? `${law.forall}#` : '#')}, ${list(insts)},\n  (${a.tab}, ${a.tree}),\n  (${b.tab}, ${b.tree})⟩`
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
    return `-- Step law: ${sl.name}
def ${id}_step${j} : StepLaw := ⟨${sl.when ? any0.c(inlineFlags(sl.when)) : TRUE},
  ${any0.c(inlineFlags(sl.then))},
  ${list(Object.keys(m.state).map(s2 => `(${ix(s2)}, ${ix(`${s2}'`)})`))},
  ${list(baseMaps.map(mp => `(${mapNames.indexOf(mp)}, ${mapNames.indexOf(`${mp}'`)})`))},
  ${list(insts)},
  (${pr.tab}, ${pr.tree})⟩
theorem ${id}_step${j}_holds : StepLawHolds ${id}_machine ${id}_step${j} :=
  steplaw_sound ${id}_machine ${id}_proof ${id}_step${j} ${id}_check (by decide +kernel)`
  })
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}${flagNames.length ? `, with flags ${flagNames.join(', ')}` : ''}  (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${mapNames.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_machine : FMMachine := ${lit(m)}
def ${id}_proof : List MEntry := ${list(entries)}
theorem ${id}_check : checkFMMachine ${id}_machine ${id}_proof = true := by decide +kernel
theorem ${id}_laws : ∀ ρ M, FMReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.law.Holds ρ M :=
  fmmachine_sound ${id}_machine ${id}_proof ${id}_check${opts.corollary ? `\n${opts.corollary}` : ''}${opts.tamper ? `
-- TAMPERED: ${opts.tamper.what}. Lean computes the check to false.
def ${id}_tampered : FMMachine := ${lit(opts.tamper.machine)}
example : checkFMMachine ${id}_tampered ${id}_proof = false := by decide +kernel` : ''}${progress.length ? `\n\n${progress.join('\n\n')}` : ''}${stepRecords.length ? `\n\n${stepRecords.join('\n\n')}` : ''}`
}

// Machines with a history through Kern.hmachine_sound (History.lean): Lean builds the plain machine (sums as state,
// relations in the assumption) and each relation's record goal; the trees and the instance keys are the kernel's.
// Pruning is left out: its goals are about the runtimes (dropping a record changes no query), the laws and relations
// are proven over the whole history either way, and Lean's HMachine has no pruning; the TypeScript kernel checks them.
function hmachineToLean(id: string, pruned: Machine, laws: Law[], tampers: {what: string, relations: {when: C, holds: C}[], withRecordTrees: boolean}[] = [], corollary?: (ix: (name: string) => number) => string): string {
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
  ${list(Object.entries(m.step.maps ?? {}).map(([name, w]) => `(${mapNames.indexOf(name)}, ${any0.e(w.key)}, ${any0.e(w.value)})`))},
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
    return `⟨⟨${any0.c(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩, ${ix(law.forall ? `${law.forall}#` : '#')}, ${list(insts)},\n  (${a.tab}, ${a.tree}),\n  (${b.tab}, ${b.tree})⟩`
  })
  const records = gs.slice(2 * laws.length).map(g => { const x2 = enc(g); return `(${x2.tab}, ${x2.tree})` })
  const tamperText = tampers.map((t, j) => `-- TAMPERED: ${t.what}. Lean computes the check to false.
def ${id}_tampered${j} : HMachine := ${lit(t.relations)}
example : checkHMachine ${id}_tampered${j} ${id}_proof ${t.withRecordTrees ? `${id}_records` : '[]'} = false := by decide +kernel`)
  return `-- ${m.name}: ${laws.map(l => l.name).join('; ')}, with a history (sums ${sums.join(', ')}; queries ${Object.keys(h.queries).join(', ')}; ${(h.relations ?? []).length} relation(s))
--   (variables ${vars.map((v2, j) => `${j} ${v2}`).join(', ')}; maps ${mapNames.map((v2, j) => `${j} ${v2}`).join(', ')})
def ${id}_machine : HMachine := ${lit(h.relations ?? [])}
def ${id}_proof : List MEntry := ${list(entries)}
def ${id}_records : List (List VDef × Tree) := ${list(records)}
theorem ${id}_check : checkHMachine ${id}_machine ${id}_proof ${id}_records = true := by decide +kernel
theorem ${id}_laws : ∀ ρ M hist, HReach ${id}_machine ρ M hist → ∀ e ∈ ${id}_proof, e.law.Holds ρ M :=
  hmachine_sound ${id}_machine ${id}_proof ${id}_records ${id}_check${corollary ? `\n${corollary(ix)}` : ''}
${tamperText.join('\n')}`
}

// The examples (../examples): every proven law of a domain, or of all of them, through the Lean twin: machines by
// machine_sound, fmachine/fmmachine_sound (flags, maps) or hmachine_sound (histories), loops by loop_sound, decisions
// as goals by Kern.sound. Usage: bun export-kernel.ts --examples [domain] > Examples.lean
if (process.argv.includes('--examples')) {
  const which = process.argv[process.argv.indexOf('--examples') + 1]
  // A path to a module exporting `domain` (e.g. ../compare/domain.ts), or a domain of ../examples by name.
  const {domains} = which?.endsWith('.ts')
    ? {domains: [((await import(`${process.cwd()}/${which}`)) as {domain: {domain: string, cases: unknown[]}}).domain] as Awaited<typeof import('../examples/index.ts')>['domains']}
    : await import('../examples/index.ts')
  const parts: string[] = [], theorems: string[] = []
  let goal = 0
  for (const d of domains.filter(dd => !which || which.startsWith('--') || which.endsWith('.ts') || dd.domain === which)) {
    d.cases.forEach((c, i) => {
      const id = `${d.domain}_${i}`.replace(/[^A-Za-z0-9_]/g, '_')
      if (c.kind === 'rule') {
        const m = c.rule.machine
        parts.push(`-- ${d.domain}: ${c.name}\n${m.history ? hmachineToLean(id, m, c.laws) : m.maps && Object.keys(m.maps).length ? mmachineToLean(id, m, c.laws) : machineToLean(id, m, c.laws)}`)
        theorems.push(`${id}_laws`)
        if (c.steps?.length) {
          // Step laws are about the plain machine: a history's sums as state, its queries as inputs (kernel.ts's
          // historyMachine, whose relations its laws' proof above checks per record).
          parts.push(`-- ${d.domain}: ${c.name}, step laws\n${mmachineToLean(`${id}s`, m.history ? historyMachine(m).machine : m, c.laws, {stepLaws: c.steps})}`)
          c.steps.forEach((_, j) => theorems.push(`${id}s_step${j}_holds`))
        }
      } else if (c.kind === 'loop') {
        parts.push(`-- ${d.domain}: ${c.name}\n${loopToLean(id, c.loop.loop, c.laws, c.loop.rankTerms)}`)
        theorems.push(`${id}_halts`)
      } else for (const dd of c.decisions) {
        parts.push(toLean({name: `${d.domain}: ${c.name}: ${dd.name}`, goal: dd.goal, tree: grown(dd.goal)}, goal, false))
        theorems.push(`t${goal++}`)
      }
    })
  }
  console.log(`import History
import StepLaw
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ${which?.endsWith('.ts') ? which : `The examples (gdp-wired/examples${which && !which.startsWith('--') ? `/${which}.ts` : ''})`}: the kernel's trees for every proven law, checked by the Lean twin. -/

${parts.join('\n\n')}

${theorems.map(t => `#print axioms ${t}`).join('\n')}`)
  process.exit(0)
}

if (process.argv.includes('--history')) {
  const m = windowLimit()
  const laws = [windowCeiling]
  const yes: C = same(n(0), n(0))
  const text = hmachineToLean('window', m, laws, [
    {what: 'the relation claimed at every t (not only t <= now), offered the same proofs', relations: [{when: yes, holds: atMost(x('ours'), x('seen'))}], withRecordTrees: true},
    {what: 'the relation left out (no record goal), offered the same machine proof', relations: [], withRecordTrees: false},
  ], ix => `-- The window ceiling in plain Lean: in every reachable state, the admitted requests in the window (variable ${ix('ours')},
-- the sum over the history) are at most c (variable ${ix('c')}), for every history of forced and admitted requests.
theorem window_ceiling (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) (h : HReach window_machine ρ M hist) :
    ρ ${ix('ours')} ≤ ρ ${ix('c')} := by
  have := window_laws ρ M hist h _ List.mem_cons_self
  simp only [MLaw.Holds, evalC, evalE] at this
  exact of_decide_eq_true this`)
  console.log(`import History
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! A sliding-window limit with a history (core/models.ts's windowLimit) through Kern.hmachine_sound: the window ceiling,
with the kernel's trees. -/

${text}

#print axioms window_laws
#print axioms window_ceiling`)
  process.exit(0)
}

const machines = [
  machineToLean('policy', loss(), [boundedLoss], `-- the budget rule's law in plain Lean: in every reachable state, s <= b + m (b, m, c, s are variables 0..3).
theorem bounded_loss (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach policy_machine maps ρ) : ρ 3 ≤ ρ 0 + ρ 1 := by
  have := policy_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`),
  machineToLean('inflight', inflight, [inflightLoss, strong], `-- the in-flight law in plain Lean: s <= b + 150 (b, t, done, s, p are variables 0..4).
theorem inflight_loss (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach inflight_machine maps ρ) : ρ 3 ≤ ρ 0 + 150 := by
  have := inflight_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`),
]

// TAMPERED: the budget rule's proof offered for the machine with the max_tokens cap forgotten (s + c, not s + min(c, m)).
const uncapped = loss(false), uv = [...uncapped.params, ...uncapped.inputs, ...Object.keys(uncapped.state)]
const ue = encode({name: 'uncapped', goal: obligations(uncapped, [boundedLoss])[0]!, tree: {leaf: []}}, false, true, uv)
// Products: a machine whose law is s <= m × requests (grind's lemma), a fold with a cap given as a param, and a goal
// that needs the product of two rows.
const counted: Machine = {name: 'loss, counted', params: ['m'], inputs: ['c'], state: {s: n(0), r: n(0)}, step: {state: {s: plus(x('s'), min(x('c'), x('m'))), r: plus(x('r'), n(1))}}}
machines.push(machineToLean('counted', counted, [{name: 's <= m × requests', holds: atMost(x('s'), prod(x('m'), x('r')))}], `-- In plain Lean: after any requests, s <= m · r (m, c, s, r are variables 0..3).
theorem loss_per_request (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach counted_machine maps ρ) : ρ 2 ≤ ρ 0 * ρ 3 := by
  have := counted_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`))
goals('products', [{name: 'x <= x·x', hyps: [not(atMost(x('x'), prod(x('x'), x('x'))))]}])
machines.push(`-- TAMPERED: the budget rule's proof offered for the machine with the max_tokens cap forgotten. Lean computes the check to false.
def uncapped_machine : Machine := ⟨[${uv.indexOf('c')}], [(${uv.indexOf('s')}, ${ue.e(uncapped.state.s!)})], [(${uv.indexOf('s')}, ${ue.e(uncapped.step.state!.s!)})], ${TRUE}, ${TRUE}⟩
example : checkMachine uncapped_machine policy_proof = false := by decide +kernel`)

const positive: Law[] = [{name: 'a >= 1', holds: atMost(n(1), x('a'))}, {name: 'b >= 1', holds: atMost(n(1), x('b'))}]
const euclid: Loop = {
  name: 'gcd by subtraction', params: ['A', 'B'], inputs: [], state: {a: x('A'), b: x('B')}, while: not(same(x('a'), x('b'))),
  body: {a: ite(less(x('b'), x('a')), minus(x('a'), x('b')), x('a')), b: ite(less(x('a'), x('b')), minus(x('b'), x('a')), x('b'))},
  pre: all(atMost(n(1), x('A')), atMost(n(1), x('B'))),
}
const {pre: _drop, ...noPre} = euclid
machines.push(loopToLean('gcd', euclid, positive, plus(x('a'), x('b')), {what: 'the gcd proof without the precondition A, B >= 1', loop: noPre}))
const pages: Loop = {name: 'pagination', params: ['total'], inputs: ['page'], state: {cur: n(0)}, while: less(x('cur'), x('total')), body: {cur: plus(x('cur'), min(x('page'), minus(x('total'), x('cur'))))}, assume: atMost(n(1), x('page'))}
machines.push(loopToLean('pages', pages, [], minus(x('total'), x('cur')), {what: 'the pagination proof when a page may be empty', loop: {...pages, assume: atMost(n(0), x('page'))}}))
const retry: Loop = {name: 'retry', params: ['budget'], inputs: ['wait'], state: {spent: n(0), tries: n(0)}, while: less(x('spent'), x('budget')), body: {spent: plus(x('spent'), max(n(1), x('wait'))), tries: plus(x('tries'), n(1))}}
machines.push(loopToLean('retry', retry, [], minus(x('budget'), x('spent'))))
const grid: Loop = {
  name: 'every cell of an n × m grid', params: ['n', 'm'], inputs: [], state: {i: n(0), j: n(0)}, while: less(x('i'), x('n')),
  body: {i: ite(less(x('j'), x('m')), x('i'), plus(x('i'), n(1))), j: ite(less(x('j'), x('m')), plus(x('j'), n(1)), n(0))},
}
machines.push(loopToLean('grid', grid, [], [minus(x('n'), x('i')), minus(x('m'), x('j'))]))
// TAMPERED: a rank that reads the turn's input; the loop runs forever (w = x + 1 each turn). kernel.ts refuses such ranks
// now, so the rank goal is written out here: while x < w, the rank w ∸ x after the turn is not below it before.
const forever: Loop = {name: 'forever', params: [], inputs: ['w'], state: {x: n(0)}, while: less(x('x'), x('w')), body: {x: plus(x('x'), n(1))}}
{
  const fv = [...forever.inputs, ...Object.keys(forever.state)]
  const g: Goal = {name: 'forever: rank drops', hyps: [forever.while, not(less(minus(x('w'), plus(x('x'), n(1))), minus(x('w'), x('x'))))]}
  const enc = encode({name: 'forever', goal: g, tree: grown(g)}, false, true, fv)
  machines.push(`-- TAMPERED: a rank (w ∸ x) that reads the turn's input w: its rank goal checks, yet the loop runs forever when every
-- turn sends w = x + 1. Lean's check refuses ranks over inputs and computes to false (kernel.ts now refuses them too).
def forever_loop : Loop := ⟨[0], [(1, .const 0)], [(1, .add (.var 1) (.const 1))], .lt (.var 1) (.var 0), ${TRUE}, ${TRUE}⟩
def forever_proof : LoopProof := ⟨[], [.sub (.var 0) (.var 1)], (${enc.tab}, ${enc.tree})⟩
example : checkLoop forever_loop forever_proof = false := by decide +kernel
-- Without that check the rank goal alone would pass:
example : checkGoal ⟨forever_proof.rank.1, rankGoal forever_loop [] forever_proof.ranks⟩ forever_proof.rank.2 = true := by decide +kernel`)
}
const shape: Fold = {
  name: 'shape', params: [], inputs: [], leaf: {leaves: n(1), nodes: n(0), height: n(0)},
  node: {leaves: plus(x('l_leaves'), x('r_leaves')), nodes: plus(plus(x('l_nodes'), x('r_nodes')), n(1)), height: plus(max(x('l_height'), x('r_height')), n(1))},
}
machines.push(foldToLean('shape', shape, [{name: 'leaves = nodes + 1', holds: same(x('leaves'), plus(x('nodes'), n(1)))}, {name: 'height <= nodes', holds: atMost(x('height'), x('nodes'))}, {name: 'height < leaves', holds: less(x('height'), x('leaves'))}], `
-- In plain Lean: every binary tree has one more leaf than it has nodes (leaves, nodes, height are variables 0..2).
theorem leaves_eq_nodes_succ (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (t : BTree) :
    foldT shape_fold ρ maps t 0 = foldT shape_fold ρ maps t 1 + 1 := by
  have := shape_laws maps ρ rfl t (allowed_trivial _ rfl ρ maps t) _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`))
const rollup = (cap: number): Fold => ({name: 'spend roll-up', params: [], inputs: ['c'], leaf: {spend: min(x('c'), n(cap)), count: n(1)}, node: {spend: plus(x('l_spend'), x('r_spend')), count: plus(x('l_count'), x('r_count'))}})
machines.push(foldToLean('rollup', rollup(50), [{name: 'spend <= 50 count', holds: atMost(x('spend'), times(50, x('count')))}], `
-- TAMPERED: the same proof offered for leaves capped at 51. Lean computes the check to false.
def rollup51_fold : Fold := { rollup_fold with leaf := [(1, .min (.var 0) (.const 51)), (2, .const 1)] }
example : checkFold rollup51_fold rollup_proof = false := by decide +kernel`))

machines.push(mmachineToLean('admit', admit(), capLaws, {
  corollary: `-- the caps rule's day cap in plain Lean: in every reachable state, every Day count is at most d (variable 0; Day is map 1).
theorem day_cap (ρ : Nat → Nat) (M : Nat → Nat → Nat) (h : FMReach admit_machine ρ M) (k : Nat) : M 1 k ≤ ρ 0 := by
  have := admit_laws ρ M h _ (List.mem_cons_of_mem _ List.mem_cons_self) k
  simpa [evalC, evalE, upd] using this`,
  tamper: {what: 'the admit proof offered for the machine whose Day cap is unguarded', machine: admit(['Acct', 'Hour', 'Dom'])},
}))
// Flags: budget rule with its guard named (room := s < b), and its proof offered for a guard that always admits.
const flagged = (room: C): Machine => ({...loss(), name: 'loss, guard as a flag', step: {flags: {room}, state: {s: ite({op: 'flag', name: 'room'}, plus(x('s'), min(x('c'), x('m'))), x('s'))}}})
machines.push(machineToLean('fpolicy', flagged(less(x('s'), x('b'))), [boundedLoss], `-- TAMPERED: the proof offered for the machine whose flag always admits (room := 0 <= 0). Lean computes the check to false.
def fpolicy_tampered : FMachine := { fpolicy_machine with flags := [(4, .le (.const 0) (.const 0))] }
example : checkFMachine fpolicy_tampered fpolicy_proof = false := by decide +kernel`))
machines.push(mmachineToLean('fadmit', admitFlagged(), capLaws, {tamper: {what: 'the flagged admit proof offered for a grant flag without the Day cap', machine: (() => {
  const m = admitFlagged(), f = m.step.flags!.granted! as {op: 'and', xs: C[]}
  return {...m, step: {...m.step, flags: {granted: {op: 'and', xs: f.xs.filter(c2 => !JSON.stringify(c2).includes('"Day"'))}}}}
})()}}))
// Progress (run-progress.ts's cases), through the machine with maps and flags.
const keysP = {A: x('A'), D: x('D'), H: x('H'), M: x('M')}
const underP = all(less(get('Acct', keysP.A), n(1)), less(get('Day', keysP.D), x('d')), less(get('Hour', keysP.H), x('hr')), less(get('Dom', keysP.M), x('dm')))
const instP = Object.fromEntries(capLaws.map(l => [l.name, [keysP.A, keysP.D, keysP.H, keysP.M]]))
const reqP = {acct: keysP.A, day: keysP.D, hour: keysP.H, dom: keysP.M, ok: n(1)}
machines.push(mmachineToLean('pflight', inflight, [inflightLoss, strong], {progress: [
  {id: 'flight_complete', name: 'in-flight: a request in flight can always complete', when: atMost(n(1), x('p')), then: less(x("p'"), x('p')), request: {t: n(0), done: n(1)}, instances: {},
    tamper: {what: 'with none in flight, one completes (false)', when: same(x('p'), n(0))}},
  {id: 'flight_admit', name: 'in-flight: under budget with room, one is admitted', when: all(less(x('s'), x('b')), less(x('p'), n(3))), then: same(x("p'"), plus(x('p'), n(1))), request: {t: n(0), done: n(0)}, instances: {}},
]}))
machines.push(mmachineToLean('padmit', admit(), capLaws, {free: ['A', 'D', 'H', 'M'], progress: [
  {id: 'admit_grant', name: 'admit: an account under every cap gets its grant', when: underP, then: same(get("Acct'", keysP.A), n(1)), request: reqP, instances: instP,
    tamper: {what: 'even with the day full (false)', when: all(less(get('Acct', keysP.A), n(1)), less(get('Hour', keysP.H), x('hr')), less(get('Dom', keysP.M), x('dm')))}},
]}))
machines.push(mmachineToLean('pfadmit', admitFlagged(), capLaws, {free: ['A', 'D', 'H', 'M'], progress: [
  {id: 'fadmit_grant', name: 'admit, the grant as a flag: an account under every cap gets its grant', when: underP, then: same(get("Acct'", keysP.A), n(1)), request: reqP, instances: instP},
]}))
machines.push(mmachineToLean('peracct', perAccount, [{name: 'a.Acct[B] = b.Acct[B]', holds: same(get('a_Acct', x('Bacct')), get('b_Acct', x('Bacct')))}]))
if (process.argv.includes('--big')) {
  const iso = (() => {
    const base = admitFlagged()
    const mine = all(same(x('who'), n(0)), same(x('acct'), x('Bacct')), same(x('day'), x('Bday')), same(x('hour'), x('Bhour')), same(x('dom'), x('Bdom')))
    const others = all(same(x('who'), n(1)), not(same(x('acct'), x('Bacct'))), not(same(x('day'), x('Bday'))), not(same(x('hour'), x('Bhour'))), not(same(x('dom'), x('Bdom'))))
    return product(base, base, {name: 'isolation', params: ['Bacct', 'Bday', 'Bhour', 'Bdom'], inputs: ['who'], bInputs: {ok: ite(same(x('who'), n(1)), n(0), x('ok'))}, assume: all(bit('who'), any(mine, others))})
  })()
  const atB = (kk: string, key: string): Law => ({name: `a.${kk}[B] = b.${kk}[B]`, holds: same(get(`a_${kk}`, x(key)), get(`b_${kk}`, x(key)))})
  machines.push(mmachineToLean('iso', iso, [atB('Acct', 'Bacct'), atB('Day', 'Bday'), atB('Hour', 'Bhour'), atB('Dom', 'Bdom')]))
  const a1 = admit()
  const caps = [['Dom', 'dom', x('dm')], ['Hour', 'hour', x('hr')], ['Day', 'day', x('d')], ['Acct', 'acct', n(1)]] as const
  const granted2 = all(...caps.map(([kk, f, cap]) => atMost(plus(get(kk, x(f)), n(1)), cap)), same(x('ok'), n(1)))
  const a2: Machine = {...a1, step: {maps: Object.fromEntries(caps.map(([kk, f]) => [kk, {key: x(f), value: ite(granted2, plus(get(kk, x(f)), n(1)), get(kk, x(f)))}]))}}
  machines.push(mmachineToLean('migration', product(admitFlagged(), a2), agree(a1)))
}

const rollupM: Fold = {name: 'spend roll-up, cap m a param', params: ['m'], inputs: ['c'], leaf: {spend: min(x('c'), x('m')), count: n(1)}, node: {spend: plus(x('l_spend'), x('r_spend')), count: plus(x('l_count'), x('r_count'))}}
machines.push(foldToLean('rollupM', rollupM, [{name: 'spend <= m count', holds: atMost(x('spend'), prod(x('m'), x('count')))}]))

const parts = [...machines, ...out.map((ex, i) => toLean(ex, i))]
parts.push(toLean(out[1]!, 1, true))
// The proof of s <= b + m offered for s <= b (false: the step admits up to m past b).
// The proof of x <= x·x offered for x·x <= x (false at x = 2).
const sq = out.findIndex(o => o.name === 'products: x <= x·x')
parts.push(toLean({name: 'the x <= x·x tree offered for x·x <= x', goal: {name: 'x·x <= x', hyps: [not(atMost(prod(x('x'), x('x')), x('x')))]}, tree: out[sq]!.tree}, 1002, true, false))
const wrong = obligations(loss(), [{name: 'wrong', holds: atMost(x('s'), x('b'))}])[1]!
parts.push(toLean({name: 'budget rule: the bounded_loss tree offered for s <= b', goal: wrong, tree: out[1]!.tree}, 1001, true, false))
console.log(`import Progress
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ${out.length} goals from gdp-wired's kernel (kernel/prove.ts trees), each checked by Lean's kernel against Kern.checkGoal,
whose soundness (Kern.sound) is proven in Kernel.lean. Goals: ${[...new Set(out.map(o => o.name.split(':')[0]))].join('; ')}. -/

${parts.join('\n\n')}

#print axioms t0
#print axioms t${out.length - 1}
#print axioms bounded_loss
#print axioms inflight_loss
#print axioms gcd_halts
#print axioms grid_halts
#print axioms leaves_eq_nodes_succ
#print axioms rollup_laws
#print axioms day_cap
#print axioms loss_per_request
#print axioms rollupM_laws
#print axioms peracct_laws
#print axioms fpolicy_laws
#print axioms fadmit_laws
#print axioms flight_complete_holds
#print axioms flight_admit_holds
#print axioms admit_grant_holds
#print axioms fadmit_grant_holds${process.argv.includes('--big') ? '\n#print axioms iso_laws\n#print axioms migration_laws' : ''}`)
console.error(out.map((o, i) => `t${i}  ${o.name}`).join('\n'))
