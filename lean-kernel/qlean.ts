// Rationals to Lean: terms, conditions, goals, trees and machines over ℚ written for Rationals.lean (namespace Q).
// A tree's leaf is written as the rows its derivation reads, each the kernel's own row at that leaf (qLeafRows), with
// its strictness, and the derivation renumbered to them; Lean finds each among its own rows (`claimOk`) and replays it
// with checkQ. Untrusted: Lean checks what this writes.
import type {Lin, Step} from '../core/solver.ts'
import {type Path, type QC, type QE, type QGoal, type QLaw, type QMachine, type Rat, type Tree, canon, qLeafRows, qObligations, ratNorm} from '../kernel/kernel.ts'
import {proveQMachine} from '../core/rationals.ts'

const int = (n: bigint | number) => (n < 0 ? `(${n})` : String(n))
export const ratLean = (r: Rat): string => { const x = ratNorm(r); return x.den === 1n ? `(${int(x.num)} : Rat)` : `(${int(x.num)} / ${x.den} : Rat)` }
export function qTermLean(e: QE, ix: (name: string) => number): string {
  switch (e.op) {
    case 'var': return `.var ${ix(e.name)}`
    case 'const': return `.const ${ratLean(e.q)}`
    case 'mul': return `.mul ${ratLean(e.k)} (${qTermLean(e.a, ix)})`
    case 'if': return `.ite (${qCondLean(e.c, ix)}) (${qTermLean(e.then, ix)}) (${qTermLean(e.else, ix)})`
    case 'add': case 'sub': case 'min': case 'max': return `.${e.op} (${qTermLean(e.a, ix)}) (${qTermLean(e.b, ix)})`
  }
}
export function qCondLean(c: QC, ix: (name: string) => number): string {
  switch (c.op) {
    case '<=': case '<': case '=': return `.${c.op === '<=' ? 'le' : c.op === '<' ? 'lt' : 'eq'} (${qTermLean(c.a, ix)}) (${qTermLean(c.b, ix)})`
    case 'and': case 'or': return `.${c.op} (${qCondLean(c.a, ix)}) (${qCondLean(c.b, ix)})`
    case 'not': return `.not (${qCondLean(c.x, ix)})`
  }
}
// A row as Cert's: its nonzero coefficients in column order, and its constant.
export const qRowLean = (lin: Lin, ix: (name: string) => number): string => {
  const cs = Object.entries(lin).filter(([key, c]) => key !== '1' && c !== 0).map(([key, c]) => [ix(key), c] as const).sort((a, b) => a[0] - b[0])
  return `(sp [${cs.map(([j, c]) => `(${j}, ${int(c)})`).join(', ')}] ${int(lin['1'] ?? 0)})`
}
const stepLean = (s: Step) => (s.kind === 'input' ? `.input ${s.index}` : s.kind === 'combine' ? `.combine ${s.a} ${s.b} ${int(s.ma)} ${int(s.mb)}` : `.cut ${s.of} ${int(s.g)} [] 0`)
// A leaf's certificate: the rows its derivation reads (as the kernel reads them at the path) and the derivation over
// them. `tamper` changes the rows as written (Lean must then refuse the leaf).
// (`tamper` sees the leaf's own rows too, and returns undefined where it doesn't apply.)
export type LeafTamper = (rows: {lin: Lin, strict: boolean}[], leaf: {lin: Lin, strict: boolean}[]) => {lin: Lin, strict: boolean}[] | undefined
export function qLeafLean(goal: QGoal, path: Path, steps: Step[], ix: (name: string) => number, tamper?: LeafTamper): string {
  const rows = qLeafRows(goal, path), at = new Map<number, number>(), claimed: {lin: Lin, strict: boolean}[] = []
  const renum = steps.map(s => {
    if (s.kind !== 'input') return s
    let j = at.get(s.index)
    if (j === undefined) { j = claimed.length; at.set(s.index, j); const r = rows[s.index]; claimed.push(r ? {lin: r.lin, strict: r.strict === true} : {lin: {}, strict: false}) }
    return {...s, index: j}
  })
  const written = (tamper && tamper(claimed, rows.map(r => ({lin: r.lin, strict: r.strict === true})))) || claimed
  return `(.leaf [${written.map(r => `(${qRowLean(r.lin, ix)}, ${r.strict})`).join(', ')}] [${renum.map(stepLean).join(', ')}])`
}
export function qTreeLean(goal: QGoal, tree: Tree, ix: (name: string) => number, path: Path = new Map(), tamper?: LeafTamper): string {
  if ('leaf' in tree) return qLeafLean(goal, path, tree.leaf, ix, tamper)
  const key = canon(tree.split)
  const yes = qTreeLean(goal, tree.yes, ix, new Map(path).set(key, {lin: tree.split, holds: true}), tamper)
  const no = qTreeLean(goal, tree.no, ix, new Map(path).set(key, {lin: tree.split, holds: false}), tamper)
  return `(.split ${qRowLean(tree.split, ix)} (${yes}) (${no}))`
}

// A rule over the rationals as Lean: the machine, each law's start and step trees, `<id>_check` (checkMachine computed
// to true by Lean's kernel), `<id>_laws` (machine_sound: every law in every reachable state) and `<id>_lawN` (law N
// alone). Throws where the kernel can't prove a law. Variables are numbered params, inputs, state.
export function qmachineToLean(id: string, m: QMachine, laws: QLaw[], opts: {ms?: number} = {}): string {
  const v = proveQMachine(m, laws, opts)
  if (!v.proven || !v.checked || !v.proof) throw new Error(`${id}: not proven (${v.goal ?? ''} ${v.stuck ?? ''})`)
  const names = [...m.params, ...m.inputs, ...Object.keys(m.state)]
  const ix = (n: string) => { const j = names.indexOf(n); if (j < 0) throw new Error(`${id}: ${n} is not a variable of the rule`); return j }
  const pair = (r: Record<string, QE>) => `[${Object.entries(r).map(([n, e]) => `(${ix(n)}, ${qTermLean(e, ix)})`).join(', ')}]`
  const T = '.le (.const (0 : Rat)) (.const (0 : Rat))'
  const entries = laws.map(law => {
    const goals = qObligations(m, laws, law), t = v.proof!.trees[law.name]!
    return `(${qCondLean(law.holds, ix)}, ${qTreeLean(goals.start, t.start, ix)}, ${qTreeLean(goals.step, t.step, ix)})`
  })
  return `-- ${m.name}: variables ${names.map((n, j) => `${j} ${n}`).join(', ')}
noncomputable def ${id}_m : Q.Machine := {
  inputs := [${m.inputs.map(ix).join(', ')}],
  init := ${pair(m.state)},
  step := ${pair(m.step)},
  pre := ${m.pre ? qCondLean(m.pre, ix) : T},
  assume := ${m.assume ? qCondLean(m.assume, ix) : T} }
noncomputable def ${id}_ps : Q.MachineProof := [
  ${entries.join(',\n  ')}]
theorem ${id}_check : Q.checkMachine ${id}_m ${id}_ps = true := by decide +kernel
theorem ${id}_laws : ∀ ρ, Q.Reach ${id}_m ρ → ∀ l ∈ ${id}_ps.map (·.1), Q.evalC ρ l = true := Q.machine_sound ${id}_m ${id}_ps ${id}_check
${laws.map((law, j) => `-- ${law.name}
theorem ${id}_law${j} (ρ : Nat → Rat) (h : Q.Reach ${id}_m ρ) : Q.evalC ρ (${qCondLean(law.holds, ix)}) = true :=
  ${id}_laws ρ h _ (List.mem_map.mpr ⟨${id}_ps[${j}]'(by decide +kernel), List.getElem_mem _, rfl⟩)`).join('\n')}`
}
// A file of rules over the rationals, each through Q.machine_sound.
export function rationalsToLean(items: {id: string, machine: QMachine, laws: QLaw[]}[], title = 'Laws over the rationals proven by gdp-wired'): string {
  const ident = (id: string) => { const s = id.replace(/[^A-Za-z0-9_]/g, '_'); return /^[A-Za-z]/.test(s) ? s : `x_${s}` }
  const parts = items.map(it => qmachineToLean(ident(it.id), it.machine, it.laws))
  const theorems = items.flatMap(it => [`${ident(it.id)}_laws`, ...it.laws.map((_, j) => `${ident(it.id)}_law${j}`)])
  return `import Rationals
open Cert Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ${title}: the kernel's trees, checked by Lean against Rationals.lean, whose soundness theorems are proven there. -/

${parts.join('\n\n')}

${theorems.map(t => `#print axioms ${t}`).join('\n')}
`
}

// The examples (examples/rationals.ts) as Lean, for the suite's lean-rationals job: bun qlean.ts > RatExamples.lean
if (import.meta.main) {
  const {adversarial, feeLaws, feeSplit, ledger, ledgerLaws, limiter, limiterLaws, ratOf} = await import('../examples/rationals.ts')
  const items = [{id: 'fee_split', machine: feeSplit().machine, laws: feeLaws()}, {id: 'rate_limiter', machine: limiter().machine, laws: limiterLaws()},
    {id: 'decimal_ledger', machine: ledger().machine, laws: ledgerLaws()},
    ...adversarial.filter(a => a.holdsOver === 'ℚ').map((a, j) => ({id: `holds_over_Q_${j}`, ...ratOf(a)}))]
  console.log(rationalsToLean(items, 'The rational examples (examples/rationals.ts) and the laws that hold over ℚ but not over ℕ'))
}
