// The conformance cases (core/conformance.ts) for Lean: each term and condition through the exporters' printer
// (lean-terms.ts), with the reference's value and truth, as `example`s Lean decides with its own evalE and evalC. The
// flag is the variable ?f, decided first, as Progress.lean's inlining reads it. Usage:
//   bun conformance.ts [cases] > Conformance.lean && lean Conformance.lean
// With --nonterm, the nontermination certificates instead (core/conformance.ts's recurCases: found, tampered, forged),
// each as `checkRecur loop recur = b` with b kernel.ts's checkRecur's answer, for NonTerm.lean's checkRecur to compute:
//   bun conformance.ts --nonterm [loops] > NonTermConformance.lean && lean NonTermConformance.lean
// With --rationals, the rational cases (core/conformance.ts's randomQCase): values, proven goals' trees, their tampered
// twins and models, each with kernel.ts's answer, for Rationals.lean to compute:
//   bun conformance.ts --rationals [cases] > RatConformance.lean && lean RatConformance.lean
import {CELLS, INIT, VARS, qgoals, qreference, qtampered, randomCase, randomQCase, recurCases, reference, reseed} from '../core/conformance.ts'
import type {Loop, QGoal, Recur} from '../kernel/kernel.ts'
import {canon, checkQTree, checkRecur} from '../kernel/kernel.ts'
import {growQ} from '../kernel/qprove.ts'
import {type Rat, q} from '../core/q.ts'
import type {Lin} from '../core/solver.ts'
import {type LeafTamper, qCondLean, qTermLean, qTreeLean, ratLean} from './qlean.ts'
import {recurLean} from './emit.ts'
import {leanTerms} from './lean-terms.ts'

reseed(Number(process.env.FUZZ_SEED ?? 4242))
const nonterm = process.argv.includes('--nonterm'), rationals = process.argv.includes('--rationals')
if (rationals) {
  // Rationals: each case's term and condition through Q.evalE and Q.evalC; each proven goal's tree (kernel.ts's answer
  // true), its tampered twins (the kernel's answer false), and its leaves written wrong for Lean alone (a claimed row's
  // coefficient sign flipped, a claimed row not among the leaf's, a row claimed strict that isn't), each computed to
  // false; and each model the search found, every hypothesis true at it in Lean too.
  const ix = (x: string) => VARS.indexOf(x as typeof VARS[number])
  const envOf = (at: Record<string, Rat>) => `(fun i => [${VARS.map(x => ratLean(at[x] ?? q(0))).join(', ')}].getD i 0)`
  const hypsOf = (g: QGoal) => `[${g.hyps.map(h => qCondLean(h, ix)).join(', ')}]`
  const key = (lin: Lin) => canon(Object.fromEntries(Object.entries(lin).filter(([, c]) => c !== 0)))
  const inLeaf = (r: {lin: Lin}, leaf: {lin: Lin}[]) => leaf.some(l => key(l.lin) === key(r.lin))
  const tampers: [string, LeafTamper][] = [
    ['a claimed row with a coefficient sign flipped', (rows, leaf) => {
      for (const [i, r] of rows.entries()) {
        const x = Object.keys(r.lin).find(n => n !== '1' && r.lin[n] !== 0)
        if (!x) continue
        const t = {lin: {...r.lin, [x]: -r.lin[x]!}, strict: r.strict}
        if (!inLeaf(t, leaf)) return rows.map((s, j) => (j === i ? t : s))
      }
      return undefined
    }],
    ['a claimed row not among the leaf\'s', (rows, leaf) => {
      const t = {lin: {...rows[0]!.lin, 1: (rows[0]!.lin['1'] ?? 0) + 1}, strict: rows[0]!.strict}
      return inLeaf(t, leaf) ? undefined : [t, ...rows.slice(1)]
    }],
    ['a row claimed strict that is not', (rows, leaf) => {
      const i = rows.findIndex(r => !r.strict && !leaf.some(l => l.strict && key(l.lin) === key(r.lin)))
      return i < 0 ? undefined : rows.map((s, j) => (j === i ? {...s, strict: true} : s))
    }],
  ]
  const out: string[] = [], tally: Record<string, number> = {}
  const count = (w: string) => { tally[w] = (tally[w] ?? 0) + 1 }
  const count0 = Number(process.argv.filter(a => !a.startsWith('--'))[2] ?? 60)
  for (let i = 0; i < count0; i++) {
    const k = randomQCase(1 + (i % 3)), ref = qreference(k), env = envOf(k.env)
    out.push(`example : Q.evalE ${env} (${qTermLean(k.t, ix)}) = ${ratLean(ref.value)} := by decide +kernel`)
    out.push(`example : Q.evalC ${env} (${qCondLean(k.c, ix)}) = ${ref.holds} := by decide +kernel`)
    count('values')
    const goals = qgoals(k)
    for (const g of goals.proven) {
      const r = growQ(g)
      if (!('tree' in r)) throw new Error(`case ${i}: ${g.name} not proven`)
      out.push(`example : Q.checkGoal ${hypsOf(g)} ${qTreeLean(g, r.tree, ix)} = ${checkQTree(g, r.tree)} := by decide +kernel`)
      count(`proven: ${checkQTree(g, r.tree)}`)
      for (const t of qtampered(r.tree)) {
        out.push(`-- ${t.what}\nexample : Q.checkGoal ${hypsOf(g)} ${qTreeLean(g, t.tree, ix)} = ${checkQTree(g, t.tree)} := by decide +kernel`)
        count(`${t.what}: ${checkQTree(g, t.tree)}`)
      }
      for (const [what, f] of tampers) {
        let applied = false
        const text = qTreeLean(g, r.tree, ix, new Map(), (rows, leaf) => { const t = f(rows, leaf); if (t) applied = true; return t })
        if (!applied) continue
        out.push(`-- ${what}\nexample : Q.checkGoal ${hypsOf(g)} ${text} = false := by decide +kernel`)
        count(`${what}: false`)
      }
    }
    for (const g of goals.models) {
      const r = growQ(g)
      if ('tree' in r || !r.rational) throw new Error(`case ${i}: ${g.name} has no model`)
      out.push(`example : ${hypsOf(g)}.all (Q.evalC ${envOf(r.rational)}) = true := by decide +kernel`)
      count('models')
    }
  }
  console.log(`import Rationals
open Cert Kern

/-! ${out.length} rational conformance cases from core/conformance.ts (${Object.entries(tally).map(([w, n]) => `${w} ${n}`).join('; ')}):
Rationals.lean's evalE, evalC and checkGoal compute kernel.ts's answers. -/

${out.join('\n')}`)
  process.exit(0)
}
const count = Number(process.argv.filter(a => !a.startsWith('--'))[2] ?? (nonterm ? 40 : 400))
if (nonterm) {
  const out: string[] = [], tally: Record<string, number> = {}
  const found = new Map<Loop, Recur>()
  recurCases(count).forEach((k, i) => {
    if (k.what === 'found') found.set(k.loop, k.recur)
    let ts = false
    try { ts = checkRecur(k.loop, k.recur) } catch { ts = false }
    const {loop, recur} = recurLean(`case ${i}`, k.loop, found.get(k.loop) ?? k.recur)
    out.push(`-- ${k.loop.name}: ${k.what}\nexample : checkRecur ${loop} ${recur(k.recur)} = ${ts} := by decide +kernel`)
    tally[`${k.what}: ${ts}`] = (tally[`${k.what}: ${ts}`] ?? 0) + 1
  })
  console.log(`import NonTerm
open Kern

/-! ${out.length} nontermination certificates from core/conformance.ts's recurCases (${Object.entries(tally).map(([w, n]) => `${w} ${n}`).join('; ')}): NonTerm.lean's checkRecur
computes kernel.ts's answer on each. -/

${out.join('\n\n')}`)
  process.exit(0)
}
const vars = [...VARS, '?f'], maps = ['M']
const {e, c} = leanTerms(vars, maps, 'conformance')
const lines: string[] = []
for (let i = 0; i < count; i++) {
  const k = randomCase(1 + (i % 3))
  const ref = reference(k)
  const fv = ref.flag ? 1 : 0
  const env = `(fun i => [${[...VARS.map(v => k.input[v]!), fv].join(', ')}].getD i 0)`
  const cells = `(fun m key => if m = 0 then [${k.cells.join(', ')}].getD key ${INIT} else 0)`
  lines.push(`example : evalE ${env} ${cells} (${e(k.t)}) = ${ref.value} := by decide`)
  lines.push(`example : evalC ${env} ${cells} (${c(k.c)}) = ${ref.holds} := by decide`)
  lines.push(`example : evalC ${env} ${cells} (${c(k.f)}) = ${ref.flag} := by decide`)
}
void CELLS
console.log(`import Kernel
open Kern

/-! ${count} conformance cases from core/conformance.ts: Lean's evalE and evalC give the TypeScript reference's values. -/

${lines.join('\n')}`)
