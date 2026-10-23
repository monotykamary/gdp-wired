// The conformance cases (core/conformance.ts) for Lean: each term and condition through the exporters' printer
// (lean-terms.ts), with the reference's value and truth, as `example`s Lean decides with its own evalE and evalC. The
// flag is the variable ?f, decided first, as Progress.lean's inlining reads it. Usage:
//   bun conformance.ts [cases] > Conformance.lean && lean Conformance.lean
// With --nonterm, the nontermination certificates instead (core/conformance.ts's recurCases: found, tampered, forged),
// each as `checkRecur loop recur = b` with b kernel.ts's checkRecur's answer, for NonTerm.lean's checkRecur to compute:
//   bun conformance.ts --nonterm [loops] > NonTermConformance.lean && lean NonTermConformance.lean
import {CELLS, INIT, VARS, randomCase, recurCases, reference, reseed, ringCase} from '../core/conformance.ts'
import type {Measure, Termination} from '../core/data.ts'
import type {Loop, Recur} from '../kernel/kernel.ts'
import {checkRecur} from '../kernel/kernel.ts'
import {recurLean} from './emit.ts'
import {leanTerms} from './lean-terms.ts'

reseed(Number(process.env.FUZZ_SEED ?? 4242))
const nonterm = process.argv.includes('--nonterm')
// With --rings, the rings of functions core/data.ts takes by well-founded recursion (core/conformance.ts's ringCase), each
// as one `mutual` block with `termination_by` the measures it found (Data.lean's Lx where they have several
// components), for Lean to check the decrease of every call again:
//   bun conformance.ts --rings [cases] > RingConformance.lean && lean RingConformance.lean
if (process.argv.includes('--rings')) {
  const n = Number(process.argv.filter(a => !a.startsWith('--'))[2] ?? 24), out: string[] = [], tally: Record<string, number> = {}
  const comp = (ps: string[], c: Measure['comps'][number]) => {
    const pos = [...c.coef.flatMap((k, i) => (k > 0 ? [`${k} * ${ps[i]}`] : [])), ...(c.c > 0 ? [String(c.c)] : [])], neg = [...c.coef.flatMap((k, i) => (k < 0 ? [`${-k} * ${ps[i]}`] : [])), ...(c.c < 0 ? [String(-c.c)] : [])]
    const sum = (ts: string[]) => (ts.length ? ts.join(' + ') : '0')
    return neg.length ? `(${sum(pos)} - (${sum(neg)}))` : `(${sum(pos)})`
  }
  for (let i = 0; i < n; i++) {
    const r = ringCase()
    let ts: (Termination | undefined)[]
    try { ts = r.fns.map(f => (void f.fn.ring, f.fn.termination)) } catch { tally[`${r.family}: refused`] = (tally[`${r.family}: refused`] ?? 0) + 1; continue }
    if (!ts.every(t => t)) { tally[`${r.family}: structural`] = (tally[`${r.family}: structural`] ?? 0) + 1; continue }
    const mOf = (j: number) => { const f = r.fns[j]!.fn, m = ts[j]!.measure, ps = f.params.map(q => q.name); return m.comps.length === 1 ? comp(ps, m.comps[0]!) : `Lx.mk [${m.comps.map(c => comp(ps, c)).join(', ')}]` }
    out.push(`-- ${r.name}: ${ts.map(t => t!.text).join('; ')}\nnamespace ${r.name}\n${r.lean(mOf(0), mOf(1))}\nend ${r.name}`)
    tally[`${r.family}: taken`] = (tally[`${r.family}: taken`] ?? 0) + 1
  }
  console.log(`import Data
open Kern
set_option linter.unusedSimpArgs false

/-! ${out.length} rings of functions core/data.ts took by well-founded recursion (core/conformance.ts's ringCase; ${Object.entries(tally).map(([w, k]) => `${w} ${k}`).join('; ')}): Lean checks each call's decrease again under the measures found. -/

${out.join('\n\n')}`)
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
