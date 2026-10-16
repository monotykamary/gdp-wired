// The conformance cases (core/conformance.ts) for Lean: each term and condition through the exporters' printer
// (lean-terms.ts), with the reference's value and truth, as `example`s Lean decides with its own evalE and evalC. The
// flag is the variable ?f, decided first, as Progress.lean's inlining reads it. Usage:
//   bun conformance.ts [cases] > Conformance.lean && lean Conformance.lean
import {CELLS, INIT, VARS, randomCase, reference, reseed} from '../core/conformance.ts'
import {leanTerms} from './lean-terms.ts'

reseed(Number(process.env.FUZZ_SEED ?? 4242))
const count = Number(process.argv[2] ?? 400)
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
