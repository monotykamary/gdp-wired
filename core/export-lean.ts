// Every refutation the library produced, as Lean data, for Lean's kernel to check against Cert.check (proven sound).
// Usage: bun export-lean.ts > ../research/lean/Obligations.lean
import {type Constraint, type Lin, type Step} from './solver.ts'
import {prove} from './machine.ts'
import {admit, boundedLoss, capLaws, inflight, inflightLoss, loss} from './models.ts'
import {atMost, n, plus, times, x} from './machine.ts'

type Ob = {name: string, constraints: Constraint[], steps: Step[]}
const obligations: Ob[] = []
const collect = (name: string, proof: ReturnType<typeof prove>) => {
  for (const [i, o] of proof.obligations.entries()) {
    if (o.verdict.kind !== 'refuted') throw new Error(`${name}: case ${i} is not refuted`)
    obligations.push({name: `${name} #${i}`, constraints: o.constraints, steps: o.verdict.steps})
  }
}
collect('bounded_loss', prove(loss(), boundedLoss))
for (const law of capLaws) collect(law.name.split(':')[0]!, prove(admit(), law, capLaws))
const inv = {name: 's + 50p <= b + 150', holds: atMost(plus(x('s'), times(50, x('p'))), plus(x('b'), n(150)))}
collect('inflight_invariant', prove(inflight, inv, [inflightLoss, inv]))
collect('inflight_loss', prove(inflight, inflightLoss, [inflightLoss, inv]))

const int = (v: number) => (v < 0 ? `(${v})` : String(v))
const list = (xs: string[]) => `[${xs.join(', ')}]`
function toLean(ob: Ob): {names: string[], rows: string, steps: string} {
  const names = [...new Set(ob.constraints.flatMap(c => Object.keys(c.lin).filter(key => key !== '1')))]
  const dense = (lin: Lin) => names.map(name => lin[name] ?? 0)
  const row = (lin: Lin) => `⟨${list(dense(lin).map(int))}, ${int(lin['1'] ?? 0)}⟩`
  const rows: Lin[] = []
  const steps = ob.steps.map(s => {
    if (s.kind === 'input') {
      rows.push(ob.constraints[s.index]!.lin)
      return `.input ${s.index}`
    }
    if (s.kind === 'combine') {
      const out: Lin = {}
      for (const [lin, m] of [[rows[s.a]!, s.ma], [rows[s.b]!, s.mb]] as const) for (const [key, c] of Object.entries(lin)) out[key] = (out[key] ?? 0) + m * c
      rows.push(out)
      return `.combine ${s.a} ${s.b} ${int(s.ma)} ${int(s.mb)}`
    }
    const from = rows[s.of]!
    const q: Lin = Object.fromEntries(names.filter(name => from[name]).map(name => [name, from[name]! / s.g]))
    const c = Math.ceil((from['1'] ?? 0) / s.g)
    rows.push({...q, 1: c})
    return `.cut ${s.of} ${int(s.g)} ${list(dense(q).map(int))} ${int(c)}`
  })
  return {names, rows: list(ob.constraints.map(c => row(c.lin))), steps: list(steps)}
}

const parts = obligations.map((ob, i) => {
  const {names, rows, steps} = toLean(ob)
  return `-- ${ob.name}: ${names.join(', ')}
def in${i} : List Row := ${rows}
def st${i} : List Step := ${steps}
theorem ob${i} : ∀ x, (∀ r ∈ in${i}, eval r x ≤ 0) → False := fun x hx => sound in${i} st${i} (by decide +kernel) x hx`
})
console.log(`import Cert
open Cert
set_option maxRecDepth 100000

/-! ${obligations.length} refutations from gdp-wired: bounded_loss, the caps rule's four caps, and the in-flight loss with
its strengthened invariant. Each \`obN\` says the case's constraints have no integer solution, by Cert.sound. -/

${parts.join('\n\n')}

#print axioms ob0
#print axioms ob${obligations.length - 1}`)
