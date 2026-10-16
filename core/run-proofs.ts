import {checkRefutation, checkWitness} from './check.ts'
import {type Law, type Machine, prove, search} from './machine.ts'
import {admit, boundedLoss, capLaws, inflight, inflightLoss, loss} from './models.ts'

export function report(m: Machine, law: Law, invariants?: Law[]) {
  const proof = prove(m, law, invariants)
  const checked = proof.obligations.every(o => o.verdict.kind === 'refuted' ? checkRefutation(o.constraints, o.verdict.steps) : o.verdict.kind === 'sat' ? checkWitness(o.constraints, o.verdict.witness) : true)
  const steps = proof.obligations.reduce((sum, o) => sum + (o.verdict.kind === 'refuted' ? o.verdict.steps.length : 0), 0)
  if (proof.proven) {
    console.log(`PROVEN        ${m.name}: ${law.name}  (${proof.obligations.length} cases, ${steps} derivation steps, all ${checked ? 'checked' : 'NOT CHECKED'})`)
    return true
  }
  const real = search(m, law)
  if (real) console.log(`REFUTED       ${m.name}: ${law.name}  params ${JSON.stringify(real.params)}, requests ${JSON.stringify(real.trace)}`)
  else {
    const cti = proof.obligations.find(o => o.verdict.kind === 'sat')
    console.log(`NOT INDUCTIVE ${m.name}: ${law.name}  no counterexample from the start within 3 requests; a step from ${cti?.verdict.kind === 'sat' ? JSON.stringify(cti.verdict.witness) : '?'} breaks it`)
  }
  return false
}

if (import.meta.main) {
  report(loss(), boundedLoss)
  for (const law of capLaws) report(admit(), law, capLaws)
  report(loss(false), boundedLoss)
  report(admit(['Acct', 'Hour', 'Dom']), capLaws[1]!, capLaws)
  report(inflight, inflightLoss)
}
