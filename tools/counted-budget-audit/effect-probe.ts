// Diagnostic only: measure the actual primitive-support workload, never accept a proof here.
import {readPool, poolLaws} from '../../examples/effect-queue.ts'
import {proveRule} from '../../core/dsl.ts'
import {fullWork} from '../../kernel/prove.ts'
const {x} = readPool(4)
const work = Number(Bun.env.PROBE_WORK ?? 1_000_000)
const inv = [...x.invariants ?? []]
for (const law of (x as typeof x & {lemmas?: import('../../core/machine.ts').Law[]}).lemmas ?? []) {
  const start = fullWork()
  console.log(JSON.stringify({event: 'lemma-start', name: law.name, work}))
  const v = proveRule(x.rule!, [...inv, law], {search: Bun.env.PROBE_MODE === 'legacy' ? {ms: 60_000} : {work}})
  console.log(JSON.stringify({event: 'lemma-result', name: law.name, units: fullWork()-start, proven: v.proven, checked: v.checked, kernelProven: v.kernelProven, translation: v.translation, why: v.why, termination: v.termination, found: v.found?.laws?.map(l=>l.text)}))
  if (v.proven && v.checked || v.kernelProven === true && v.translation === 'unchecked') inv.push(law, ...(v.found?.laws ?? []).map(f=>f.law))
}
for (const law of poolLaws(x)) {
  const start = fullWork()
  console.log(JSON.stringify({event: 'law-start', name: law.name, work}))
  const v = proveRule(x.rule!, [...inv, law], {search: Bun.env.PROBE_MODE === 'legacy' ? {ms: 60_000} : {work}})
  console.log(JSON.stringify({event:'law-result',name:law.name,units:fullWork()-start,proven:v.proven,checked:v.checked,kernelProven:v.kernelProven,translation:v.translation,why:v.why,termination:v.termination}))
}
