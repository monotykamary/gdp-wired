import {resolve} from 'node:path'
import {classify} from './classify.ts'
import {controls, generate, nativeCheck, render} from './model.ts'
const [rootArg, seedArg, indexArg, replayArg, distArg] = process.argv.slice(2)
const root = resolve(rootArg!), seed = Number(seedArg), index = Number(indexArg)
const c = indexArg!.startsWith('control:') ? controls()[indexArg!.slice(8)]! : generate(seed, index)
if (!c) throw new Error('unknown control')
if (process.argv[7]) c.laws = [JSON.parse(process.argv[7]!)]
const prefix = distArg === 'dist' ? 'dist/core' : 'core', extension = distArg === 'dist' ? 'js' : 'ts'
const {extract} = await import(`${root}/${prefix}/extract.${extension}`)
const {buildLaw, LawError} = await import(`${root}/${prefix}/laws.${extension}`)
const {proveSteps} = await import(`${root}/${prefix}/dsl.${extension}`)
const replay = replayArg === 'replay'
const extraction = extract(c.source, {entry: c.entry, ...(c.standalone ? {mode: 'standalone'} : {}), ...(replay ? {} : {check: {runs: 0, states: 0, probes: false}})})
const laws: Record<string, unknown>[] = []
if (extraction.ok) for (const expression of c.laws) {
  const text = render(expression, true), nontrivial = expression.k !== 'lit'
  let built
  try { built = buildLaw(extraction, {name: text, expr: text, method: 'decide'}, {clock: 1, calendar: {weekend: ['sat', 'sun']}}) }
  catch (e) { if (!(e instanceof LawError)) throw e; laws.push({text, nontrivial, status: 'law-refused', message: String(e)}); continue }
  if (built.kind !== 'step') throw new Error('fuzzer expected a step law')
  const v = proveSteps(extraction.rule, extraction.invariants ?? [], [built.law], {from: 'any', search: false})
  const status = {proven: v.proven, checked: v.checked, kernelProven: v.kernelProven, translation: v.translation}
  if (v.kernelProven || v.proven && v.checked) {
    const native = nativeCheck(c, expression)
    laws.push({text, nontrivial, status: classify(v, native.ok, replay), proof: status, native, why: v.why})
  } else laws.push({text, nontrivial, status: v.stuck === 'unknown' ? 'unknown' : 'not-proven', proof: status, stuck: v.stuck})
}
console.log('FUZZ_CASE ' + JSON.stringify({id: c.id, family: c.family, tags: c.tags, source: c.source, root, replay: replay ? 'default' : 'disabled', extracted: extraction.ok, refusals: extraction.refusals, evidence: extraction.evidence, laws}, (_k, v) => v === undefined ? {$undefined: true} : typeof v === 'bigint' ? v.toString() : v))
