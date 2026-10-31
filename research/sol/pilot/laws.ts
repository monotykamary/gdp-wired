// A file's comment laws proven one by one, each timed (the extraction's check small: --quick), to find a slow stage.
import {readFileSync} from 'node:fs'
import {extractSolidity} from '../../../core/extract-sol.ts'
import {buildLaw, lawsIn} from '../../../core/laws.ts'
import {proveRule, proveSteps} from '../../../core/dsl.ts'
const [file, root] = process.argv.slice(2), quick = process.argv.includes('--quick'), ms = Number(process.env.MS ?? 60000)
let t0 = performance.now()
const x = extractSolidity(file!, {root, ...(quick ? {check: {runs: 10, states: 20}} : {}), ...(process.env.METHODS ? {methods: process.env.METHODS.split(',')} : {})})
console.log(`extracted: ${x.ok} in ${Math.round(performance.now() - t0)} ms ${JSON.stringify(x.refusals)} ${JSON.stringify({requests: x.evidence?.requests, states: x.evidence?.fromStates, probes: x.evidence?.probes})}`)
if (!x.ok) process.exit(1)
for (const l of lawsIn(readFileSync(file!, 'utf8')).filter(l => !process.env.LAW || l.name === process.env.LAW)) {
  t0 = performance.now()
  const b = buildLaw(x, l)
  const v = b.kind === 'law' ? proveRule(x.rule!, [...x.invariants ?? [], b.law], {search: {ms}}) : proveSteps(x.rule!, [...x.invariants ?? []] as never, [b.law], {search: {ms}})
  const rp = v.run && x.replay ? x.replay(v.run, b.law) : undefined
  console.log(`${l.name}: ${v.proven && v.checked ? 'proven' : v.run ? 'broken' : 'unknown'} in ${Math.round(performance.now() - t0)} ms${rp ? ` (${rp.what})` : ''}${v.why ? ` (${v.why})` : ''}`)
}
