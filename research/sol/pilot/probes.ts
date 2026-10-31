// Each of the check's probes (a branch condition refuted as "never holds") timed on its own, to find a slow one.
import {extractSolidity} from '../../../core/extract-sol.ts'
import {conditionsOf, condAt} from '../../../core/extract-check.ts'
import {no, proveSteps} from '../../../core/dsl.ts'
const [file, root] = process.argv.slice(2)
const x = extractSolidity(file!, {root, check: {runs: 2, states: 2, probes: false}})
if (!x.ok) { console.log(JSON.stringify(x.refusals)); process.exit(1) }
const r = x.rule!, conds = conditionsOf(x.model!)
console.log(`${conds.length} conditions`)
for (const [i, c] of conds.entries()) {
  const t0 = performance.now()
  process.stdout.write(`probe ${i + 1}: ${JSON.stringify(c).slice(0, 160)} ... `)
  const law = r.stepLaw(`probe ${i + 1}`, () => no, env => condAt(c, env as Record<string, unknown>))
  const v = proveSteps(r as never, [], [law], {search: false})
  console.log(`${Math.round(performance.now() - t0)} ms, ${v.proven ? 'never' : v.witness ? 'witness' : 'unknown'}`)
}
