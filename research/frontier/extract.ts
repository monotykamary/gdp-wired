// Invariant items from the examples: each law of an example rule proven alone (its sibling laws taken out), and its
// step laws with no law at all. Where that fails, the siblings were the invariant it needs, and the law is a wall item.
// `bun research/frontier/extract.ts` writes walls.json, which invariants.ts reads.
import {writeFileSync} from 'node:fs'
import {domains} from '../../examples/index.ts'
import {proveRule, proveSteps} from '../../core/dsl.ts'

export type Wall = {domain: string, case: string, law?: string, steps?: true, ms: number}
const out: Wall[] = []
for (const d of domains) for (const c of d.cases) {
  if (c.kind !== 'rule') continue
  if (c.laws.length >= 2) for (const law of c.laws) {
    const t = performance.now(), v = proveRule(c.rule, [law], {search: false}), ms = Math.round(performance.now() - t)
    if (!(v.proven && v.checked) && !v.run) out.push({domain: d.domain, case: c.name, law: law.name, ms})
  }
  if (c.steps?.length && c.laws.length) {
    const t = performance.now(), v = proveSteps(c.rule, [], c.steps, {search: false}), ms = Math.round(performance.now() - t)
    if (!(v.proven && v.checked) && !v.run) out.push({domain: d.domain, case: c.name, steps: true, ms})
  }
}
writeFileSync(`${import.meta.dir}/walls.json`, JSON.stringify(out, null, 1) + '\n')
console.log(`${out.length} items`, out.map(w => `${w.domain}/${w.case}: ${w.law ?? 'step laws'}`).join('\n'))
