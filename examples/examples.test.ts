// The examples' triple check (harness.ts), one test per domain: the kernel proves every law and refuses every broken
// variant, random runs of both runtimes keep every law and break every broken variant. DOMAIN picks one domain (and
// imports only its file), EXAMPLES_SCALE multiplies the runs. Lean checks the same trees in lean-kernel
// (export-kernel.ts --examples).
import {expect, test} from 'bun:test'
import {type Domain, checkCase} from './harness.ts'

const only = process.env.DOMAIN, scale = Number(process.env.EXAMPLES_SCALE ?? 1)
const domains: Domain[] = only ? [((await import(`./domains/${only}.ts`)) as {domain: Domain}).domain] : (await import('./index.ts')).domains
for (const d of domains) {
  test(`${d.domain}: ${d.about}`, () => {
    const findings = d.cases.flatMap(c => checkCase(c, scale))
    for (const f of findings) console.log(`${f.ok ? 'ok  ' : 'FAIL'} ${d.domain} / ${f.case} / ${f.item} / ${f.check}: ${f.detail.slice(0, 220)}`)
    const failed = findings.filter(f => !f.ok)
    expect(failed.map(f => `${f.case} / ${f.item} / ${f.check}: ${f.detail}`)).toEqual([])
    console.log(`${d.domain}: ${d.cases.length} cases, ${findings.length} checks, all passed`)
  }, 1_800_000)
}
