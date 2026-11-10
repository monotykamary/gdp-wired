import {strict as assert} from 'node:assert'
import {copyFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
const out = 'ledger-prepared-input'
mkdirSync(out)
for (const name of readdirSync('generator-input')) if (name.endsWith('.ts') || name.endsWith('.source') || name === 'baseline.pack') copyFileSync(join('generator-input', name), join(out, name))
for (const name of readdirSync('ledger-input')) if (name.endsWith('.ts') || ['identity.json', 'candidate.patch'].includes(name)) copyFileSync(join('ledger-input', name), join(out, name))
let text = readFileSync(join(out, 'preflight.ts'), 'utf8')
const replace = (old: string, value: string) => { assert.equal(text.split(old).length, 2, 'unique preflight anchor'); text = text.replace(old, value) }
replace("input=resolve('generator-input')", "input=resolve('ledger-prepared-input')")
const files = ['./core/work-ledger.test.ts', './core/meter.test.ts', './core/work-clock.test.ts', './core/work-entry.test.ts', './core/count-work.test.ts', './core/finite-work.test.ts', './core/counts-completion-order.test.ts', './kernel/work-budget.test.ts']
replace("['targeted',['test','./core/field-laws.test.ts','./core/field-loaded.test.ts','./core/finite-work.test.ts','./core/finite-tiny.test.ts','./core/finite-tiny-houdini.test.ts','./core/support-order.test.ts','./core/counts-completion-order.test.ts','./kernel/model-values.test.ts']]", `['targeted',${JSON.stringify(['test', ...files])}]`)
writeFileSync(join(out, 'preflight.ts'), text)
