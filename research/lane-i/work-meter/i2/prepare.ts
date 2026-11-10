import {strict as assert} from 'node:assert'
import {copyFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

const out = 'i2-prepared-input'
mkdirSync(out)
for (const name of readdirSync('generator-input')) if (name.endsWith('.ts') || name.endsWith('.source') || name === 'baseline.pack') copyFileSync(join('generator-input', name), join(out, name))
for (const name of ['identity.json', 'candidate.patch', 'prepare.ts']) copyFileSync(join('i2-input', name), join(out, name))
let text = readFileSync(join(out, 'preflight.ts'), 'utf8')
const replace = (old: string, value: string) => { assert.equal(text.split(old).length, 2, 'unique preflight anchor'); text = text.replace(old, value) }
replace("input=resolve('generator-input')", "input=resolve('i2-prepared-input')")
replace("['targeted',['test','./core/field-laws.test.ts','./core/field-loaded.test.ts','./core/finite-work.test.ts','./core/finite-tiny.test.ts','./core/finite-tiny-houdini.test.ts','./core/support-order.test.ts','./core/counts-completion-order.test.ts','./kernel/model-values.test.ts']]", "['targeted',['test','./core/meter.test.ts','./core/compile.test.ts','./core/sample-step.test.ts','./core/runtime-keys.test.ts','./core/small-counts.test.ts','./core/values.test.ts','./core/functions.test.ts','./kernel/model-values.test.ts']]")
writeFileSync(join(out, 'preflight.ts'), text)
