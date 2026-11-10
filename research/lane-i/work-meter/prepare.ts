import {strict as assert} from 'node:assert'
import {copyFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

const out = 'meter-prepared-input'
mkdirSync(out)
for (const name of readdirSync('generator-input')) if (name.endsWith('.ts') || name.endsWith('.source') || name === 'baseline.pack') copyFileSync(join('generator-input', name), join(out, name))
for (const name of readdirSync('meter-input').filter(name => name.endsWith('.ts') || name === 'identity.json' || name === 'candidate.patch')) copyFileSync(join('meter-input', name), join(out, name))
const version = process.env.METER_CODE_VERSION ?? '1'
assert(['1', '2'].includes(version))
if (version === '2') for (const name of ['identity.json', 'candidate.patch']) copyFileSync(join('meter-input', name.replace('.', '-v2.')), join(out, name))
let text = readFileSync(join(out, 'preflight.ts'), 'utf8')
const replace = (old: string, value: string) => { assert.equal(text.split(old).length, 2, 'unique preflight anchor'); text = text.replace(old, value) }
replace("input=resolve('generator-input')", "input=resolve('meter-prepared-input')")
replace("['targeted',['test','./core/field-laws.test.ts','./core/field-loaded.test.ts','./core/finite-work.test.ts','./core/finite-tiny.test.ts','./core/finite-tiny-houdini.test.ts','./core/support-order.test.ts','./core/counts-completion-order.test.ts','./kernel/model-values.test.ts']]", "['meter-audit',['research/lane-i/generator/meter-audit.ts']],['targeted',['test','--preload','./research/lane-i/generator/meter-mutate.ts','./kernel','./core/solver.test.ts','./core/rationals.test.ts']]")
replace("if(label==='targeted'&&process.argv.includes('--tools-only'))continue;", "if((label==='targeted'&&process.argv.includes('--tools-only'))||(label==='type-lint'&&process.env.METER_MUTATION!=='plain'))continue;")
writeFileSync(join(out, 'preflight.ts'), text)
