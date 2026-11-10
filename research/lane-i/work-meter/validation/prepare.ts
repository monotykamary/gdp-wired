import {strict as assert} from 'node:assert'
import {copyFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
if (process.env.METER_PREPARED !== '1') await import(resolve('recovery-input/materialize.ts'))
if (process.env.METER_COMPOSITION) await import(resolve('recovery-input/compose.ts'))
const out = 'validation-prepared-input'
mkdirSync(out)
for (const name of readdirSync('generator-input')) if (name.endsWith('.ts') || name.endsWith('.source') || name === 'baseline.pack') copyFileSync(join('generator-input', name), join(out, name))
for (const name of readdirSync('validation-input')) if (name.endsWith('.ts') || ['identity.json', 'candidate.patch'].includes(name)) copyFileSync(join('validation-input', name), join(out, name))
let text = readFileSync(join(out, 'preflight.ts'), 'utf8')
const replace = (old: string, value: string) => { assert.equal(text.split(old).length, 2, 'unique preflight anchor'); text = text.replace(old, value) }
replace("input=resolve('generator-input')", "input=resolve('validation-prepared-input')")
replace("resolve('research/verify-all/final-gate-common.ts')", "resolve('recovery-input/final-gate-common.ts')")
replace("resolve('frozen/driver/resource-run.ts')", "resolve('recovery-input/driver/resource-run.ts')")
replace("resolve('frozen/gate-inputs')", "resolve('recovery-input')")
const mutated = process.env.METER_MUTATION && process.env.METER_MUTATION !== 'plain'
const files = mutated ? ['./kernel', './core/solver.test.ts', './core/rationals.test.ts'] : ['./core/meter-complete.test.ts', './core/meter.test.ts', './core/compile.test.ts', './core/sample-step.test.ts', './core/runtime-keys.test.ts', './core/small-counts.test.ts', './core/values.test.ts', './core/functions.test.ts', './kernel/model-values.test.ts', './core/count-cubes.test.ts', './core/count-support.test.ts', './core/finite-tiny-houdini.test.ts', './core/finite-work.test.ts', './core/infer.test.ts', './kernel/steplaw.test.ts']
if (process.env.METER_COMPOSITION) files.push('./core/work-ledger.test.ts', './core/work-clock.test.ts', './core/work-entry.test.ts', './core/count-work.test.ts', './kernel/work-budget.test.ts')
if (process.env.METER_COMPOSITION === 'bitmap') files.push('./core/bitsets.test.ts', './core/bitsets-meter.test.ts')
const args = mutated ? ['test', '--preload', './research/lane-i/generator/meter-mutate.ts', ...files] : ['test', ...files]
replace("['targeted',['test','./core/field-laws.test.ts','./core/field-loaded.test.ts','./core/finite-work.test.ts','./core/finite-tiny.test.ts','./core/finite-tiny-houdini.test.ts','./core/support-order.test.ts','./core/counts-completion-order.test.ts','./kernel/model-values.test.ts']]", `['meter-audit',['research/lane-i/generator/meter-audit.ts']],['targeted',${JSON.stringify(args)}]`)
if (mutated) replace("if(label==='targeted'&&process.argv.includes('--tools-only'))continue;", "if(label==='type-lint')continue;")
writeFileSync(join(out, 'preflight.ts'), text)
