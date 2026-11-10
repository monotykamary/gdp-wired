// Run on Boat with a JSON map from control id to its untouched parent/release root.
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {pathToFileURL} from 'node:url'
import {parse} from '../../core/laws.ts'
import {nativeLaw} from '../../core/native-law.ts'
import {attachNativeLaw, attachSource, translationVerdict} from '../../core/source-check.ts'
import {sourceDiagnostic} from '../../core/source-diagnostic.ts'
import {nativeCounterexample, sourceControls} from './source-crosscheck-cases.ts'

const roots = JSON.parse(readFileSync(process.argv[2]!, 'utf8')) as Record<string, string>
const rows: unknown[] = []
for (const c of sourceControls) {
  const witness = nativeCounterexample(c)
  if (c.holds(witness.result, witness.args)) throw new Error(`${c.id}: the native positive control is not false`)
  const root = roots[c.id]
  if (!root) throw new Error(`${c.id}: no untouched historical root`)
  const core = join(root, c.revision === '0.47.0' ? 'dist/core' : 'core'), extension = c.revision === '0.47.0' ? 'js' : 'ts'
  // Keep each historical Rule/Kind module graph intact. Mixing its Rule with the
  // current graph's codec can itself create a conformance mismatch. Only add the
  // current replay instrumentation; never copy an extractor, law translator or prover.
  const untouched = ['extract', 'extract-read', 'extract-shapes', 'laws', 'dsl'].map(name => {
    const path = join(core, `${name}.${extension}`)
    return [path, readFileSync(path, 'utf8')] as const
  })
  let instrumented = readFileSync(new URL('../../core/extract-check.ts', import.meta.url), 'utf8')
    .replace("'./source-check.ts'", JSON.stringify(new URL('../../core/source-check.ts', import.meta.url).href))
    .replace("'./native-domain.ts'", JSON.stringify(new URL('../../core/native-domain.ts', import.meta.url).href))
  if (extension === 'js') instrumented = new Bun.Transpiler({loader: 'ts'}).transformSync(instrumented.replace(/from '(\.\/[^']+)\.ts'/g, "from '$1.js'"))
  writeFileSync(join(core, `extract-check.${extension}`), instrumented)
  const load = (name: string) => import(pathToFileURL(join(core, `${name}.${extension}`)).href)
  const replayModule = await load('extract-check') as typeof import('../../core/extract-check.ts')
  const replay = replayModule.check
  const oldExtract = await load('extract') as typeof import('../../core/extract.ts')
  const oldLaws = await load('laws') as typeof import('../../core/laws.ts')
  const oldDsl = await load('dsl') as typeof import('../../core/dsl.ts')
  const x = oldExtract.extract(c.source, {file: `${c.id}.ts`, entry: c.entry, ...(c.standalone ? {mode: 'standalone' as const} : {}), check: {runs: 0, states: 0, probes: false}})
  if (!x.ok) throw new Error(`${c.id}: historical source unexpectedly refused: ${JSON.stringify(x.refusals)}`)
  const law = oldLaws.buildLaw(x, {name: c.id, expr: c.expr, method: 'decide'}, {clock: 1, calendar: {}})
  const raw = law.kind === 'law' ? oldDsl.proveRule(x.rule!, [...x.invariants ?? [], law.law], {search: false}) : oldDsl.proveSteps(x.rule!, x.invariants ?? [], [law.law], {search: false})
  if (!(raw.proven && raw.checked)) throw new Error(`${c.id}: historical kernel false proof did not reproduce: ${JSON.stringify(raw)}`)
  const evaluate = nativeLaw(parse(c.expr), {clock: 1, calendar: {}}, parse, x.consts, new Set(x.names?.map(n => n.code.split('.')[0]!)))
  attachNativeLaw(x.rule!, law.law, c.id, 'decide', evaluate)
  const evidence = replay(c.source, `${c.id}.ts`, x.model!, x.rule!, x.sorts!)
  if (evidence.harness || evidence.source || evidence.mismatch?.includes("doesn't load")) throw new Error(`${c.id}: replay adapter failed: ${JSON.stringify(evidence)}`)
  if (['B1', 'P1'].includes(c.id) && evidence.mismatch) throw new Error(`${c.id}: this control must pass rule replay before the native law check: ${evidence.mismatch}`)
  attachSource(x.rule!, evidence, x.invariants ?? [])
  const verdict = evidence.mismatch ? undefined : translationVerdict(x.rule!, [...x.invariants ?? [], law.law], raw)
  if (!evidence.mismatch && !(verdict?.translation === 'error' && !verdict.proven && !verdict.checked)) throw new Error(`${c.id}: default protection did not detect the false proof: ${JSON.stringify(verdict)}`)
  const disabled = []
  for (const options of [{runs: 0, states: 0, probes: false as const}, {lawCrossCheck: false}]) {
    const uncheckedEvidence = replay(c.source, `${c.id}.ts`, x.model!, x.rule!, x.sorts!, options)
    attachSource(x.rule!, uncheckedEvidence, x.invariants ?? [])
    const v = translationVerdict(x.rule!, [...x.invariants ?? [], law.law], raw)
    if (v.translation !== 'unchecked' || v.proven || v.checked) throw new Error(`${c.id}: disablement was not fail closed`)
    disabled.push({translation: v.translation, proven: v.proven, checked: v.checked})
  }
  if (untouched.some(([path, text]) => readFileSync(path, 'utf8') !== text)) throw new Error(`${c.id}: a specific-fix source file was changed`)
  rows.push({id: c.id, revision: c.revision, untouchedReader: true, replayInstrumentationOnly: true, rawKernel: {proven: raw.proven, checked: raw.checked}, nativeWitness: sourceDiagnostic(witness), defaultRefused: true, route: evidence.mismatch ? 'rule replay' : 'native law', why: evidence.mismatch ?? verdict?.why, disabled})
}
const report = {passed: rows.length === 5, controls: rows}
if (process.argv[3]) writeFileSync(process.argv[3], JSON.stringify(report, null, 2) + '\n')
console.log('HISTORICAL_CONTROLS ' + JSON.stringify(report))
