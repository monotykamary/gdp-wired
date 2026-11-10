import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
import {stripVTControlCharacters} from 'node:util'

const version = process.argv[3] ?? '1'; assert(['1', '2'].includes(version))
const resultDir = process.argv[2] ?? 'meter-results'
const cfg = JSON.parse(readFileSync(version === '2' ? 'meter-input/identity-v2.json' : 'meter-input/identity.json', 'utf8'))
const profiles = ['plain', 'zero', 'double', 'random']
const rows: any[] = []
const sha = (text: string) => createHash('sha256').update(text).digest('hex')
const prefixed = (text: string, tag: string) => text.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
const clean = stripVTControlCharacters
for (const mode of profiles) {
  const text = readFileSync(`${resultDir}/kernel-meter-${mode}.log`, 'utf8')
  const sources = prefixed(text, 'GENERATOR_SOURCE'), unchanged = prefixed(text, 'GENERATOR_UNCHANGED')
  assert.equal(sources.length, 1); assert.equal(unchanged.length, 1)
  assert.equal(sources[0].candidate, cfg.candidate)
  assert.deepEqual(sources[0].blobs, cfg.expectedCandidateBlobs)
  assert.equal(unchanged[0].production, true)
  const checks = prefixed(text, 'GENERATOR_CHECK'), traces = new Map<string, string>()
  assert.equal(new Set(checks.map(r => r.label)).size, checks.length, 'duplicate check label')
  for (const record of checks) {
    assert.equal(record.exit, 0, mode + ':' + record.label); assert.equal(record.signal, null)
    const raw = gunzipSync(Buffer.from(record.traceGzipBase64, 'base64')).toString()
    const separator = '\n---stderr---\n', index = raw.indexOf(separator); assert(index >= 0)
    assert.equal(sha(raw.slice(0, index)), record.stdoutSha256)
    assert.equal(sha(raw.slice(index + separator.length)), record.stderrSha256)
    traces.set(record.label, clean(raw))
  }
  for (const label of ['meter-audit', 'targeted', 'roster', 'decoder']) assert(traces.has(label), label)
  const ast = prefixed(traces.get('meter-audit')!, 'KERNEL_METER_AST_AUDIT')
  assert.equal(ast.length, 2)
  assert(ast.every(r => r.incrementsOnly && r.readMutationRefused && r.semanticMutationDetected && r.writes > 0))
  if (version === '2') assert(ast.every(r => r.counterResultMutationRefused), 'counter-result branch audit required')
  const target = traces.get('targeted')!, preload = prefixed(target, 'KERNEL_METER_PRELOAD'), mutation = prefixed(target, 'KERNEL_METER_MUTATION')
  assert(preload.length > 0 && preload.every(r => r.mode === mode && r.installed), 'missing preload receipt')
  assert(mutation.length > 0 && mutation.every(r => r.mode === mode), 'missing Bun hook receipts')
  const exercised = mutation.filter(r => r.exercised); assert(exercised.length > 0, 'meter mutation was not exercised')
  const cases: string[] = []
  let file = ''
  for (const line of target.split('\n')) {
    if (line.trim().endsWith('.test.ts:')) file = line.trim()
    if (line.startsWith('(pass) ') || line.startsWith('(skip) ')) cases.push(file + line.replace(/ \[[0-9.]+m?s\]$/, ''))
  }
  assert(cases.length > 0)
  assert(/\b0 fail\b/.test(target))
  const pass = Number(target.match(/\b(\d+) pass\b/)?.[1]), assertions = Number(target.match(/\b(\d+) expect\(\) calls\b/)?.[1])
  assert.equal(pass, 262, 'complete frozen kernel/refusal test selection')
  for (const field of ['tableCells', 'checkSteps']) assert(Number.isFinite(exercised.at(-1).values[field]))
  if (mode === 'zero') assert.deepEqual(exercised.at(-1).values, {tableCells: 0, checkSteps: 0})
  if (mode === 'plain') {
    assert(traces.has('type-lint'))
    assert(traces.get('type-lint')!.includes('Found 0 warnings and 0 errors.'))
  }
  rows.push({mode, cpu: sources[0].cpu, pass, assertions, cases: cases.sort(), caseHash: sha(JSON.stringify(cases.sort())), ast, mutation: exercised.at(-1), hookReceipts: mutation.length})
}
for (const row of rows.slice(1)) assert.deepEqual(row.cases, rows[0].cases, 'acceptance/refusal test vector changed')
console.log('KERNEL_METER_RECEIPT_AUDIT ' + JSON.stringify({candidate: cfg.candidate, profiles: rows.map(({cases: _cases, ...row}) => row), sameTestVector: true, sourceUnchanged: true, scope: 'existing test expectations under meter mutations; not Lane D 28-certificate audit, complete accounting, weights, or W'}))
