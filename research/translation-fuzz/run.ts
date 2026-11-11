import {mkdirSync, appendFileSync, writeFileSync} from 'node:fs'
import {dirname, resolve} from 'node:path'
import {FAMILIES, controls} from './model.ts'
const args = process.argv.slice(2)
const option = (name: string, fallback?: string): string => { const i = args.indexOf(name); if (i < 0) { if (fallback !== undefined) return fallback; throw new Error(`missing ${name}`) } return args[i + 1]! }
const api = resolve(option('--api', process.cwd())), output = resolve(option('--out')), seed = Number(option('--seed', '31'))
const count = Number(option('--count', '130')), start = Number(option('--start', '0')), shard = Number(option('--shard', '0')), shards = Number(option('--shards', '1'))
const deadline = Number(option('--case-ms', '15000')), replay = !args.includes('--no-replay'), control = args.includes('--controls'), dist = args.includes('--dist')
if (args.includes('--replay') && args.includes('--no-replay')) throw new Error('conflicting replay options')
for (const n of [seed, count, start, shard, shards, deadline]) if (!Number.isInteger(n) || n < 0) throw new Error('invalid numeric option')
if (!shards || shard >= shards || !deadline || seed > 0xffffffff || start + shard + Math.max(0, count - 1) * shards > 0xffffffff) throw new Error('invalid case range')
mkdirSync(dirname(output), {recursive: true}); writeFileSync(output + '.jsonl', '', {flag: 'wx'})
const generatorHash = new Bun.CryptoHasher('sha256').update(await Bun.file(resolve(import.meta.dir, 'model.ts')).arrayBuffer()).digest('hex')
const summary = {api, seed, start, count, shard, shards, generatorHash, replay: replay ? 'default' : 'disabled', generatorFamilies: [...FAMILIES], generated: 0, extracted: 0, proven: 0, kernelProven: 0, nativeCheckedRows: 0, findings: 0, blockedFindings: 0, modelFindings: 0, falseRejections: 0, unsafeVerdicts: 0, unknown: 0, refused: 0, notProven: 0, errors: 0, timeouts: 0, families: {} as Record<string, number>, tags: {} as Record<string, number>, acceptedTags: {} as Record<string, number>, provenTags: {} as Record<string, number>, nontrivialProvenTags: {} as Record<string, number>}
const selections = args.includes('--control') ? [`control:${option('--control')}`] : control ? Object.keys(controls()).map(k => `control:${k}`) : Array.from({length: count}, (_, i) => String(start + shard + i * shards))
for (const index of selections) {
  const child = Bun.spawn(['bun', resolve(import.meta.dir, 'worker.ts'), api, String(seed), index, replay ? 'replay' : 'disabled', dist ? 'dist' : 'source'], {cwd: api, stdout: 'pipe', stderr: 'pipe', env: {...process.env, GDP_CYCLIC_LOG: '0'}})
  let expired = false
  const timer = setTimeout(() => { expired = true; child.kill('SIGKILL') }, deadline)
  const [status, stdout, stderr] = await Promise.all([child.exited, new Response(child.stdout).text(), new Response(child.stderr).text()]); clearTimeout(timer)
  const line = stdout.split('\n').findLast(s => s.startsWith('FUZZ_CASE '))
  if (status !== 0 || !line) {
    summary.errors++; if (expired) summary.timeouts++
    const row = {seed, index, error: expired ? 'timeout' : 'worker-failed', status, stdout, stderr}
    appendFileSync(output + '.jsonl', JSON.stringify(row) + '\n'); console.log('FUZZ_ERROR ' + JSON.stringify(row)); continue
  }
  const row = JSON.parse(line.slice(10)); appendFileSync(output + '.jsonl', JSON.stringify(row) + '\n')
  if (args.includes('--emit-cases')) console.log('FUZZ_CASE ' + JSON.stringify(row))
  summary.generated++; if (row.extracted) { summary.extracted++; for (const tag of row.tags) summary.acceptedTags[tag] = (summary.acceptedTags[tag] ?? 0) + 1 }
  summary.families[row.family] = (summary.families[row.family] ?? 0) + 1
  for (const tag of row.tags) summary.tags[tag] = (summary.tags[tag] ?? 0) + 1
  for (const law of row.laws) {
    if (law.native) { summary.kernelProven++; summary.nativeCheckedRows += law.native.checked }
    if (law.status === 'FINDING' || law.status === 'proven-native-valid') {
      summary.proven++
      for (const tag of row.tags) { summary.provenTags[tag] = (summary.provenTags[tag] ?? 0) + 1; if (law.nontrivial) summary.nontrivialProvenTags[tag] = (summary.nontrivialProvenTags[tag] ?? 0) + 1 }
    }
    if (law.status === 'FINDING') summary.findings++
    else if (law.status === 'BLOCKED_FINDING') summary.blockedFindings++
    else if (law.status === 'MODEL_FINDING') summary.modelFindings++
    else if (law.status === 'FALSE_REJECTION') summary.falseRejections++
    else if (law.status === 'UNSAFE_VERDICT') summary.unsafeVerdicts++
    else if (law.status === 'unknown') summary.unknown++
    else if (law.status === 'law-refused') summary.refused++
    else if (law.status === 'not-proven') summary.notProven++
    if (['FINDING', 'BLOCKED_FINDING', 'MODEL_FINDING', 'FALSE_REJECTION', 'UNSAFE_VERDICT'].includes(law.status)) console.log('FUZZ_' + law.status + ' ' + JSON.stringify({id: row.id, family: row.family, source: row.source, law, replay: row.replay}))
  }
  console.log('FUZZ_PROGRESS ' + JSON.stringify({id: row.id, generated: summary.generated, proven: summary.proven, findings: summary.findings, blocked: summary.blockedFindings, errors: summary.errors}))
}
writeFileSync(output + '.summary.json', JSON.stringify(summary, null, 2) + '\n'); console.log('FUZZ_SUMMARY ' + JSON.stringify(summary))
if (summary.findings && args.includes('--expect-clean')) console.error('error: UNSOUND source translation: a default source proof is natively false')
if (summary.falseRejections || summary.unsafeVerdicts) console.error('error: COVERAGE source cross-check disagrees with the independent oracle or its verdict contract')
if (summary.errors > summary.timeouts) console.error('error: COVERAGE translation worker failed')
else if (summary.timeouts) console.error('error: Test timed out after the translation case deadline')
if (summary.errors || summary.falseRejections || summary.unsafeVerdicts || args.includes('--expect-clean') && summary.findings) process.exitCode = 1
