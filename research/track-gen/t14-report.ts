// Read complete boat receipts; no solver execution. Each strict run carries its
// actual CPU model, VM, pinning, wrapper exit and harness verdict.
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
const dir = process.argv[2]!, output = process.argv[3]!
const placement = JSON.parse(readFileSync(join(dir, 'placement.json'), 'utf8'))
const cpuByVm = new Map<string, {cpu: string, evidence: string}>()
for (const path of [join(dir, 'placement.json'), ...process.argv.slice(6)]) {
  const receipt = JSON.parse(readFileSync(path, 'utf8'))
  for (const [name, row] of Object.entries(receipt)) {
    const r = row as {cpu?: string, vm?: string}
    if (!r.cpu || !r.vm) continue
    const old = cpuByVm.get(r.vm)
    if (old && old.cpu !== r.cpu) throw Error(`conflicting CPU labels for ${r.vm}`)
    if (!old) cpuByVm.set(r.vm, {cpu: r.cpu, evidence: `${path}#${name}`})
  }
}
const summary = new Map(readFileSync(join(dir, 'summary.tsv'), 'utf8').trim().split('\n').map(l => {const [name, code, seconds, backend] = l.split('\t'); return [name!, {code: Number(code), seconds: Number(seconds), backend}] as const}))
const pairs = readdirSync(dir).filter(f => /^(safe-|duo-|broken-|mldr-pair-|share-pair-).*\.log$/.test(f)).map(file => {
  const name = file.slice(0, -4), text = readFileSync(join(dir, file), 'utf8'), cpu = placement[name]
  const directModel = text.match(/^T14_CPU_MODEL (.+)$/m)?.[1]
  const cpuModel = directModel || cpu?.cpu || cpuByVm.get(cpu?.vm)?.cpu
  const cpuEvidence = directModel ? `${dir}/${file}` : cpu?.cpu ? `${dir}/placement.json#${name}` : cpuByVm.get(cpu?.vm)?.evidence
  const starts = [...text.matchAll(/^PAIR begin side=(\S+) id=(\S+) repeat=(\d+) mode=(\S+)$/gm)]
  const sides = starts.map((start, i) => {
    const part = text.slice(start.index! + start[0].length, starts[i + 1]?.index ?? text.length), side = start[1]!, id = start[2]!, mode = start[4]!
    const json = part.split('\n').find(l => l.startsWith('{"id":'))
    const result = json ? JSON.parse(json) : undefined
    const code = Number(part.match(new RegExp(`PAIR end side=${side} exit=(\\d+)`))?.[1] ?? NaN)
    const seconds = Number(part.match(new RegExp(`STRICT_PROCESS_SECONDS ${side} ([\\d.]+)`))?.[1] ?? NaN)
    const units = part.match(/^T14_TOTAL_WORK (.+)$/m), measured = units ? JSON.parse(units[1]!) : undefined
    const outcome = result?.[mode === 'broken' ? 'broken' : 'search']
    const verdict = code === 0 && seconds <= 60 && !result?.error ? outcome?.verdict ?? 'missing' : code === 137 || code === 124 ? 'killed' : 'error'
    const attempts = [...part.matchAll(/^counts: try (.*?) \| ls (\d+) pass ([01]) ms ([\d.-]+) took ([\d.-]+) wall ([\d.-]+) \[(.*?)\] -> (\S+)$/gm)].map(m => ({law: m[1], laws: Number(m[2]), pass: Number(m[3]), share: Number(m[4]), took: Number(m[5]), wallMs: Number(m[6]), outcome: m[8]}))
    return {side, id, mode, repeat: Number(start[3]), code, seconds, verdict, result, full: outcome?.full ?? measured?.full, work: outcome?.work ?? measured?.work, attempts, cpuModel, cpuEvidence, vm: cpu?.vm, vcpus: cpu?.vcpus, exclusive: cpu?.exclusive, coTenants: cpu?.co_tenants}
  })
  const base = sides.find(s => s.side === 'baseline'), candidate = sides.find(s => s.side === 'candidate')
  const complete = sides.length === 2 && !!base && !!candidate && !!cpuModel && cpu?.exclusive === true && cpu?.co_tenants === 0
  const lost = base?.verdict === 'proven' && candidate?.verdict !== 'proven'
  const wrong = candidate?.mode === 'broken' && candidate?.verdict === 'proven'
  const moved = !!base && !!candidate && (base.verdict !== candidate.verdict || base.full !== candidate.full || base.work !== candidate.work)
  const errors = sides.filter(s => s.verdict === 'error' || s.verdict === 'missing').map(s => s.side)
  const candidateKilled = candidate?.verdict === 'killed' && candidate.mode !== 'broken'
  return {name, receipt: summary.get(name), complete, lost, wrong, moved, errors, candidateKilled, sides}
})
const tests = [...summary].filter(([name]) => name === 'check' || name === 'latest-check' || name.startsWith('tests-')).map(([name, receipt]) => ({name, ...receipt, placement: placement[name]}))
const expectedPairs = Number(process.argv[4] ?? pairs.length), expectedTests = Number(process.argv[5] ?? tests.length)
const result = {dir, expectedPairs, expectedTests, pairs, tests, totals: {pairs: pairs.length, incomplete: pairs.filter(p => !p.complete).length, missingPairs: expectedPairs - pairs.length, missingTests: expectedTests - tests.length, errors: pairs.filter(p => p.errors.length).map(p => p.name), candidateKilled: pairs.filter(p => p.candidateKilled).map(p => p.name), lost: pairs.filter(p => p.lost).length, wrong: pairs.filter(p => p.wrong).length, changed: pairs.filter(p => p.moved).map(p => p.name), failedTests: tests.filter(t => t.code !== 0).map(t => t.name)}}
writeFileSync(output, JSON.stringify(result, null, 2) + '\n')
console.log(JSON.stringify(result.totals, null, 2))
if (result.totals.incomplete || result.totals.missingPairs || result.totals.missingTests || result.totals.errors.length || result.totals.candidateKilled.length || result.totals.lost || result.totals.wrong || result.totals.failedTests.length) process.exitCode = 1
