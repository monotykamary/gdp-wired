// Small-log reconciliation only; large archives remain on boat.
import {strict as assert} from 'node:assert'
import {existsSync, readFileSync, writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {join, basename} from 'node:path'
import {createHash} from 'node:crypto'
const dir = process.argv[2]
if (!dir) throw Error('BATCH_OUTPUT required')
const names = ['p1-ab', 'p1-ba', 'rows-ab', 'rows-ba', 'star-ab', 'star-ba']
const placement = JSON.parse(readFileSync(join(dir, 'placement.json'), 'utf8'))
const exits = new Map(readFileSync(join(dir, 'summary.tsv'), 'utf8').trim().split('\n').map(line => { const [name, code] = line.split('\t'); return [name, Number(code)] }))
const rows = names.map(name => {
  assert.equal(exits.get(name), 0, name)
  const path = join(dir, name + (existsSync(join(dir, name + '.log')) ? '.log' : '.log.gz'))
  const bytes = readFileSync(path), text = (path.endsWith('.gz') ? gunzipSync(bytes) : bytes).toString('utf8')
  const arms: any[] = [], audits = new Map<string, any>(), manifests: any[] = []
  let input: string | undefined
  for (const line of text.split('\n')) {
    if (line.startsWith('INPUT=')) { input = basename(line.slice(6)); continue }
    let r: any
    try { r = JSON.parse(line) } catch { continue }
    if (r.side === 'before' || r.side === 'after') arms.push(r)
    else if (r.artifact === 'track-m-tar-v1') manifests.push(r)
    else if (r.conditional === true) { assert(input); assert(!audits.has(input)); audits.set(input, r); input = undefined }
  }
  assert.equal(arms.length, 2, name); assert.equal(audits.size, 2, name)
  assert.deepEqual(arms.map(a => a.side), name.endsWith('-ab') ? ['before', 'after'] : ['after', 'before'])
  const cpu = placement[name]
  assert(cpu.exclusive); assert.equal(cpu.co_tenants, 0); assert.equal(cpu.vcpus, 8)
  for (const arm of arms) {
    assert(arm.conditional && arm.generatorOnly); assert.deepEqual(arm.suppliedLaws, []); assert.equal(arm.familySize, 34)
    assert.equal(arm.budget, 6000); assert.equal(arm.wallAllowance, 7000); assert.deepEqual(arm.passOrder, [1, 0])
    const audit = audits.get(`${arm.tag}-${arm.side}.json.gz`); assert(audit)
    assert(audit.familyVerified && audit.originalHarness)
    for (const key of ['tag', 'law', 'checked', 'units', 'wallMs', 'results']) assert.deepEqual(audit[key], arm[key], `${name}: ${key}`)
  }
  const before = arms.find(a => a.side === 'before')!, after = arms.find(a => a.side === 'after')!
  return {name, cpu, logSha256: createHash('sha256').update(text).digest('hex'), archive: manifests.at(-1),
    arms: arms.map(({side, tag, law, checked, units, wallMs, withinDiagnosticLine, results}) => ({side, tag, law, checked, units, wallMs, withinDiagnosticLine, results, originalFamilyVerified: true})),
    unitDelta: after.units - before.units, wallDeltaMs: after.wallMs - before.wallMs}
})
const out = {conditional: true, standalone: true, gateGreen: false, validationExit: exits.get('check'), source: 'b056c3b4', control: 'a4dc71d0', rows,
  independentAudit: {outcomes: rows.length * 2, checked: rows.flatMap(r => r.arms).filter(a => a.checked).length}}
writeFileSync(join(dir, 'summary.json'), JSON.stringify(out, null, 2) + '\n')
console.log(JSON.stringify({validationExit: out.validationExit, audit: out.independentAudit, rows: rows.map(({name, unitDelta, arms}) => ({name, unitDelta, arms: arms.map(({side, checked, units, wallMs}) => ({side, checked, units, wallMs}))}))}, null, 2))
