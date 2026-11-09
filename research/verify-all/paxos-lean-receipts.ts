// Validate terminal evidence only; never search for or replace a certificate.
import {readFileSync, writeFileSync, mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const root = process.argv[2] ?? 'evidence'
const read = (p: string) => readFileSync(p, 'utf8')
const sha = (s: string) => createHash('sha256').update(s).digest('hex')
function requireThat(ok: unknown, message: string): asserts ok { if (!ok) throw Error(message) }
const batch = join(root, 'paxos-lean-recheck')
const summary = read(join(batch, 'summary.tsv')).trim().split('\n').map(s => s.split('\t'))
requireThat(summary.length === 3 && new Set(summary.map(r => r[0])).size === 3, 'incomplete batch')
for (const row of summary) requireThat(row[1] === '0' && row[3] === 'boat', 'non-successful boat receipt: ' + row.join(' '))
const combined = read(join(batch, 'combined.log')), probe = read(join(batch, 'law12-probe.log')), census = read(join(batch, 'census.log'))
function record(text: string, prefix: string): any {
  const line = text.split('\n').find(s => s.startsWith(prefix + ' '))
  requireThat(line, 'missing record ' + prefix)
  return JSON.parse(line.slice(prefix.length + 1))
}
function records(text: string, prefix: string): any[] {
  return text.split('\n').filter(s => s.startsWith(prefix + ' ')).map(s => JSON.parse(s.slice(prefix.length + 1)))
}
for (const text of [combined, probe]) requireThat(!/\berror:|sorryAx|uses 'sorry'/.test(text), 'Lean error or placeholder in terminal output')
const inputs = record(combined, 'COMBINED_INPUTS')
requireThat(inputs.originalSha256 === 'e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1', 'changed original export')
for (const name of ['paxos_row_alpha','paxos_reach_alpha','paxos_alpha_entry12_accepted','paxos_alpha_start12','paxos_alpha_step12','paxos_alpha_whole_rejected','paxos_alpha_step20_rejected','first_original_rejected','root_no_original_rejected','first_source_inconsistent','combined_paxos_check','combined_original_laws']) {
  requireThat(combined.includes("'" + name + "'"), 'missing checked theorem ' + name)
}
requireThat(combined.includes('("SAME_FULL_HYPOTHESES", true)') && combined.includes('("LEAN_BAD_LEAVES", [[true, true, true, true, false], [false]])') && combined.includes('("ADAPTED_TREE_CONTROL", true)'), 'localization changed')
const work = mkdtempSync(join(tmpdir(), 'paxos-receipts-'))
const packed = combined.match(/COMBINED_ARTIFACT_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nCOMBINED_ARTIFACT_END/)
requireThat(packed, 'missing generated Lean artifact')
writeFileSync(join(work, 'combined.tar.xz'), Buffer.from(packed[1]!, 'base64'))
const tar = spawnSync('tar', ['-xJf', join(work, 'combined.tar.xz'), '-C', work], {encoding: 'utf8', timeout: 30000})
requireThat(tar.status === 0, 'cannot extract Lean artifact: ' + tar.stderr)
const lean = read(join(work, 'paxos-soundness-combined.lean'))
requireThat(sha(lean) === inputs.combinedSha256 && !/\bsorry\b|\badmit\b|native_decide/.test(lean), 'invalid combined artifact')
requireThat(!lean.includes('theorem verified_check :'), 'original rejected safety theorem imported')
const trials = records(probe, 'PROOF_SEARCH'), runs = records(probe, 'INTERPRETER_LAW'), reuse = records(probe, 'REUSED_POSITIVE_CERT')
requireThat(trials.length === 24 && trials.filter(t => t.accepted).length === 2, 'unexpected probe count')
requireThat(trials.filter(t => t.accepted).every(t => t.kind === 'bounded' && t.strategy === 'both'), 'unexpected acceptance')
requireThat(trials.filter(t => t.kind !== 'bounded').length === 16 && trials.filter(t => t.kind !== 'bounded').every(t => !t.accepted), 'accepted false control')
requireThat(runs.length === 6 && runs.every(r => JSON.stringify(r.values) === (r.kind === 'bounded' ? '[true,true,true]' : '[true,false,true]')), 'interpreter results changed')
requireThat(reuse.length === 4 && reuse.every(r => !r.accepted), 'reused positive certificate accepted false law')
const rows = records(census, 'CENSUS_ROW'), totals = record(census, 'CENSUS_SUMMARY')
requireThat(rows.length === 29 && sha(JSON.stringify(rows)) === totals.censusSha256, 'census integrity')
const others = rows.filter(r => r.accepted && r.id !== 'paxos_epr')
requireThat(others.length === 27 && others.every(r => r.leanChecked && !r.scanPrefixFurtherKeys.length && !r.carryCoWrite.length) && totals.otherCollisions.length === 0, 'census feature conclusion changed')
for (const r of rows) requireThat(sha(read(join(root, r.receipt))) === r.receiptSha256, 'changed underlying receipt ' + r.id)
const originalCensus = read(join(root, 'paxos-feature-census/paxos-feature-census.log'))
requireThat(totals.censusSha256 === record(originalCensus, 'CENSUS_SUMMARY').censusSha256, 'inherited census did not reproduce')
const inheritedTreeLog = read(join(root, 'paxos-law20-terminal/paxos-law20-validate.log'))
requireThat(sha(inheritedTreeLog) === '17ce685be65380ae37a1b086168b8e6017bf4773f742a417e8b41b38af4aa5e1', 'inherited tree receipt identity')
requireThat(inheritedTreeLog.includes('TS_NODE_COUNT 73 TS_LEAF_COUNT 37 TS_FAILED_NODES []'), 'TS traversal missing')
for (const [text, count] of [[combined, 2], [probe, 1]] as const) {
  const walls = text.match(/^LEAN_WALL .+$/gm) ?? []
  requireThat(walls.length === count && walls.every(w => w.endsWith('exit=0')), 'missing successful Lean subprocess')
}
const manifest = {
  baseline: 'e11165280a1bab4944a692a64ab1554e5f53c82e', summary,
  logSha256: {combined: sha(combined), probe: sha(probe), census: sha(census), inheritedTree: sha(inheritedTreeLog)},
  combined: inputs,
  leanWall: {combined: combined.match(/^LEAN_WALL .+$/gm), probe: probe.match(/^LEAN_WALL .+$/gm)},
  law12: {trials: 24, acceptedTrueLaws: 2, falseLawTrialsRejected: 16, reusedProofsRejected: 4, interpreter: runs},
  census: {totals, otherCertificates: others.map(r => ({id:r.id, otherFurtherKeys:r.otherFurtherKeys.length, packetSha256:r.packetSha256, leanSha256:r.leanSha256, receipt:r.receipt, receiptSha256:r.receiptSha256}))}
}
console.log('PAXOS_RECEIPT_BEGIN\n' + JSON.stringify(manifest, null, 2) + '\nPAXOS_RECEIPT_END')
console.log('PAXOS_RECEIPT_SHA256 ' + sha(JSON.stringify(manifest, null, 2)))
