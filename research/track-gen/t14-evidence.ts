// Format existing checked receipts; this does not run a prover.
import {readFileSync, writeFileSync} from 'node:fs'
type Side = {side: string, id: string, verdict: string, full?: number, work?: number, seconds: number, cpuModel: string, cpuEvidence: string, vm: string}
type Pair = {name: string, moved: boolean, sides: Side[]}
const read = (path: string): {pairs: Pair[]} => JSON.parse(readFileSync(path, 'utf8'))
const gate = read('runs/t14-gate-summary.json'), confirmations = read('runs/t14-final-summary.json'), capture = read('runs/t14-capture-summary.json')
const pairs = [...gate.pairs, ...confirmations.pairs, ...capture.pairs], cpus = [...new Set(pairs.flatMap(p => p.sides.map(s => s.cpuModel)))].sort()
if (cpus.some(c => !c)) throw Error('missing CPU model')
const rows = ['# T-14 lane-local iteration evidence (before Section 16)', '', 'Not a Lane D one-command final-gate receipt; this evidence alone does not authorize a merge.', '', 'Implementation: `1681e8e5` plus the test-only deterministic packed-domain route check.', 'Baseline: `b788e195`. All original-harness verdicts use `--ms 60000` under `timeout -s KILL 60`.', '', '## Verdicts', '', '- IC3Syn: 28/28 already-proven protocols retained in each of three paired repeats; MLDR unknown on both sides.', '- DuoAI: 10/10 proven on both sides in each of three repeats.', '- Broken variants: none proven; 11 refuted, 17 unknown, one strict kill on each side.', '- Generation: 87 pairs, zero solver queries, all other 28 canonical lists identical x3; MLDR 34 to 35.', '- Tests: six shards pass in `t14-gate-v1`; the repaired shard 2 and type/lint/commitlint pass in `t14-capture-v2`.', '- Quick bar: `t14-bar/runs/t14-post-recovery/REPORT.md`: wrong 0 and solid losses 0; three non-solid CHC losses remain reported there.', '', '## Every changed counted-work row', '', '`full` is the harness raw weighted counter; `work` is its scalar work counter. These are not wall seconds.', 'The JSON summaries retain full precision, complete harness outcomes, helper attempts, and CPU provenance.', '', '| pair | baseline full | candidate full | baseline work | candidate work | verdicts |', '| --- | ---: | ---: | ---: | ---: | --- |']
for (const p of gate.pairs.filter(p => p.moved).sort((a, b) => a.name.localeCompare(b.name))) {
  const b = p.sides.find(s => s.side === 'baseline')!, c = p.sides.find(s => s.side === 'candidate')!
  rows.push(`| ${p.name} | ${b.full ?? 'n/a'} | ${c.full ?? 'n/a'} | ${b.work ?? 'n/a'} | ${c.work ?? 'n/a'} | ${b.verdict} / ${c.verdict} |`)
}
rows.push('', '## CPU model for every strict pair', '', 'Each pair ran on one isolated pinned large VM. CPU labels missing after scheduler recovery were recovered only from another receipt with the identical VM ID; each JSON side records that source.', '')
cpus.forEach((cpu, i) => rows.push(`- C${i + 1}: ${cpu}`))
for (const [label, data] of [['Full gate', gate], ['T-14 and fixed-share controls', confirmations], ['Corrected research capture', capture]] as const) {
  rows.push('', `### ${label}`, '', '| pair | VM | CPU | baseline seconds | candidate seconds |', '| --- | --- | --- | ---: | ---: |')
  for (const p of data.pairs.sort((a, b) => a.name.localeCompare(b.name))) {
    const b = p.sides.find(s => s.side === 'baseline')!, c = p.sides.find(s => s.side === 'candidate')!
    if (b.vm !== c.vm || b.cpuModel !== c.cpuModel) throw Error(`unpaired hardware: ${p.name}`)
    rows.push(`| ${p.name} | ${c.vm} | C${cpus.indexOf(c.cpuModel) + 1} | ${b.seconds} | ${c.seconds} |`)
  }
}
writeFileSync('runs/T14-GATE.md', rows.join('\n') + '\n')
console.log(JSON.stringify({path: 'runs/T14-GATE.md', changedProtocols: [...new Set(gate.pairs.filter(p => p.moved).map(p => p.sides[0]!.id))].sort(), strictPairs: pairs.length}, null, 2))
