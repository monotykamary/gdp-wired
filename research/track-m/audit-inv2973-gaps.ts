// Read-only audit of captured Inv2973 packets. No prover, generation, or replay.
import {createHash} from 'node:crypto'
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

const root = process.argv[2] ?? 'runs/track-m'
const output = process.argv[3] ?? join(root, 'inv2973-gap-layout-v1', 'audit.json')
const read = (path: string) => readFileSync(join(root, path), 'utf8')
const hash = (text: string) => createHash('sha256').update(text).digest('hex')
const records = (text: string): any[] => text.split('\n').filter(line => line.startsWith('{')).map(line => JSON.parse(line))
const termKey = (terms: [number, string][]) => JSON.stringify([...terms].sort((a, b) => a[1].localeCompare(b[1])))
const packets = Object.fromEntries(['first', 'all'].map(name => {
  const file = `inv2973-gap-layout-v1/layout-${name}.log`, text = read(file)
  const packet = records(text).find(value => value.reads && value.insts)
  if (!packet) throw new Error(`No packet: ${file}`)
  return [name, {...packet, file, sha256: hash(text)}]
}))
if (JSON.stringify(packets.first.reads) !== JSON.stringify(packets.all.reads)) throw new Error('Read IDs differ between layouts')
const targets: Record<string, [number, string][]> = {
  votersOld: [[1, 'r$8'], [-1, 'r$23']], committedOld: [[1, 'r$9'], [-1, 'r$23']],
  committedSize: [[1, 'r$9'], [-1, 'r$22']], committedBadA: [[1, 'r$9'], [-1, 'r$38']], committedBadB: [[1, 'r$9'], [-1, 'r$40']],
  replaceIntersection: [[1, 'r$4'], [-1, 'r$11']], replaceLeftDifference: [[1, 'r$5'], [-1, 'r$12']], replaceRightDifference: [[1, 'r$6'], [-1, 'r$10']],
  copySizeA: [[1, 'r$0'], [-1, 'r$17']], copySizeB: [[1, 'r$1'], [-1, 'r$17']],
  copyIntersection: [[1, 'r$4'], [-1, 'r$27']], copyLeftDifference: [[1, 'r$5'], [-1, 'r$28']], copyRightDifference: [[1, 'r$6'], [-1, 'r$29']],
  sendIntersection: [[1, 'r$4'], [-1, 'r$24']], sendLeftDifference: [[1, 'r$5'], [-1, 'r$25']], sendRightDifference: [[1, 'r$6'], [-1, 'r$26']],
  copiedOldA: [[1, 'r$2'], [-1, 'r$23']], copiedOldB: [[1, 'r$3'], [-1, 'r$23']],
  unchangedOldA: [[1, 'r$2'], [-1, 'r$15']], unchangedOldB: [[1, 'r$3'], [-1, 'r$16']],
  diagonalLeft: [[1, 'r$5']], diagonalRight: [[1, 'r$6']],
}
const layouts = Object.fromEntries(Object.entries(packets).map(([name, packet]: [string, any]) => [name, {
  file: packet.file, sha256: packet.sha256, reads: packet.reads, insts: packet.insts,
  arities: packet.insts.reduce((out: Record<string, number>, q: any) => {out[q.terms.length] = (out[q.terms.length] ?? 0) + 1; return out}, {}),
  matches: Object.fromEntries(Object.entries(targets).map(([id, terms]) => {
    const match = (wanted: [number, string][]) => packet.insts.flatMap((q: any, index: number) => q.unit === 0 && termKey(q.terms) === termKey(wanted) ? [{index, wit: q.wit}] : [])
    return [id, {terms, forward: match(terms), reverse: match(terms.map(([k, v]) => [-k, v]))}]
  })),
}]))
const files = [0, 1, 5, 6].map(op => `active-source-narrow-v1/overlap-${op}.log`).concat([
  'active-source-resume-v1/overlap-setup.log', 'active-source-resume-v1/overlap-copy.log',
  'source-family-v1/overlap-family-source.log',
])
const captures = files.map(file => {
  const text = read(file)
  return {file, sha256: hash(text), records: records(text).filter(v => v.diagnostic).map(v => {
    const packet = v.instances === packets.first.insts.length ? packets.first : v.instances === packets.all.insts.length ? packets.all : undefined
    const identify = (entry: any) => {
      const q = packet?.insts[entry.index]
      if (q && entry.terms && termKey(q.terms) !== termKey(entry.terms)) throw new Error(`Candidate mismatch: ${file}:${entry.index}`)
      return q && {index: entry.index, wit: q.wit, terms: q.terms, unit: q.unit}
    }
    return {op: v.value, branch: v.branch, checked: v.conditionalChecked, hyps: v.hyps, instances: v.instances,
      failed: v.failed?.map((f: any) => ({...identify(f), queryHyps: f.query?.hyps, outcome: f.query?.outcome, suggested: f.suggestedFromFullGoal})),
      sourceAdditions: v.sourceAdditions,
      tail: v.tail?.filter((e: any) => ['direct-copy', 'count-lemma', 'row-case', 'field-bound-conclusion'].includes(e.stage)).map((e: any) => ({stage: e.stage, ...identify(e), reads: e.reads, proposed: e.proposed, proved: e.proved, rowCase: e.key})),
    }
  })}
})
const input = 'canonical-capture-v1/fixtures/input.json', text = read(input), data = JSON.parse(text)
const result = {kind: 'static-captured-packet-audit', runtime: 'fd2d1dcb', input: {file: input, sha256: hash(text), law: data.laws.find((law: any) => law.name.startsWith('Inv2973')), counts: data.m.counts}, layouts, captures}
writeFileSync(output, JSON.stringify(result, null, 2) + '\n')
console.log(JSON.stringify({output, layouts: Object.fromEntries(Object.entries(layouts).map(([name, layout]: [string, any]) => [name, {reads: layout.reads.length, instances: layout.insts.length, arities: layout.arities}])), captures: captures.reduce((n, c) => n + c.records.length, 0)}))
