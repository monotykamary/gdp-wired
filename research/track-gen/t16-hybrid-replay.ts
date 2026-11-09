// Iteration-only receipt replay. This is NOT final-gate admission tooling.
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {type Law, type Machine, type Request, type State, interpret} from '../../core/machine.ts'
import {finiteEvaluator} from '../../core/finite-houdini.ts'
import {withWall} from '../../kernel/prove.ts'
import {mldr} from '../protocols/ic3syn/mldr.ts'

type EncodedState = {scalars: Record<string, number>, maps: Record<string, [number, number][]>}
type Drop = {stage: number, round: number, ms: number, law: string, pre: EncodedState, request: Record<string, number | [number, number][]>}
type Result = {mode: string, initial: number, drops: Omit<Drop, 'pre' | 'request'>[], timedOut: boolean, wall: number, removed: number, survivors: number}
const dir = process.argv[2] ?? 'hybrid-data', input = process.argv[3] ?? 'tiny-data/0.json'
const raw = readFileSync(input), inputHash = createHash('sha256').update(raw).digest('hex')
if (inputHash !== '96ba906a86c7f54db1371cea2c55c0bbcc79fd9e8ebe368b770f6495a9ee4496') throw Error('frozen input changed')
const capture = JSON.parse(raw.toString()) as {beforeFinite: {machine: Machine, caller: Law[], candidates: Law[]}, finiteDrops: {round: number, law: Law, params: Record<string, number>, pre: EncodedState, request: Drop['request']}[]}
const {machine, caller, candidates} = capture.beforeFinite, source = mldr().machine
const run = interpret(source), evaluate = finiteEvaluator(machine), params = {size: 3}
const declarations: Law[] = [...machine.facts ?? [], ...(machine.pre ? [{name: 'pre', holds: machine.pre}] : [])]
const decode = (pre: EncodedState): State => ({scalars: pre.scalars, maps: Object.fromEntries(Object.entries(pre.maps).map(([k, v]) => [k, new Map(v)]))})
const request = (value: Drop['request']): Request => Object.fromEntries(Object.entries(value).map(([k, v]) => [k, Array.isArray(v) ? new Map(v) : v]))
const seven = ['CV at most 2', 'inX: no quorum canVote/1', 'inX: stored guard reconfigs/inS', ...[0, 1, 2, 3].map(i => `inX: stored guard reconfigs/inS or disabled/${i}`)]
const placement = JSON.parse(readFileSync(`${dir}/placement.json`, 'utf8')) as Record<string, {vm: string, type: string, cpu: string, exclusive: boolean, co_tenants: number}>
const summary = readFileSync(`${dir}/summary.tsv`, 'utf8').trim().split('\n').map(line => line.split('\t'))
const roster = ['original', 'survivors'].flatMap(mode => [1, 2, 3].map(n => `${mode}-hybrid-${n}`))
if (summary.length !== 6 || new Set(summary.map(row => row[0])).size !== 6 || summary.some(row => !roster.includes(row[0]!))) throw Error('incorrect six-job roster')
const rows = withWall(performance.now() + 30_000, () => roster.map(job => {
  const text = readFileSync(`${dir}/${job}.log`, 'utf8'), receipts = text.split('\n').filter(line => line.startsWith('HYBRID_RESULT '))
  if (receipts.length !== 1) throw Error(`missing/duplicate result: ${job}`)
  const result = JSON.parse(receipts[0]!.slice('HYBRID_RESULT '.length)) as Result
  const drops = text.split('\n').filter(line => line.startsWith('HYBRID_CTI ')).map(line => JSON.parse(line.slice('HYBRID_CTI '.length)) as Drop)
  const mode = job.startsWith('original-') ? 'original' : 'survivors'
  if (result.mode !== mode || result.initial !== (mode === 'original' ? 40 : 34)) throw Error(`wrong initial family: ${job}`)
  if (JSON.stringify(result.drops) !== JSON.stringify(drops.map(({stage, round, ms, law}) => ({stage, round, ms, law})))) throw Error(`CTI/result mismatch: ${job}`)
  if (new Set(drops.map(d => d.law)).size !== drops.length || result.removed !== drops.length || result.survivors !== result.initial - drops.length) throw Error(`incorrect removals: ${job}`)
  if (!Number.isFinite(result.wall) || result.wall < 0 || drops.some(d => !Number.isFinite(d.ms) || d.ms < 0 || d.ms > result.wall)) throw Error(`invalid wall: ${job}`)
  const hardware = placement[job], exit = Number(summary.find(row => row[0] === job)![1])
  if (!hardware?.exclusive || hardware.co_tenants !== 0 || hardware.type !== 'large' || !hardware.cpu || !hardware.vm) throw Error(`missing large exclusive placement: ${job}`)
  let alive = candidates.slice()
  const historical: string[] = []
  const certify = (name: string, pre: EncodedState, req: Drop['request'], p: Record<string, number>): void => {
    const law = alive.find(l => l.name === name), state = decode(pre)
    if (!law || caller.some(l => l.name === name) || ![...declarations, ...caller, ...alive].every(l => evaluate(l, p, state) === true)) throw Error(`uncertified predecessor: ${job} / ${name}`)
    if (evaluate(law, p, run.step(p, state, request(req))) !== false) throw Error(`uncertified post-state: ${job} / ${name}`)
  }
  if (mode === 'survivors') for (const round of [...new Set(capture.finiteDrops.map(d => d.round))].sort((a, b) => a - b)) {
    const group = capture.finiteDrops.filter(d => d.round === round)
    for (const d of group) { certify(d.law.name, d.pre, d.request, d.params); historical.push(d.law.name) }
    alive = alive.filter(l => !group.some(d => d.law.name === l.name))
  }
  const groups: Drop[][] = []
  for (const d of drops) {
    const last = groups.at(-1)
    if (last && last[0]!.stage === d.stage && last[0]!.round === d.round) last.push(d)
    else groups.push([d])
  }
  for (const group of groups) {
    for (const d of group) certify(d.law, d.pre, d.request, params)
    alive = alive.filter(l => !group.some(d => d.law === l.name))
  }
  const named = seven.filter(name => drops.some(d => d.law === name))
  return {job, exit, hardware, ...result, certified: drops.map(d => d.law), historical,
    namedSevenNew: named, namedSevenIncludingHistorical: seven.filter(name => named.includes(name) || historical.includes(name)),
    remaining: alive.map(l => l.name), meetsNewFiveAndWall: exit === 0 && named.length >= 5 && result.wall <= 2000}
}))
console.log('HYBRID_REPLAY', JSON.stringify({inputHash, rows,
  originalThreeMeetNewFive: rows.filter(r => r.mode === 'original').every(r => r.meetsNewFiveAndWall),
  allSixExitsZero: rows.every(r => r.exit === 0), allSixWallsWithinAllowance: rows.every(r => r.wall <= 2000),
  replaySourceSha256: Object.fromEntries(['research/protocols/ic3syn/mldr.ts', 'core/machine.ts', 'core/finite-houdini.ts'].map(path => [path, createHash('sha256').update(readFileSync(path)).digest('hex')])),
  trust: 'Independent interpreter/full-round-family replay only; no proof, completeness, or final-gate claim.'}))
