import {type E, type C, get, n, x, same, not} from '../../core/machine.ts'
import {tuple} from '../../kernel/kernel.ts'
import type {Fact} from '../../kernel/cyclic.ts'
import {certify, type Spec} from './certify.ts'
import {EGraph, Meter} from './match.ts'
const vote = (a: E, b: E, v: E) => get('Vote', tuple([a, b, v]))
const proposal = (b: E, v: E) => get('Proposal', tuple([b, v]))
const one = (t: E): C => same(t, n(1))
export const voteClause: Fact = {name: 'vote implies proposal', keys: ['a', 'b', 'v'], holds: {op: 'or', xs: [not(one(vote(x('a'), x('b'), x('v')))), one(proposal(x('b'), x('v')))]}}
export function voteExperiment(enabled: boolean, missingVote = false) {
  const start = performance.now()
  const meter = new Meter(100_000, start + 1000), graph = new EGraph(meter)
  const spec: Spec = {name: 'synthetic vote to proposal', hyps: missingVote ? [] : [one(vote(x('acceptor'), x('ballot'), x('value')))], concl: one(proposal(x('ballot'), x('value'))), rank: [n(0)], insts: [], uses: []}
  graph.seed([...spec.hyps, not(spec.concl)])
  const matches = enabled ? graph.match([vote(x('a'), x('b'), x('v'))], voteClause.keys) : []
  spec.insts = matches.map(s => ({fact: 0, at: voteClause.keys.map(k => s[k]!)}))
  const matchingMs = performance.now() - start
  const result = certify([voteClause], [spec], meter.used)
  return {...result, matchingMs, matchingUnits: meter.used, instances: spec.insts.length}
}
