// A real recursive datatype, not bounded list evaluation or a length abstraction.
import {data, define, law, natural, self, proveData, type Val} from '../../core/data.ts'
import {type C, get, n, x, not} from '../../core/machine.ts'
import {substC, substE} from '../../kernel/kernel.ts'
import {type Cyclic, refuseCyclic} from '../../kernel/cyclic.ts'
import {fullWork, withWall} from '../../kernel/prove.ts'
import {certify, type Spec} from './certify.ts'
import {EGraph, Meter} from './match.ts'

const List = data('AstraListExperiment', {nil: {}, cons: {head: natural, tail: self}})
const app = define('astraExperimentAppend', {xs: List, ys: List}, List, ({xs, ys}) => (xs as Val).match({nil: () => ys as Val, cons: ({head, tail}) => List.cons(head, app(tail, ys))}))
const rev = define('astraExperimentReverse', {xs: List}, List, ({xs}) => (xs as Val).match({nil: () => List.nil, cons: ({head, tail}) => app(rev(tail), List.cons(head, List.nil)) as Val}))
const snoc = law('reverse of append one', {a: List, n: natural}, ({a, n}) => (rev(app(a, List.cons(n, List.nil))) as Val).eq(List.cons(n, rev(a))))

export function prepareLemma() {
  const start = performance.now(), work = fullWork()
  const verdict = withWall(start + 20000, () => proveData(snoc, {lemmas: false, ms: 10000}))
  return {verdict, ms: performance.now() - start, proofUnits: fullWork() - work}
}

export function recursiveExperiment(lemma: Cyclic, root: number, enabled: boolean) {
  const refusal = refuseCyclic(lemma)
  if (refusal !== undefined) throw new Error(`unchecked lemma: ${refusal}`)
  const theorem = lemma.nodes[root]
  if (!theorem || theorem.concl.op !== '=') throw new Error('expected equational lemma root')
  // This is the snoc obligation on the recursive call's tail, with arbitrary
  // head and tail. It does NOT claim a proof of reverse(reverse(xs)) = xs.
  const sub = {vars: {a: get('AstraListExperiment.cons.tail', x('input')), n: get('AstraListExperiment.cons.head', x('input'))}, maps: {}, flags: {}}
  const forward = substC(theorem.concl, sub)
  if (forward.op !== '=') throw new Error('expected equation')
  const concl: C = {op: '=', a: forward.b, b: forward.a}
  const rank = theorem.rank.map(e => substE(e, sub))
  if (!rank.length) throw new Error('lemma must have a rank')
  rank[0] = {op: 'add', a: rank[0]!, b: n(1)}
  const client: Spec = {name: 'reverse-append obligation at recursive tail', hyps: theorem.hyps.map(c => substC(c, sub)), concl, rank, insts: [], uses: []}
  const matchingStart = performance.now()
  const meter = new Meter(500_000, matchingStart + 2000), graph = new EGraph(meter)
  graph.seed([...client.hyps, not(concl)])
  const matches = enabled ? graph.match([theorem.concl.a], ['a', 'n'], 8) : []
  client.uses = matches.map(binding => ({node: root, subst: binding, guard: {op: '<=', a: n(0), b: n(0)}}))
  const specs: Spec[] = [...lemma.nodes, client]
  const matchingMs = performance.now() - matchingStart
  const result = certify(lemma.facts, specs, meter.used, 2_000_000, lemma.nodes)
  let removedUse: string | undefined, badRank: string | undefined
  if (result.checked && result.proof) {
    const removed = structuredClone(result.proof)
    removed.nodes.at(-1)!.uses = []
    removedUse = refuseCyclic(removed)
    const wrong = structuredClone(result.proof)
    wrong.nodes.at(-1)!.rank = theorem.rank.map(e => substE(e, sub))
    badRank = refuseCyclic(wrong)
  }
  return {...result, matchingMs, matchingUnits: meter.used, matches: matches.length, lemmaUses: client.uses.length, removedUse, badRank}
}
