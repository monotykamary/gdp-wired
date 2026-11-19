// Deliberate exact-Lean release gate; run each case in its own pinned Node process.
import assert from 'node:assert/strict'
import {createHash} from 'node:crypto'
import {forall} from '../../core/dsl.ts'
import type {Law, Machine} from '../../core/machine.ts'
import {raftTally, items as raft} from '../../research/realworld/items/dist-etcd-raft.ts'
import {tigerbeetle, items as tiger} from '../../research/realworld/items/ledgerpay-tigerbeetle.ts'
import {proveLeanAggregate} from './index.ts'

const tally = raftTally(), transfers = tigerbeetle()
const inputs: [Machine, Law][] = [
  [tally.machine, tally.law(raft.find(i => i.id === 'distributed/etcd-raft/tally')!.laws[0]!.name,
    ({yes, no, n}) => yes.plus(no).atMost(n))],
  [tally.machine, tally.law(raft.find(i => i.id === 'distributed/etcd-raft/tally')!.laws[1]!.name,
    ({yes, no, n}) => yes.times(2).gt(n).and(n.minus(no).times(2).atMost(n)).not())],
  [transfers.machine, transfers.law(tiger[0]!.laws[0]!.name,
    ({A}) => forall(k => A.at(k).dnec.implies(A.at(k).dp.plus(A.at(k).dpo).atMost(A.at(k).cpo))))],
  [transfers.machine, transfers.law(tiger[0]!.laws[1]!.name,
    ({A}) => forall(k => A.at(k).cned.implies(A.at(k).cp.plus(A.at(k).cpo).atMost(A.at(k).dpo))))],
]
const selected = process.argv[2]
if (selected === 'repeat') {
  const m = structuredClone(tally.machine), guard = m.step.flags!.records!
  assert(guard.op === 'and')
  m.step.flags!.records = guard.xs[0]!
  const result = await proveLeanAggregate(m, inputs[0]![1], {searchMs: 4000})
  assert.notEqual(result.kind, 'lean-checked')
  assert(!('receipt' in result) && !('checked' in result))
  console.log(JSON.stringify(result))
} else {
  const input = inputs[Number(selected)]
  assert(input, 'choose 0, 1, 2, 3, or repeat')
  const result = await proveLeanAggregate(...input)
  assert(result.kind === 'lean-checked', JSON.stringify(result))
  assert.equal(result.verdict, 'checked in Lean, not by the kernel')
  assert.equal(result.mechanism, Number(selected) < 2 ? 'finite-fold' : 'weighted')
  assert(!('checked' in result) && !('proven' in result))
  const sha = (v: string) => createHash('sha256').update(v).digest('hex')
  assert.equal(result.receipt.inputSha256, sha(JSON.stringify(input)))
  assert.equal(result.receipt.sourceSha256, sha(result.receipt.source))
  console.log(JSON.stringify(result))
}
