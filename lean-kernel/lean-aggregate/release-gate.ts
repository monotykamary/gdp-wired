// Deliberate exact-Lean release gate; run each case in its own pinned Node process.
import assert from 'node:assert/strict'
import {createHash} from 'node:crypto'
import {n, same, type Machine} from '../../core/machine.ts'
import {checkAdmissionControls, corpusInput} from './admission-controls.ts'
import {proveLeanAggregate, type LeanAggregateVerdict} from './index.ts'
import {admitAggregateSource} from './source.ts'

function assertRefusal(result: LeanAggregateVerdict, detail: RegExp) {
  assert(result.kind === 'not-checked' && result.reason !== 'lean', JSON.stringify(result))
  assert.match(result.detail, detail)
  assert(!('receipt' in result) && !('checked' in result) && !('proven' in result))
}

// Source-level analogues of the frozen instrumented packet controls. The
// source still scopes, so rejection cannot be due to submitting a ghost/sum.
function weightedMutant(machine: Machine, side: 0 | 1, control: 'lost-grouping' | 'stale-contribution'): void {
  const write = machine.step.maps?.[side === 0 ? 'A.dp' : 'A.cp']
  assert(write && 'each' in write && write.value.op === 'if' && write.value.else.op === 'if')
  const delta = write.value.else
  if (control === 'lost-grouping') {
    assert(delta.c.op === 'and')
    const routing = delta.c.xs[1]
    assert(routing?.op === 'or')
    const resolving = routing.xs[0]
    assert(resolving?.op === 'and')
    const group = resolving.xs[1]
    assert(group?.op === '=' && group.a.op === 'var' && group.a.name === write.each &&
      group.b.op === 'get' && group.b.map === (side === 0 ? 'T.dr' : 'T.cr'))
    // Resolve the pending amount without restricting it to its owning account.
    resolving.xs[1] = same(n(0), n(0))
  } else {
    assert(delta.then.op === 'sub' && delta.then.b.op === 'if')
    const removal = delta.then.b.c
    assert(removal.op === 'or' && removal.xs[0]?.op === 'flag' && removal.xs[0].name === 'resolves' &&
      removal.xs[1]?.op === 'flag' && removal.xs[1].name === 'expires')
    // Expiry still subtracts; a post or void leaves its pending contribution stale.
    delta.then.b.c = removal.xs[1]
  }
}

const selected = process.argv[2]
if (selected === 'admission') {
  console.log(JSON.stringify({case: selected, refused: await checkAdmissionControls()}))
} else if (selected === 'repeat') {
  const [original, law] = corpusInput(0)
  const m = structuredClone(original), guard = m.step.flags?.records
  assert(guard?.op === 'and' && guard.xs[0])
  m.step.flags!.records = guard.xs[0]
  admitAggregateSource(m, law)
  const result = await proveLeanAggregate(m, law, {searchMs: 4000})
  assertRefusal(result, /^Finite-fold local goals did not close\.$/)
  console.log(JSON.stringify(result))
} else if (selected === 'lost-grouping-0' || selected === 'lost-grouping-1' ||
    selected === 'stale-contribution-0' || selected === 'stale-contribution-1') {
  const side = selected.endsWith('-0') ? 0 : 1
  const control = selected.startsWith('lost-grouping') ? 'lost-grouping' : 'stale-contribution'
  const [original, law] = corpusInput(side === 0 ? 2 : 3)
  const m = structuredClone(original)
  weightedMutant(m, side, control)
  assert.notEqual(admitAggregateSource(m, law), JSON.stringify([original, law]))
  const result = await proveLeanAggregate(m, law)
  assertRefusal(result, /^No weighted update shape recognized\.$|^Weighted equality did not close\.$/)
  console.log(JSON.stringify(result))
} else {
  assert(selected === '0' || selected === '1' || selected === '2' || selected === '3',
    'choose 0, 1, 2, 3, admission, repeat, lost-grouping-0/1, or stale-contribution-0/1')
  const index = selected === '0' ? 0 : selected === '1' ? 1 : selected === '2' ? 2 : 3
  const input = corpusInput(index)
  // Hash the actual corpus pair independently of the adapter's snapshot.
  const sha = (v: string) => createHash('sha256').update(v).digest('hex')
  const expected = sha(JSON.stringify(input))
  const result = await proveLeanAggregate(...input)
  assert(result.kind === 'lean-checked', JSON.stringify(result))
  assert.equal(result.verdict, 'checked in Lean, not by the kernel')
  assert.equal(result.mechanism, index < 2 ? 'finite-fold' : 'weighted')
  assert(!('checked' in result) && !('proven' in result))
  assert.equal(result.receipt.inputSha256, expected)
  assert.equal(result.receipt.sourceSha256, sha(result.receipt.source))
  assert.equal(result.receipt.theorem, 'aggregate_claim')
  console.log(JSON.stringify(result))
}
