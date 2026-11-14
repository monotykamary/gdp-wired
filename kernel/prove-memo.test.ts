import {expect, test} from 'bun:test'
import {bool, nat, no, rule} from '../core/dsl.ts'
import {checkLaws} from './kernel.ts'
import {memoHits, proveLaws, proveSetFast} from './prove.ts'

// Distinct machine names isolate tests; fresh copies within a test retain the same name.
const make = (name = 'fresh binder memo regression') => rule(name)
  .inputs({i: nat}).maps({Flag: bool.from(false)})
  .step(({i, Flag}) => ({Flag: Flag.set(i, no)}))

const checked = (r: ReturnType<typeof make>, laws = r.kindLaws()) => {
  const out = proveSetFast(r.machine, laws)
  expect(out.proven).toBe(true)
  expect(out.checked).toBe(true)
  expect(out.proof && checkLaws(r.machine, laws, out.proof)).toBe(true)
  return out
}

// Rollback base only: retain positive assertions as explicit expected false-negatives.
// Both markers must be removed by a proper reuse fix before 0.49.0 can ship.
test.failing('fresh alpha-equivalent kind binders do not reuse stale instances (expected false-negative)', () => {
  const first = make(), firstLaws = first.kindLaws()
  checked(first, firstLaws)
  const second = make(), secondLaws = second.kindLaws()
  expect(JSON.stringify(secondLaws)).not.toBe(JSON.stringify(firstLaws))
  checked(second, secondLaws)
  const ordinary = proveLaws(second.machine, secondLaws)
  expect(ordinary.proven && ordinary.checked && !!ordinary.proof && checkLaws(second.machine, secondLaws, ordinary.proof)).toBe(true)
})

test('exact same-binder memo hits remain usable and independently checked', () => {
  const r = make('exact same-binder memo regression'), laws = r.kindLaws()
  checked(r, laws)
  const before = memoHits.n
  checked(r, laws)
  expect(memoHits.n).toBeGreaterThan(before)
})

test.failing('binding metadata is not memoized only by a shared holds object (expected false-negative)', () => {
  const r = make('shared holds metadata memo regression'), [kind] = r.kindLaws()
  expect(kind?.forall).toBeDefined()
  const first = {...kind!, name: 'shared holds binding metadata'}
  checked(r, [first])
  // Adding an unused universally quantified key preserves truth, not the instance tuple's width.
  const second = {...first, keys: [...(first.keys ?? []), 'unused$987654']}
  expect(second.holds).toBe(first.holds)
  const before = memoHits.miss
  const out = proveSetFast(r.machine, [second])
  // This checks invalidation, not the fast prover's support for an extra unused key.
  expect(memoHits.miss).toBeGreaterThan(before)
  if (out.proven) expect(out.checked && !!out.proof && checkLaws(r.machine, [second], out.proof)).toBe(true)
})
