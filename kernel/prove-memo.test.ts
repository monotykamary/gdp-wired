import {expect, test} from 'bun:test'
import {bool, nat, no, rule} from '../core/dsl.ts'
import {checkLaws} from './kernel.ts'
import {memoHits, proveLaws, proveSetFast, sortMemoStats} from './prove.ts'

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
// The renamed-state marker must be removed by the complete reuse fix.
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

test('law text and sort caches both invalidate changed shared-holds metadata', () => {
  const r = make('shared holds cache identity regression'), [kind] = r.kindLaws()
  const first = {...kind!, name: 'shared holds identity'}
  checked(r, [first])
  const before = {memo: memoHits.miss, sort: sortMemoStats.misses}
  const second = {...first, keys: [...(first.keys ?? []), 'unused$987654']}
  expect(second.holds).toBe(first.holds)
  // Cache identity is separate from the fast prover's cold extra-key completeness limit.
  proveSetFast(r.machine, [second])
  expect(memoHits.miss).toBeGreaterThan(before.memo)
  expect(sortMemoStats.misses).toBeGreaterThan(before.sort)
})

for (const warm of [false, true]) test(`shared-holds metadata has a checked public proof, warm=${warm}`, () => {
  const name = `public shared-holds memo regression ${warm}`
  const lawsOf = (r: ReturnType<typeof make>) => {
    const [kind] = r.kindLaws(), first = {...kind!, name: 'shared holds binding metadata'}
    const second = {...first, keys: [...(first.keys ?? []), 'unused$987654']}
    expect(second.holds).toBe(first.holds)
    return [second]
  }
  const publicChecked = (r: ReturnType<typeof make>, laws = lawsOf(r)) => {
    // Probe the fast route first: its cold extra-key limit must not poison the public ordinary proof.
    proveSetFast(r.machine, laws)
    const out = proveLaws(r.machine, laws)
    expect(out.proven).toBe(true)
    expect(out.checked).toBe(true)
    expect(out.proof && checkLaws(r.machine, laws, out.proof)).toBe(true)
  }
  if (warm) publicChecked(make(name))
  publicChecked(make(name))
})
