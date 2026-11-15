import {expect, test} from 'bun:test'
import {bool, nat, no, rule, yes} from '../core/dsl.ts'
import {checkLaws} from './kernel.ts'
import {patternsOf} from './epr.ts'
import {decideLaw, memoHits, memoReuseStats, proveLaw, proveLaws, proveSetFast, sortMemoStats} from './prove.ts'

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

test('fresh alpha-equivalent kind binders do not reuse stale instances', () => {
  const first = make(), firstLaws = first.kindLaws()
  checked(first, firstLaws)
  const second = make(), secondLaws = second.kindLaws()
  expect(JSON.stringify(secondLaws)).not.toBe(JSON.stringify(firstLaws))
  const failed = memoReuseStats.hitCheckFailures, retries = memoReuseStats.coldRetries
  checked(second, secondLaws)
  if (process.env.GDP_MEMO_ALPHA !== '0') {
    expect(memoReuseStats.hitCheckFailures).toBeGreaterThan(failed)
    expect(memoReuseStats.coldRetries - retries).toBe(1)
  }
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
  const ignored = memoReuseStats.modelsIgnored, cold = memoReuseStats.coldRetries, modelRetries = memoReuseStats.modelRetries
  if (warm) publicChecked(make(name))
  publicChecked(make(name))
  if (warm && process.env.GDP_MEMO_ALPHA !== '0') {
    expect(memoReuseStats.modelsIgnored).toBeGreaterThan(ignored)
    expect(memoReuseStats.coldRetries - cold).toBe(1)
    expect(memoReuseStats.modelRetries - modelRetries).toBe(1)
  }
})

// A real composed key admits all three consumers to the native EPR memo path.
const jointMemoRule = (name: string) => {
  const r = rule(name).inputs({i: nat, j: nat})
    .state({'v$1': 0, 'v$2': 1}).maps({Seen: bool.from(false)})
    .assume(({i, j}) => i.lt(64).and(j.lt(64)))
    .step(({i, j, Seen}) => ({Seen: Seen.set(i.times(64).plus(j), Seen.at(i.times(64).plus(j)).not())}))
  expect(Object.values(patternsOf(r.machine, [])).some(pattern => pattern.length > 1)).toBe(true)
  return r
}

for (const consumer of ['law', 'decision', 'set'] as const) {
  test(`local hit check rejects a mismatched cached positive, consumer=${consumer}`, () => {
    const r = jointMemoRule(`joint positive ${consumer}`)
    const good = r.law('memo subject', s => s['v$1'].eq(0)), bad = r.law('memo subject', s => s['v$2'].eq(0))
    const ask = (laws: typeof good[]) => consumer === 'law' ? proveLaw(r.machine, laws, 0) : consumer === 'decision' ? decideLaw(r.machine, laws, 0) : proveSetFast(r.machine, laws)
    expect(ask([good])?.proven).toBe(true)
    const before = memoReuseStats.hitCheckFailures, retries = memoReuseStats.coldRetries
    expect(ask([bad])?.proven).not.toBe(true)
    expect(memoReuseStats.hitCheckFailures).toBeGreaterThan(before)
    expect(memoReuseStats.coldRetries - retries).toBe(1)
  })
  test(`exact model subsets reuse while renamed negative hints go cold, consumer=${consumer}`, () => {
    const r = jointMemoRule(`joint model ${consumer}`)
    const good = r.law('memo subject', s => s['v$1'].eq(0)), bad = r.law('memo subject', s => s['v$2'].eq(0)), support = r.law('dropped support', () => yes)
    const ask = (laws: typeof good[], i: number) => consumer === 'law' ? proveLaw(r.machine, laws, i) : consumer === 'decision' ? decideLaw(r.machine, laws, i) : proveSetFast(r.machine, laws)
    expect(ask([support, bad], 1)?.proven).toBe(false)
    const reuse = memoReuseStats.modelHits
    expect(ask([bad], 0)?.proven).toBe(false)
    expect(memoReuseStats.modelHits).toBeGreaterThan(reuse)
    const rejected = memoReuseStats.modelsIgnored
    expect(ask([good], 0)?.proven).toBe(true)
    expect(memoReuseStats.modelsIgnored).toBeGreaterThan(rejected)
    const out = proveLaws(r.machine, [good])
    expect(out.proven && out.checked && out.proof && checkLaws(r.machine, [good], out.proof)).toBe(true)
  })
}

test('renamed model payload is recomputed before the public proof', () => {
  const name = 'renamed model material regression'
  const badOf = (r: ReturnType<typeof make>) => {
    const [kind] = r.kindLaws()
    return {...kind!, name: 'model material', keys: [...(kind!.keys ?? []), 'unused$987654']}
  }
  const first = make(name), old = badOf(first), prior = proveSetFast(first.machine, [old])
  expect(prior.proven).toBe(false)
  expect(JSON.stringify(prior.failed)).toContain(`${old.forall}#`)
  const second = make(name), current = badOf(second), before = memoReuseStats.modelsIgnored
  const out = proveSetFast(second.machine, [current])
  expect(out.proven).toBe(false)
  expect(memoReuseStats.modelsIgnored).toBeGreaterThan(before)
  expect(JSON.stringify(out.failed)).not.toContain(`${old.forall}#`)
  expect(JSON.stringify(out.failed)).toContain(`${current.forall}#`)
  const publicProof = proveLaws(second.machine, [current])
  expect(publicProof.proven && publicProof.checked && publicProof.proof && checkLaws(second.machine, [current], publicProof.proof)).toBe(true)
})

test('renamed-hint support follows the current law selected by widened rows', () => {
  const r = rule('current memo support provenance').inputs({i: nat, j: nat})
    .state({x: 0, y: 0}).maps({Seen: bool.from(false)})
    .assume(({i, j}) => i.lt(64).and(j.lt(64)))
    .step(({i, j, y, Seen}) => ({x: y, Seen: Seen.set(i.times(64).plus(j), Seen.at(i.times(64).plus(j)).not())}))
  const a = r.law('original support', s => s.y.eq(0)), b = r.law('current support', s => s.y.eq(0))
  const target = r.law('dependent property', s => s.x.eq(0)), extra = r.law('added context', () => yes)
  const old = decideLaw(r.machine, [a, b, target], 2)
  expect(old?.proven).toBe(true)
  if (!old || !old.proven) throw new Error('old native proof missing')
  const supports = [a, b].filter(l => old.uses.includes(l.name))
  expect(supports.length).toBe(1)
  const previous = supports[0]!, replacement = previous === a ? b : a
  const laws = [replacement, previous, target, extra], checks = memoReuseStats.hitChecks
  const current = decideLaw(r.machine, laws, 2)
  expect(current?.proven).toBe(true)
  if (!current || !current.proven) throw new Error('current checked proof missing')
  expect(memoReuseStats.hitChecks).toBeGreaterThan(checks)
  expect(current.uses).toContain(replacement.name)
  expect(current.uses).not.toContain(previous.name)
  const proof = proveSetFast(r.machine, laws)
  expect(proof.proven && proof.checked && proof.proof && checkLaws(r.machine, laws, proof.proof)).toBe(true)
})

test('reordered exact contexts retain independently checked material hits', () => {
  const r = jointMemoRule('ordered material provenance')
  const a = r.law('first property', s => s['v$1'].eq(0)), b = r.law('second property', s => s['v$2'].eq(1))
  const first = proveSetFast(r.machine, [a, b])
  expect(first.proven && first.checked && first.proof && checkLaws(r.machine, [a, b], first.proof)).toBe(true)
  const before = memoReuseStats.setHits
  const second = proveSetFast(r.machine, [b, a])
  expect(second.proven && second.checked && second.proof && checkLaws(r.machine, [b, a], second.proof)).toBe(true)
  expect(memoReuseStats.setHits).toBeGreaterThan(before)
  const hits = memoReuseStats.setHits
  const third = proveSetFast(r.machine, [b, a])
  expect(third.proven && third.checked && third.proof && checkLaws(r.machine, [b, a], third.proof)).toBe(true)
  expect(memoReuseStats.setHits).toBeGreaterThan(hits)
})
