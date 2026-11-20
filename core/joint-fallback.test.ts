// Joint-proof fallback tests: when an ordinary proof ends unknown (not proven, not refuted), retry jointly with
// compatible sibling laws stated on the same rule within the time that law's own budget has left, crediting only that
// law and only when the kernel checks the whole joint family. Never change a proven or refuted verdict, and never let
// a false sibling carry a target through.
import {expect, setDefaultTimeout, test} from 'bun:test'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {check} from './cli.ts'
import {nat, rule, when} from './dsl.ts'
import {dedup, items as watermillItems} from '../research/realworld/items/dist-watermill.ts'
import {type RealItem, invariant, jointSpec, proveItemLaw, stepLaw} from '../research/realworld/lib.ts'

setDefaultTimeout(180_000)

const watermill = watermillItems[0]!

test('realworld corpus fallback proves Watermill #0 while keeping #1 and #2 proven', () => {
  // Control: Watermill #0 alone ends unknown (not proven, not refuted) under ordinary scoring.
  const alone = watermill.laws[0]!.prove(15_000)
  expect(alone.proven).toBe(false)
  expect(alone.checked).toBe(false)
  expect(alone.run).toBeUndefined()

  // Fallback: proveItemLaw retries Watermill #0 jointly with #1 and #2 within its remaining budget.
  const proven0 = proveItemLaw(watermill, 0, 30_000)
  expect(proven0.proven).toBe(true)
  expect(proven0.checked).toBe(true)

  // Sibling laws still prove directly on their own ordinary paths.
  const proven1 = proveItemLaw(watermill, 1, 15_000)
  expect(proven1.proven).toBe(true)
  expect(proven1.checked).toBe(true)
  const proven2 = proveItemLaw(watermill, 2, 15_000)
  expect(proven2.proven).toBe(true)
  expect(proven2.checked).toBe(true)
})

test('realworld corpus fallback: a false sibling must NOT let the target through or turn unknown into refuted', () => {
  const spec = jointSpec(watermill.laws[0]!)
  expect(spec).toBeDefined()
  const d = spec!.rule as ReturnType<typeof dedup>

  // Add a false sibling step law on the exact same Watermill rule: the joint family fails, so #0 stays unknown.
  const falseSibling = stepLaw(
    d,
    d.stepLaw('false sibling: every message is dropped', (_, after) => after.seen),
    'safety', 'inferred', 'negative control: false sibling must block joint proof',
  )
  const withFalseSibling: RealItem = {...watermill, laws: [...watermill.laws, falseSibling]}
  const res = proveItemLaw(withFalseSibling, 0, 15_000)
  expect(res.proven).toBe(false)
  expect(res.checked).toBe(false)
  expect(res.run).toBeUndefined()

  // Ex-falso soundness control: a contradictory false sibling invariant must never carry a false target through.
  const r = rule('ex-falso-control')
    .inputs({k: nat})
    .state({x: 0})
    .step(({k, x}) => ({x: when(k.gt(0), x.plus(1), x)}))
  const badItem: RealItem = {
    ...watermill,
    id: 'test/ex-falso-control',
    laws: [
      invariant(r, r.law('false target', ({x}) => x.eq(99)), 'safety', 'inferred', 'false target'),
      invariant(r, r.law('false sibling', ({x}) => x.eq(1)), 'safety', 'inferred', 'false sibling'),
    ],
  }
  const exFalso = proveItemLaw(badItem, 0, 5_000)
  expect(exFalso.proven).toBe(false)
  expect(exFalso.checked).toBe(false)
  expect(exFalso.run).toBeDefined()
})

test('realworld corpus fallback: a refuted target stays refuted and proven/exhausted verdicts are unchanged', () => {
  const spec = jointSpec(watermill.laws[0]!)
  expect(spec).toBeDefined()
  const d = spec!.rule as ReturnType<typeof dedup>

  // A false target beside true Watermill siblings stays refuted by its own run; fallback never runs.
  const badTarget = stepLaw(
    d,
    d.stepLaw('false target: every message is dropped', (_, after) => after.seen),
    'safety', 'inferred', 'negative control: refuted target stays refuted',
  )
  const refutedItem: RealItem = {...watermill, laws: [badTarget, watermill.laws[1]!, watermill.laws[2]!]}
  const refuted = proveItemLaw(refutedItem, 0, 15_000)
  expect(refuted.proven).toBe(false)
  expect(refuted.checked).toBe(false)
  expect(refuted.run).toBeDefined()

  // Exhausted budget control: if the ordinary call consumes the budget, fallback must not run.
  let siblingTouched = false
  const r = rule('budget-control').inputs({n: nat}).state({x: 0}).step(({x}) => ({x}))
  const baseLaw = invariant(r, r.law('dummy', ({x}) => x.atMost(0)), 'safety', 'inferred', 'control')
  const exhausted: RealItem = {
    ...watermill,
    id: 'test/budget-exhausted',
    laws: [
      {
        ...baseLaw,
        prove: () => ({proven: false, checked: false, stuck: 'unknown', stopped: true, termination: {kind: 'wall-deadline', phase: 'test', scope: 'search'}}),
      },
      {
        ...invariant(r, r.law('sibling', ({x}) => x.atMost(0)), 'safety', 'inferred', 'sibling'),
        prove: () => { siblingTouched = true; return {proven: true, checked: true} },
      },
    ],
  }
  const stopped = proveItemLaw(exhausted, 0, 5_000)
  expect(stopped.proven).toBe(false)
  expect(stopped.stopped).toBe(true)
  expect(siblingTouched).toBe(false)
})

const weightedReserveSource = (lawComments: string) => `
type Bucket = { a: number; b: number; c: number }
export class WeightedReserve {
  buckets = new Map<number, Bucket>()
  constructor(private readonly cap: number) {
    if (cap < 0) throw new Error('cap >= 0')
  }
  ${lawComments}
  init(k: number): void {
    if (k < 0) throw new Error('key')
    if (!this.buckets.has(k)) this.buckets.set(k, { a: 0, b: 0, c: this.cap })
  }
  reserve(k: number): void {
    if (k < 0) throw new Error('key')
    const cur = this.buckets.get(k)
    if (!cur || cur.c < 11) return
    this.buckets.set(k, { a: cur.a, b: cur.b + 1, c: cur.c - 11 })
  }
  convert(k: number): void {
    if (k < 0) throw new Error('key')
    const cur = this.buckets.get(k)
    if (!cur || cur.b < 1) return
    this.buckets.set(k, { a: cur.a + 1, b: cur.b - 1, c: cur.c + 4 })
  }
  burn(k: number): void {
    if (k < 0) throw new Error('key')
    const cur = this.buckets.get(k)
    if (!cur || cur.c < 1) return
    this.buckets.set(k, { a: cur.a, b: cur.b, c: cur.c - 1 })
  }
}
`

test('CLI check fallback proves an unknown law with its sibling, rejects false siblings, and keeps refuted targets broken', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-joint-fallback-'))
  const targetLaw = '// gdp: law seven a within cap: forall k in buckets: 7 * buckets[k].a <= cap'
  const helperLaw = '// gdp: law weighted bound: forall k in buckets: 7 * buckets[k].a + 11 * buckets[k].b + buckets[k].c <= cap'
  const falseSibling = '// gdp: law false sibling: forall k in buckets: buckets[k].c == 0'
  const refutedTarget = '// gdp: law false target: forall k in buckets: buckets[k].c == 0'
  const checkOpts = {ms: 15_000, propose: false, check: {runs: 15, depth: 6, states: 20}}
  try {
    // 1) Alone: target law ends unknown (not proven, not broken).
    const aloneFile = join(dir, 'alone.ts')
    writeFileSync(aloneFile, weightedReserveSource(targetLaw))
    const alone = await check([aloneFile], checkOpts)
    expect(alone.exit).toBe(2)
    expect(alone.rules[0]!.ok).toBe(true)
    expect(alone.rules[0]!.laws[0]!.verdict).toBe('unknown')

    // 2) With its true sibling in the same file: target law is proven via the joint fallback.
    const jointFile = join(dir, 'joint.ts')
    writeFileSync(jointFile, weightedReserveSource(`${targetLaw}\n  ${helperLaw}`))
    const joint = await check([jointFile], checkOpts)
    expect(joint.exit).toBe(0)
    const byName = (res: Awaited<ReturnType<typeof check>>, name: string) =>
      res.rules[0]!.laws.find(l => l.name === name)!
    expect(byName(joint, 'seven a within cap').verdict).toBe('proven')
    expect(byName(joint, 'weighted bound').verdict).toBe('proven')

    // 3) Control: adding a false sibling must NOT let the unknown target through (whole joint family fails).
    const badSibFile = join(dir, 'false-sibling.ts')
    writeFileSync(badSibFile, weightedReserveSource(`${targetLaw}\n  ${helperLaw}\n  ${falseSibling}`))
    const badSib = await check([badSibFile], checkOpts)
    expect(badSib.exit).toBe(2)
    expect(byName(badSib, 'seven a within cap').verdict).toBe('unknown')
    expect(byName(badSib, 'seven a within cap').run).toBeUndefined()
    expect(byName(badSib, 'weighted bound').verdict).toBe('proven')
    expect(byName(badSib, 'false sibling').verdict).toBe('broken')
    expect(byName(badSib, 'false sibling').run?.length).toBeGreaterThan(0)

    // 4) Control: a refuted target stays broken even beside true siblings.
    const refutedFile = join(dir, 'refuted-target.ts')
    writeFileSync(refutedFile, weightedReserveSource(`${refutedTarget}\n  ${helperLaw}`))
    const refuted = await check([refutedFile], checkOpts)
    expect(refuted.exit).toBe(1)
    expect(byName(refuted, 'false target').verdict).toBe('broken')
    expect(byName(refuted, 'false target').run?.length).toBeGreaterThan(0)
    expect(byName(refuted, 'weighted bound').verdict).toBe('proven')
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
})
