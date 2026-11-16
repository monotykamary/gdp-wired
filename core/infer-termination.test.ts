import {expect, test} from 'bun:test'
import {inferLaws} from './infer.ts'
import {proveRule, rule} from './dsl.ts'
import {proofOutput, publishProof, type ProofOutputNode} from './proof-output.ts'
import {toInterchange} from '../interchange/format.ts'
import {checkDocument} from '../interchange/check.ts'
import {accounts, accountsLaw} from '../examples/infer.ts'
import {checkWorkAdmission, remainingWork} from '../kernel/prove.ts'
import {withSearchWatchdog, checkWatchdog} from './search-watchdog.ts'

test('completed inference metadata cleanup retains exportable proof custody', () => {
  const r = rule('completed inference').state({value: 0}).step(({value}) => ({value: value.plus(1)}))
  const laws = [r.law('nonnegative', ({value}) => value.atLeast(0))]
  let capsule: ProofOutputNode | undefined
  proofOutput.on = event => { capsule = event.proof }
  try {
    const first = inferLaws(r, laws, [], {work: 1000000})
    // A checked family completed before the new local allowance; observing a
    // zero local allowance afterward must not taint it or lose its capsule.
    const v = inferLaws(r, laws, [], {first, ms: 0, wall: Infinity})
    expect(v).toMatchObject({proven: true, checked: true, stats: {stopped: false}})
    expect(v.stopped).toBeUndefined(); expect(v.termination).toBeUndefined(); expect(v.stats.termination).toBeUndefined()
    publishProof(v, r.machine, laws)
    const usual = (node: ProofOutputNode | undefined): Extract<ProofOutputNode, {kind: 'usual'}> | undefined => {
      if (!node) return undefined
      if (node.kind === 'usual') return node
      if (node.kind === 'derived') for (const parent of node.parents) { const found = usual(parent); if (found) return found }
      return undefined
    }
    const saved = usual(capsule)
    expect(saved).toBeDefined()
    const doc = toInterchange({kind: 'laws', machine: saved!.machine, laws: saved!.laws, proof: saved!.proof})
    expect(checkDocument(JSON.parse(JSON.stringify(doc)))).toMatchObject({accepted: true})
  } finally { proofOutput.on = undefined }
})

test('local counted allowance reports exhaustion even with an infinite real wall', () => {
  const r = accounts(), law = accountsLaw(r), first = proveRule(r, [law], {search: false})
  expect(first.stuck).toBe('sat')
  for (const timed of [false, true]) {
    const out = inferLaws(r, [law], [], {first, ms: 0, wall: Infinity, timed})
    expect(out).toMatchObject({proven: false, checked: false, stopped: true, stats: {stopped: true}, termination: {kind: timed ? 'wall-deadline' : 'work-exhausted', phase: 'inference allowance', scope: 'stage'}})
    expect(out.context?.goal).toBe(first.goal)
    expect(out.context?.stuck).toBe(first.stuck)
    expect(out.context?.witness).toEqual(first.witness)
  }
})

test('work and watchdog interruption retain actual partial counters and immutable initial SAT context', () => {
  const r = accounts(), law = accountsLaw(r), first = proveRule(r, [law], {search: false})
  expect(first.stuck).toBe('sat')
  for (const kind of ['work-exhausted', 'wall-deadline'] as const) for (const withFirst of [true, false]) {
    let seen: Record<string, number | string> | undefined
    const out = inferLaws(r, [law], [], {work: 1000000, ...(withFirst ? {first} : {}), progress: (phase, info) => {
      if (phase !== 'runs') return
      seen = info
      if (kind === 'work-exhausted') checkWorkAdmission(remainingWork() + 1, 'partial work control')
      else withSearchWatchdog(1, () => { Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 20); checkWatchdog('partial wall control') })
    }})
    expect(seen).toBeDefined()
    expect(out).toMatchObject({proven: false, checked: false, stopped: true, termination: {kind}, stats: {stopped: true}})
    expect(out.stats.samples).toBe(Number(seen!.samples))
    expect(out.stats.samples).toBeGreaterThan(0)
    expect(out.stats.work).toBeGreaterThan(0)
    expect(out.context?.goal).toBe(first.goal)
    expect(out.context?.witness).toEqual(first.witness)
  }
})
