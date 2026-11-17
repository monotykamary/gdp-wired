// Real source-finalization results, with a controlled clock jump only AFTER
// public publication. This avoids timing races and never fabricates a proof.
import {expect, spyOn, test} from 'bun:test'
import {extract} from './extract.ts'
import {buildLaw} from './laws.ts'
import {proveRule} from './dsl.ts'
import {proofOutput} from './proof-output.ts'
import {completedSearch, completedSourceRefusal} from './search-termination.ts'
import {requireSourceTranslation} from './source-check.ts'
import {WatchdogExpired, withSearchWatchdog} from './search-watchdog.ts'
import {BudgetExpired, checkWorkAdmission, remainingWork, withBudget} from '../kernel/prove.ts'

const fixture = (kind: 'unchecked' | 'error' | 'unknown') => {
  const x = extract('export class Counter { value = 0; steps = 0; tick() { if (this.steps < 3) { this.value++; this.steps++; } } }', {
    entry: 'Counter', check: {runs: 2, depth: 4, states: 0, probes: false, ...(kind === 'unchecked' ? {lawCrossCheck: false} : {})},
  })
  expect(x.ok).toBe(true)
  const built = buildLaw(x, {name: kind, expr: kind === 'unchecked' ? 'value >= 0' : kind === 'error' ? 'value == 0' : 'value <= 3'})
  if (built.kind !== 'law') throw new Error('expected a source invariant')
  // Deliberately faulty lowering: the independent native interpreter must
  // reject it, as in source-check.test.ts; this is NOT a trusted source proof.
  if (kind === 'error') built.law.holds = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  return {x, law: built.law, prove: () => proveRule(x.rule!, [...x.invariants ?? [], built.law], {search: false, watchdogMs: 100000})}
}
const atFinalization = <T>(action: (arm: () => void) => T): T => {
  const realNow = performance.now.bind(performance)
  let armed = false
  const clock = spyOn(performance, 'now').mockImplementation(() => realNow() + (armed ? 1e9 : 0))
  try { return action(() => { armed = true }) } finally { clock.mockRestore() }
}

for (const kind of ['unchecked', 'error'] as const) test(`completed source ${kind} survives a post-finalization owned watchdog without becoming proof`, () => {
  const f = fixture(kind), previous = proofOutput.on
  let finalized: unknown
  try {
    const out = atFinalization(arm => {
      proofOutput.on = event => { finalized = event.result; arm() }
      return f.prove()
    })
    expect(finalized).toBeDefined()
    expect(finalized).toBe(out)
    expect(out).toMatchObject({proven: false, checked: false, kernelProven: true, translation: kind})
    expect(out.stopped).toBeUndefined(); expect(out.termination).toBeUndefined()
    expect(completedSourceRefusal(out)).toBe(true)
    expect(() => requireSourceTranslation(f.x.rule!, [f.law])).toThrow()
  } finally { proofOutput.on = previous }
})

test('generic unknown still receives the actual owned watchdog cause', () => {
  const f = fixture('unknown'), previous = proofOutput.on
  const baseline = f.prove()
  expect(baseline.run).toBeUndefined(); expect(completedSearch(baseline)).toBe(false)
  let finalized: unknown
  try {
    const out = atFinalization(arm => { proofOutput.on = event => { finalized = event.result; arm() }; return f.prove() })
    expect(finalized).toBeDefined()
    expect(out).toMatchObject({proven: false, checked: false, stopped: true, termination: {kind: 'wall-deadline'}})
    expect(completedSourceRefusal(out)).toBe(false)
  } finally { proofOutput.on = previous }
})

test('interrupted source refusals and structurally unrelated unknowns are not completion', () => {
  const f = fixture('unchecked'), out = f.prove()
  expect(completedSourceRefusal(out)).toBe(true)
  for (const incomplete of [
    {...out, stopped: true}, {...out, termination: {kind: 'work-exhausted'}},
    {...out, stats: {stopped: true}}, {...out, stats: {stopped: false, termination: {kind: 'wall-deadline'}}},
    {...out, kernelProven: false}, {...out, kernelProven: undefined}, {...out, translation: 'sampled'}, {...out, translation: 'exhaustive'},
  ]) expect(completedSearch(incomplete)).toBe(false)
})

for (const cause of ['ancestor', 'work'] as const) test(`completed source refusal cannot swallow ${cause} cancellation`, () => {
  const f = fixture('unchecked'), previous = proofOutput.on
  let finalized: unknown, childReturned = false
  try {
    expect(() => atFinalization(arm => {
      proofOutput.on = event => {
        finalized = event.result
        if (cause === 'work') {
          try { checkWorkAdmission(remainingWork() + 1, 'source completion denied actual work') }
          catch (error) { if (!(error instanceof BudgetExpired)) throw error }
        }
        arm()
      }
      const child = () => { const out = f.prove(); childReturned = true; return out }
      return cause === 'ancestor' ? withSearchWatchdog(1000000, child) : withBudget(1000000, child)
    })).toThrow(cause === 'ancestor' ? WatchdogExpired : BudgetExpired)
    expect(finalized).toMatchObject({kernelProven: true, translation: 'unchecked'})
    expect(childReturned).toBe(false)
  } finally { proofOutput.on = previous }
})
