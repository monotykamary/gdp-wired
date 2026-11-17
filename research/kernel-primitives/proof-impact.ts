// Isolated proof-impact probe. Run in the same --timing VM/job as the baseline; do not
// interpret these process-local milliseconds as a cross-machine speed comparison.
// Usage: bun research/kernel-primitives/proof-impact.ts [--ms 10000]
import {performance} from 'node:perf_hooks'
import {min, nat, proveRule, rule, type Verdict} from '../../core/dsl.ts'
import {fixedInt} from '../../core/fixed-integers.ts'

const args = process.argv.slice(2)
if (args.length !== 0 && (args.length !== 2 || args[0] !== '--ms')) throw new Error('usage: proof-impact.ts [--ms positive-integer]')
const ms = args.length ? Number(args[1]) : 10000
if (!Number.isSafeInteger(ms) || ms <= 0) throw new RangeError('--ms must be a positive integer')

const u8 = fixedInt(8, false)
const u32 = fixedInt(32, false)
const u64 = fixedInt(64, false)

const cases = [
  {
    name: 'baseline/nat-counter-nonnegative',
    make: () => {
      const r = rule('nat counter').inputs({d: nat}).state({x: 0}).step(({x, d}) => ({x: x.plus(d)}))
      return {r, laws: [r.law('counter nonnegative', ({x}) => x.atLeast(0))]}
    },
  },
  {
    name: 'baseline/nat-saturating-upper-255',
    make: () => {
      const r = rule('nat saturating').inputs({d: nat}).state({x: 0}).step(({x, d}) => ({x: min(x.plus(d), 255)}))
      return {r, laws: [r.law('counter at most 255', ({x}) => x.atMost(255))]}
    },
  },
  {
    name: 'fixed/u8-wrap-bounds',
    make: () => {
      const r = rule('u8 wrap').inputs({d: u8}).state({x: u8.from('0')}).step(({x, d}) => ({x: x.plus(d, 'WRAP')}))
      return {r, laws: [r.law('wrapped x in unsigned 8-bit bounds', ({x}) => x.atLeast(u8.lift('0')).and(x.atMost(u8.lift('255'))))]}
    },
  },
  {
    name: 'fixed/u8-saturate-bounds',
    make: () => {
      const r = rule('u8 saturate').inputs({d: u8}).state({x: u8.from('0')}).step(({x, d}) => ({x: x.plus(d, 'SATURATE')}))
      return {r, laws: [r.law('saturated x in unsigned 8-bit bounds', ({x}) => x.atLeast(u8.lift('0')).and(x.atMost(u8.lift('255'))))]}
    },
  },
  {
    name: 'fixed/u8-trap-bounds',
    make: () => {
      const r = rule('u8 trap').inputs({d: u8}).state({x: u8.from('0')}).step(({x, d}) => ({x: x.plus(d, 'TRAP')}))
      return {r, laws: [r.law('trapping x retains unsigned 8-bit bounds', ({x}) => x.atMost(u8.lift('255')))]}
    },
  },
  {
    name: 'fixed/u32-wrap-bounds',
    make: () => {
      const r = rule('u32 wrap').inputs({d: u32}).state({x: u32.from('0')}).step(({x, d}) => ({x: x.plus(d, 'WRAP')}))
      return {r, laws: [r.law('wrapped x in unsigned 32-bit bounds', ({x}) => x.atLeast(u32.lift('0')).and(x.atMost(u32.lift('4294967295'))))]}
    },
  },
  {
    name: 'fixed/u64-wrap-bounds',
    make: () => {
      const r = rule('u64 wrap').inputs({d: u64}).state({x: u64.from('0')}).step(({x, d}) => ({x: x.plus(d, 'WRAP')}))
      return {r, laws: [r.law('wrapped x in unsigned 64-bit bounds', ({x}) => x.atLeast(u64.lift('0')).and(x.atMost(u64.lift('18446744073709551615'))))]}
    },
  },
] as const

console.log(JSON.stringify({type: 'metadata', repetitions: 3, warmups: 1, search: false, watchdogMs: ms,
  hardwarePlacement: 'required externally from supercomputer --timing placement.json; none asserted by this process'}))

// TRAP timing is now included: Rule assembly retains a rollback branch and
// both runtimes throw before writes. Dedicated integration tests check effects.

for (const c of cases) {
  let prepared: ReturnType<typeof c.make>
  try { prepared = c.make() }
  catch (error) {
    console.log(JSON.stringify({type: 'case-error', name: c.name, stage: 'construction', error: String(error)}))
    continue
  }
  for (let repeat = 0; repeat < 4; repeat++) {
    const started = performance.now()
    try {
      const verdict: Verdict = proveRule(prepared.r, prepared.laws, {search: false, watchdogMs: ms})
      const wallMs = performance.now() - started
      console.log(JSON.stringify({type: 'receipt', name: c.name, pass: repeat === 0 ? 'warmup' : repeat,
        wallMs, proven: verdict.proven, kernelChecked: verdict.checked,
        stuck: verdict.stuck ?? null, goal: verdict.goal ?? null, why: verdict.why ?? null,
        termination: verdict.termination ?? null}))
    } catch (error) {
      console.log(JSON.stringify({type: 'case-error', name: c.name, pass: repeat === 0 ? 'warmup' : repeat,
        wallMs: performance.now() - started, error: String(error)}))
    }
  }
}
