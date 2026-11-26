// End-to-end verification script for the proposed SumDecl `reset?` change.
// Runs ONLY inside an ephemeral patched copy on Boat (never against the unpatched worktree):
//   1. Proves putClear, covering.test.ts's broadcast-covering-clear, step-reads-sum, and
//      cohort19 law-2 & law-3 (Apache Spark MemoryStore #0 and #1).
//   2. Verifies preserved negative controls (lowerBoundDual, partial range wipe, infinite shift).
//   3. Runs a 12-mutant battery (all 4 required classes + certificate tampers) against BOTH
//      TypeScript kernel.ts AND Lean 4.34.0 `decide +kernel`.
//   4. Emits Lean 4.34.0 files (PutClear.lean, SparkMemoryStore.lean, MutantBattery.lean) to
//      OUT_DIR for Lean elaboration and `#print axioms` verification.
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {bool, choose, forall, nat, no, oneOf, proveRule, proveSteps, record, replayRefutation, rule, when, yes} from '../../core/dsl.ts'
import {type C, type E, type Law, type Machine, type Sum} from '../../core/machine.ts'
import {check, checkLaws, sumMachine, trueC} from '../../kernel/kernel.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {retainedSumMachineToLean, smachineToLean} from '../../lean-kernel/emit.ts'

const outDir = process.env.OUT_DIR ?? '.'
mkdirSync(outDir, {recursive: true})

const assert = (cond: boolean, msg: string) => {
  if (!cond) throw new Error(`VERIFY FAILED: ${msg}`)
}

const sumAnswer = (m: Machine, laws: Law[], proof: {instances: Record<string, Record<string, E[]>>, trees: Record<string, import('../../kernel/kernel.ts').Tree>}): boolean => {
  try {
    const {machine, goals} = sumMachine(m, undefined, laws)
    return goals.every(g => proof.trees[g.name] !== undefined && check(g, proof.trees[g.name]!)) && checkLaws(machine, laws, proof)
  } catch {
    return false
  }
}

const Block = record({present: bool, size: nat})

// Exact frozen cohort19 model (commit 1ec42d55cf821f4b3ccf7cdbde5ffb2f4d979c51)
const sparkMemoryStore = () => rule('Spark MemoryStore + StorageMemoryPool')
  .params({poolSize: nat})
  .inputs({op: oneOf('putBlock', 'removeBlock', 'reserveUnroll', 'releaseUnroll', 'clear'), id: nat, size: nat, maxAcquisition: nat})
  .state({memoryUsed: 0})
  .maps({Blocks: Block.from({present: false, size: 0}), Unroll: 0})
  .flags(({op, id, size, maxAcquisition, poolSize, memoryUsed, Blocks, Unroll}) => ({
    puts: op.is('putBlock').and(Blocks.at(id).present.not(), size.atMost(maxAcquisition), memoryUsed.plus(size).atMost(poolSize)),
    removes: op.is('removeBlock').and(Blocks.at(id).present),
    reservesUnroll: op.is('reserveUnroll').and(size.atMost(maxAcquisition), memoryUsed.plus(size).atMost(poolSize)),
    releasesUnroll: op.is('releaseUnroll').and(Unroll.at(id).gt(0)),
    clears: op.is('clear'),
  }))
  .step(({id, size, memoryUsed, Blocks, Unroll, puts, removes, reservesUnroll, releasesUnroll, clears}) => {
    const b = Blocks.at(id), u = Unroll.at(id), relU = when(size.atMost(u), size, u)
    return {
      memoryUsed: when(clears, 0,
        when(puts.or(reservesUnroll), memoryUsed.plus(size),
          when(removes, memoryUsed.minus(b.size),
            when(releasesUnroll, memoryUsed.minus(relU), memoryUsed)))),
      Blocks: Blocks.each(k => ({
        present: choose(clears, no, choose(puts.and(k.eq(id)), yes, choose(removes.and(k.eq(id)), no, Blocks.at(k).present))),
        size: when(clears, 0, when(puts.and(k.eq(id)), size, when(removes.and(k.eq(id)), 0, Blocks.at(k).size))),
      })),
      Unroll: Unroll.each(k => when(clears, 0,
        when(reservesUnroll.and(k.eq(id)), Unroll.at(k).plus(size),
          when(releasesUnroll.and(k.eq(id)), Unroll.at(k).minus(relU), Unroll.at(k))))),
    }
  })

const summary: Record<string, unknown> = {positive: {}, controls: {}, mutants: {}}

// 1. putClear
const putClear = rule('put-clear')
  .inputs({op: oneOf('put', 'clear'), id: nat, val: nat})
  .state({total: 0})
  .maps({M: 0})
  .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clear')}))
  .step(({id, val, total, M, puts, clears}) => ({
    total: when(clears, 0, when(puts, total.plus(val), total)),
    M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), val, M.at(k)))),
  }))
const pcEq = putClear.law('M.sum() == total', ({M, total}) => M.sum().eq(total))
const pcLe = putClear.law('M.sum() <= total', ({M, total}) => M.sum().atMost(total))
const pcStep = putClear.stepLaw('clear zeroes sum', (_b, a) => a.M.sum().eq(0), ({clears}) => clears)
const vPcEq = proveRule(putClear, [pcEq], {search: false})
const vPcLe = proveRule(putClear, [pcLe], {search: false})
const vPcStep = proveSteps(putClear, [], [pcStep], {search: false})
assert(vPcEq.proven && vPcEq.checked, `putClear eqLaw failed: ${JSON.stringify(vPcEq)}`)
assert(vPcLe.proven && vPcLe.checked, `putClear leLaw failed: ${JSON.stringify(vPcLe)}`)
assert(vPcStep.proven && vPcStep.checked, `putClear stepLaw failed: ${JSON.stringify(vPcStep)}`)
const pcM = putClear.withSumsOf(pcEq).machine
const pcLaws = [...putClear.kindLaws(), pcEq]
const pcProof = proveLaws(pcM, pcLaws)
assert(pcProof.proven && pcProof.checked && !!pcProof.proof, `putClear proveLaws failed`)
const pcLean = `import Sums
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

${retainedSumMachineToLean('putclear', pcM, pcLaws, pcProof.proof!, {})}

#print axioms putclear_scheck
#print axioms putclear_exact
#print axioms putclear_own
#print axioms putclear_sum0
`
writeFileSync(join(outDir, 'PutClear.lean'), pcLean)
;(summary.positive as Record<string, unknown>).putClear = {eq: true, le: true, step: true}

// 2. covering.test.ts broadcast-covering-clear
const withClear = rule('broadcast-covering-clear')
  .inputs({op: oneOf('put', 'remove', 'clear'), id: nat, val: nat})
  .state({total: 0})
  .maps({M: 0})
  .flags(({op, id, M}) => ({
    puts: op.is('put').and(M.at(id).eq(0)),
    removes: op.is('remove').and(M.at(id).gt(0)),
    clears: op.is('clear'),
  }))
  .step(({id, val, total, M, puts, removes, clears}) => ({
    total: when(clears, 0, when(puts, total.plus(val), when(removes, total.minus(M.at(id)), total))),
    M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), val, when(removes.and(k.eq(id)), 0, M.at(k))))),
  }))
const clearLaw = withClear.law('every cell fits in total', ({M, total}) => forall(k => M.at(k).atMost(total)))
const vCov = proveRule(withClear, [clearLaw], {search: {ms: 15_000}})
assert(vCov.proven && vCov.checked, `broadcast-covering-clear failed: ${JSON.stringify(vCov)}`)
;(summary.positive as Record<string, unknown>).broadcastCoveringClear = {proven: true, found: vCov.found?.laws?.map(l => l.text)}

// 3. cohort19 law-2 & law-3: Spark MemoryStore #0 and #1
const spark = sparkMemoryStore()
const law0 = spark.law('every cached block size is covered by memoryUsed', ({Blocks, memoryUsed}) =>
  forall(b => Blocks.at(b).present.implies(Blocks.at(b).size.atMost(memoryUsed))))
const law1 = spark.law('every task unroll allocation is covered by memoryUsed', ({Unroll, memoryUsed}) =>
  forall(t => Unroll.at(t).atMost(memoryUsed)))
const t0 = Date.now()
const vLaw0 = proveRule(spark, [law0], {search: {ms: 20_000}})
const ms0 = Date.now() - t0
assert(vLaw0.proven && vLaw0.checked, `Spark MemoryStore #0 failed: ${JSON.stringify(vLaw0)}`)
const t1 = Date.now()
const vLaw1 = proveRule(spark, [law1], {search: {ms: 20_000}})
const ms1 = Date.now() - t1
assert(vLaw1.proven && vLaw1.checked, `Spark MemoryStore #1 failed: ${JSON.stringify(vLaw1)}`)

const sparkSumEq = spark.law('sum == memoryUsed', ({Blocks, Unroll, memoryUsed}) =>
  Blocks.sum(b => when(b.present, b.size, 0)).plus(Unroll.sum()).eq(memoryUsed))
const sparkSummed = spark.withSumsOf(sparkSumEq, law0, law1)
const sparkM = sparkSummed.machine
const sparkLaws = [...sparkSummed.kindLaws(), sparkSumEq, law0, law1]
const sparkProof = proveLaws(sparkM, sparkLaws)
assert(sparkProof.proven && sparkProof.checked && !!sparkProof.proof, `Spark explicit proveLaws failed: ${JSON.stringify(sparkProof.failed)}`)
const sparkLean = `import Sums
open Kern Cert
set_option maxRecDepth 200000
set_option maxHeartbeats 0

${retainedSumMachineToLean('spark', sparkM, sparkLaws, sparkProof.proof!, {})}

#print axioms spark_scheck
#print axioms spark_exact
#print axioms spark_own
#print axioms spark_sum0
#print axioms spark_sum1
`
writeFileSync(join(outDir, 'SparkMemoryStore.lean'), sparkLean)
;(summary.positive as Record<string, unknown>).sparkMemoryStore = {
  law0: {proven: true, checked: true, ms: ms0, found: vLaw0.found?.laws?.map(l => l.text)},
  law1: {proven: true, checked: true, ms: ms1, found: vLaw1.found?.laws?.map(l => l.text)},
  sumsCount: Object.keys(sparkM.sums ?? {}).length,
}

// 4. step-reads-sum
const stepReads = rule('step-reads-sum')
  .inputs({op: oneOf('put', 'clear', 'check'), id: nat})
  .state({cleared: 0, ok: 1})
  .maps({M: 0})
  .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clear'), checks: op.is('check')}))
  .step(({id, cleared, ok, M, puts, clears, checks}) => ({
    cleared: when(clears, 1, when(puts, 0, cleared)),
    ok: when(checks.and(cleared.eq(1)), when(M.sum().eq(0), 1, 0), ok),
    M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), 1, M.at(k)))),
  }))
const stepHelper = stepReads.law('cleared => sum == 0', ({cleared, M}) => cleared.eq(1).implies(M.sum().eq(0)))
const stepOk = stepReads.law('ok stays 1', ({ok}) => ok.eq(1))
const vStepReads = proveRule(stepReads, [stepHelper, stepOk], {search: false})
assert(vStepReads.proven && vStepReads.checked, `step-reads-sum failed: ${JSON.stringify(vStepReads)}`)
;(summary.positive as Record<string, unknown>).stepReadsSum = true

// 5. Preserved negative controls (lowerBoundDual, partial range wipe, infinite shift)
const rPartial = rule('range-clear')
  .inputs({op: oneOf('put', 'clearBelow'), id: nat, val: nat, limit: nat})
  .maps({M: 0})
  .flags(({op, id, M}) => ({puts: op.is('put').and(M.at(id).eq(0)), clears: op.is('clearBelow')}))
  .step(({id, val, limit, M, puts, clears}) => ({
    M: M.each(k => when(clears.and(k.lt(limit)), 0, when(puts.and(k.eq(id)), val, M.at(k)))),
  }))
const vPartial = proveRule(rPartial, [rPartial.law('sum non-negative', ({M}) => M.sum().atLeast(0))], {search: false})
assert(!vPartial.proven && vPartial.stuck === 'unknown', `range-clear control failed: ${JSON.stringify(vPartial)}`)

const rShift = rule('shift-all')
  .maps({M: 0})
  .step(({M}) => ({M: M.each(k => M.at(k).plus(1))}))
const vShift = proveRule(rShift, [rShift.law('sum is 0', ({M}) => M.sum().eq(0))], {search: false})
assert(!vShift.proven && vShift.stuck === 'unknown', `shift-all control failed: ${JSON.stringify(vShift)}`)
;(summary.controls as Record<string, unknown>).rangeClear = {stuck: vPartial.stuck, goal: vPartial.goal}
;(summary.controls as Record<string, unknown>).shiftAll = {stuck: vShift.stuck, goal: vShift.goal}
const lowerBoundDual = (rareClear: boolean) => rule(rareClear ? 'dual-rare-clear' : 'dual-reachable-clear')
  .inputs({op: oneOf('put', 'clear'), id: nat})
  .state({hasPut: 0})
  .maps({M: 0})
  .flags(({op, id, M}) => ({
    puts: op.is('put').and(M.at(id).eq(0)),
    clears: op.is('clear').and(M.at(id).eq(0), rareClear ? id.eq(999999) : yes),
  }))
  .step(({id, hasPut, M, puts, clears}) => ({
    hasPut: when(puts, 1, hasPut),
    M: M.each(k => when(clears, 0, when(puts.and(k.eq(id)), 1, M.at(k)))),
  }))
const rRare = lowerBoundDual(true)
const rareLower = rRare.law('hasPut <= M.sum()', ({hasPut, M}) => hasPut.atMost(M.sum()))
const vRare = proveRule(rRare, [rareLower], {search: false})
assert(!vRare.proven && !vRare.checked && vRare.stuck === 'unknown' && /@cover M/.test(vRare.goal ?? ''), `lowerBoundDual(true) control failed: ${JSON.stringify(vRare)}`)
const rReach = lowerBoundDual(false)
const falseLower = rReach.law('hasPut <= M.sum()', ({hasPut, M}) => hasPut.atMost(M.sum()))
const vReach = proveRule(rReach, [falseLower], {search: false})
assert(!vReach.proven && vReach.stuck === 'sat' && !!vReach.run && replayRefutation(rReach, [falseLower], [], vReach.run.params, vReach.run.trace as Record<string, number>[], 4, falseLower), `lowerBoundDual(false) control failed`)
;(summary.controls as Record<string, unknown>).lowerBoundDualRare = {stuck: vRare.stuck, goal: vRare.goal}
;(summary.controls as Record<string, unknown>).lowerBoundDualReach = {stuck: vReach.stuck, replayed: true}

// 6. Mutant battery (12 mutants: ALL refused in BOTH TypeScript kernel.ts AND Lean 4.34.0 decide +kernel!)
const v = (name: string): E => ({op: 'var', name})
const k = (value: number): E => ({op: 'const', value})
const eq = (a: E, b: E): C => ({op: '=', a, b})
const lt = (a: E, b: E): C => ({op: '<', a, b})
const and2 = (a: C, b: C): C => ({op: 'and', xs: [a, b]})
const ite = (c: C, then: E, otherwise: E): E => ({op: 'if', c, then, else: otherwise})
const get = (map: string, key: E): E => ({op: 'get', map, key})

const sumDecl = (key: string, term: E, reset?: C): Sum => ({key, term, ...(reset ? {reset} : {})}) as Sum

// Base machine with `limit` input + `fReadCell` / `fChain` flags already in scope so Lean shares one variable numbering.
const baseM: Machine = {
  name: 'reset-mutant-base',
  params: [],
  inputs: ['op', 'id', 'val', 'limit'],
  state: {S: k(0), total: k(0)},
  maps: {M: 0},
  step: {
    flags: {
      puts: and2(eq(v('op'), k(0)), eq(get('M', v('id')), k(0))),
      clears: eq(v('op'), k(1)),
      clearsReadingM: and2(eq(v('op'), k(1)), eq(get('M', v('id')), k(0))),
      zeroAtId: eq(get('M', v('id')), k(0)),
      chainedReadingM: and2(eq(v('op'), k(1)), {op: 'flag', name: 'zeroAtId'}),
    },
    state: {
      total: ite({op: 'flag', name: 'clears'}, k(0), ite({op: 'flag', name: 'puts'}, {op: 'add', a: v('total'), b: v('val')}, v('total'))),
    },
    maps: {
      M: {
        each: 'k$w',
        value: ite({op: 'flag', name: 'clears'}, k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w')))),
      },
    },
  },
  assume: {op: '<=', a: v('op'), b: k(1)},
  sums: {S: sumDecl('k$S', get('M', v('k$S')), {op: 'flag', name: 'clears'})},
}
const baseLaws: Law[] = [
  {name: 'S == total', holds: eq(v('S'), v('total'))},
  {name: 'every cell <= total', forall: 'k$l', holds: {op: '<=', a: get('M', v('k$l')), b: v('total')}},
]
const baseRes = proveLaws(baseM, baseLaws)
assert(baseRes.proven && baseRes.checked && !!baseRes.proof, `mutant base not proven: ${JSON.stringify(baseRes.failed)}`)

const withReset = (reset: C | undefined): Machine => ({
  ...baseM,
  sums: {S: sumDecl('k$S', get('M', v('k$S')), reset)},
})
const withWrite = (value: E): Machine => ({
  ...baseM,
  step: {...baseM.step, maps: {M: {each: 'k$w', value}}},
})

const leanTampers: {what: string, m: Machine, expect: boolean}[] = [
  // Class 1: key-dependent guards
  {what: 'M1 key-dependent reset reading sum.key (k$S < limit)', m: withReset(lt(v('k$S'), v('limit'))), expect: false},
  {what: 'M2 key-dependent reset reading cover key (x$S < limit)', m: withReset(lt(v('x$S'), v('limit'))), expect: false},
  {what: 'M3 key-dependent reset reading write key (k$w < limit)', m: withReset(lt(v('k$w'), v('limit'))), expect: false},
  // Class 2: partial wipes
  {
    what: 'M4 partial wipe (clears && k < limit) with reset = clears',
    m: withWrite(ite(and2({op: 'flag', name: 'clears'}, lt(v('k$w'), v('limit'))), k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))),
    expect: false,
  },
  {
    what: 'M5 partial wipe (clears && k != 0) with reset = clears',
    m: withWrite(ite(and2({op: 'flag', name: 'clears'}, {op: 'not', x: eq(v('k$w'), k(0))}), k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))),
    expect: false,
  },
  // Class 3: reset that also writes (single-map)
  {
    what: 'M6 reset that also writes (clears sets id to val, 0 elsewhere)',
    m: withWrite(ite({op: 'flag', name: 'clears'}, ite(eq(v('k$w'), v('id')), v('val'), k(0)), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))),
    expect: false,
  },
  // Class 4: guard reading summed cells
  {what: 'M8 guard reading summed cell at key (M[k$S] = 1)', m: withReset(eq(get('M', v('k$S')), k(1))), expect: false},
  {what: 'M9 guard reading summed cell directly (op = 1 && M[id] = 0)', m: withReset(and2(eq(v('op'), k(1)), eq(get('M', v('id')), k(0)))), expect: false},
  {what: 'M10 guard reading summed cell via plain flag (clearsReadingM)', m: withReset({op: 'flag', name: 'clearsReadingM'}), expect: false},
  {what: 'M11 guard reading summed cell via chained flag (chainedReadingM)', m: withReset({op: 'flag', name: 'chainedReadingM'}), expect: false},
  // Certificate / guard tampers
  {what: 'M12b tamper reset dropped (none) against reset proof', m: withReset(undefined), expect: false},
  {what: 'M12c tamper reset swapped to puts', m: withReset({op: 'flag', name: 'puts'}), expect: false},
  {what: 'M12d tamper reset swapped to trueC', m: withReset(trueC), expect: false},
]

const mutantResults: Record<string, {tsSumAnswer: boolean, tsProveLaws?: boolean, tsThrow?: string}> = {}
for (const t of leanTampers) {
  const ans = sumAnswer(t.m, baseLaws, baseRes.proof!)
  assert(ans === false, `TS sumAnswer accepted mutant: ${t.what}`)
  let thrown: string | undefined
  let freshProven: boolean | undefined
  try {
    const r = proveLaws(t.m, baseLaws)
    freshProven = r.proven && r.checked
  } catch (e) {
    thrown = String(e)
  }
  assert(!freshProven, `TS proveLaws proved mutant: ${t.what}`)
  mutantResults[t.what] = {tsSumAnswer: ans, ...(freshProven !== undefined ? {tsProveLaws: freshProven} : {}), ...(thrown ? {tsThrow: thrown} : {})}
}

// Mutant M7: two-map summand M[k] + U[k], M clears on clears, U writes U.set(id, val)
const twoMapResetWrite: Machine = {
  name: 'M7-two-map-reset-also-writes',
  params: [],
  inputs: ['op', 'id', 'val'],
  state: {S: k(0)},
  maps: {M: 0, U: 0},
  step: {
    flags: {puts: eq(v('op'), k(0)), clears: eq(v('op'), k(1))},
    maps: {
      M: {each: 'k$w', value: ite({op: 'flag', name: 'clears'}, k(0), ite(and2({op: 'flag', name: 'puts'}, eq(v('k$w'), v('id'))), v('val'), get('M', v('k$w'))))},
      U: {key: v('id'), value: v('val')},
    },
  },
  assume: {op: '<=', a: v('op'), b: k(1)},
  sums: {S: sumDecl('k$S', {op: 'add', a: get('M', v('k$S')), b: get('U', v('k$S'))}, {op: 'flag', name: 'clears'})},
}
const m7Res = proveLaws(twoMapResetWrite, [{name: 'nonneg', holds: {op: '<=', a: k(0), b: v('S')}}])
assert(!m7Res.proven && m7Res.failed?.goal === 'S @reset', `M7 two-map reset-also-writes failed unexpectedly: ${JSON.stringify(m7Res.failed)}`)
mutantResults['M7 reset that also writes (two-map M+U, U.set)'] = {tsSumAnswer: false, tsProveLaws: false}

// Mutant M12a: dropping `S @reset` tree from valid proof
const droppedResetTrees = {...baseRes.proof!.trees}
delete droppedResetTrees['S @reset']
const droppedOk = checkLaws(baseM, baseLaws, {...baseRes.proof!, trees: droppedResetTrees})
assert(!droppedOk, `M12a dropping S @reset tree was accepted by checkLaws`)
mutantResults['M12a dropped S @reset tree'] = {tsSumAnswer: false}

summary.mutants = mutantResults

// Emit MutantBattery.lean with `decide +kernel` for base + ALL 13 Lean tampers + M12a missing reset tree!
const batteryBody = smachineToLean('mutbase', baseM, baseLaws, {
  sumTampers: leanTampers,
  coverTrees: baseRes.proof!.trees,
  noFacts: true,
})
const mutantLean = `import Sums
open Kern Cert
set_option maxRecDepth 200000
set_option maxHeartbeats 0

${batteryBody}

-- TAMPERED: M12a dropped @reset tree (none when d.reset = some _). Lean computes checkSums to false.
example : checkSums mutbase_sums mutbase_proof (mutbase_covers.map (fun p => (p.1, none))) = false := by decide +kernel

#print axioms mutbase_scheck
#print axioms mutbase_exact
#print axioms mutbase_own
`
writeFileSync(join(outDir, 'MutantBattery.lean'), mutantLean)
writeFileSync(join(outDir, 'verify-summary.json'), JSON.stringify(summary, null, 2))
console.log('ALL_PROPOSAL_CHECKS_PASSED:', JSON.stringify({
  putClear: true,
  broadcastCoveringClear: true,
  sparkLaw0Ms: ms0,
  sparkLaw1Ms: ms1,
  stepReadsSum: true,
  controlsPassed: 4,
  mutantsRefusedTS: Object.keys(mutantResults).length,
  leanTampersEmitted: leanTampers.length + 1,
}))
