// Transactions (Effect 4's TxRef and Effect.tx, Effect 3's STM and TRef, read by gdp-wired/effect): for the suite
// (`bun examples/effect-stm.ts`) and core/effect-stm.test.ts. Two accounts holding 100 between them (examples/
// effect-bank.ts on Effect 4, the same bank in STM on Effect 3):
//   - each method one transaction, a step of the rule: calls from any number of fibers are any order of those steps,
//     so the laws proven of the rule hold under any interleaving: the money is conserved, checking is never overdrawn.
//     spend waits (Effect.txRetry, STM.check) until the savings cover it, a guard: the step isn't taken until then;
//   - broken: save reads the balance in one transaction and writes it in another (a sleep, an audit call, between).
//     Read as two steps of each fiber, every fiber's (lift), "the money is conserved" is refuted by a run of two
//     fibers interleaving; and the same two saves, run concurrently on Effect's runtime, end with more than 100.
import {readFileSync} from 'node:fs'
import {fileURLToPath} from 'node:url'
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
import {type Law} from '../core/machine.ts'
import {proveRule} from '../core/dsl.ts'
import {type Extraction} from '../core/extract.ts'
import {extractEffect, fiberRun} from '../core/effect.ts'
import {inProject} from './effect-retry.ts'

export const bankFile = fileURLToPath(new URL('./effect-bank.ts', import.meta.url))
const SAVE4 = /  const save = Effect\.fn\('Bank\.save'\)\(function\* \(amount: number\) \{[\s\S]*?\n  \}\)\n/
// The bank on Effect 4, as written; broken, save reads in one transaction and writes in another.
export const bank4 = (bug?: 'two transactions') => {
  const code = readFileSync(bankFile, 'utf8')
  return bug ? code.replace(SAVE4, `  const save = Effect.fn('Bank.save')(function* (amount: number) {
    if (amount < 0) return yield* new Insufficient({amount})
    const balance = yield* TxRef.get(checking)
    if (balance < amount) return yield* new Insufficient({amount})
    yield* Effect.sleep('1 millis')
    yield* Effect.tx(Effect.gen(function* () {
      yield* TxRef.set(checking, balance - amount)
      yield* TxRef.update(savings, s => s + amount)
    }))
  })
`) : code
}
// The bank on Effect 3: STM.gen transactions, STM.check to wait.
export const bank3 = (bug?: 'two transactions') => `import {Data, Effect, STM, TRef} from 'effect'
export class Insufficient extends Data.TaggedError('Insufficient')<{readonly amount: number}> {}
export const make = Effect.gen(function* () {
  const checking = yield* TRef.make(100)
  const savings = yield* TRef.make(0)
  const save = Effect.fn('Bank.save')(function* (amount: number) {
    if (amount < 0) return yield* Effect.fail(new Insufficient({amount}))
${bug ? `    const balance = yield* TRef.get(checking)
    if (balance < amount) return yield* Effect.fail(new Insufficient({amount}))
    yield* Effect.sleep('1 millis')
    yield* STM.gen(function* () {
      yield* TRef.set(checking, balance - amount)
      yield* TRef.update(savings, s => s + amount)
    })` : `    yield* STM.gen(function* () {
      const balance = yield* TRef.get(checking)
      if (balance < amount) return yield* STM.fail(new Insufficient({amount}))
      yield* TRef.set(checking, balance - amount)
      yield* TRef.update(savings, s => s + amount)
    })`}
  })
  const spend = (amount: number) => STM.gen(function* () {
    const s = yield* TRef.get(savings)
    yield* STM.check(() => amount >= 0 && s >= amount)
    yield* TRef.set(savings, s - amount)
    yield* TRef.update(checking, c => c + amount)
  }).pipe(STM.commit)
  return {save, spend}
})
`
export const readBank = (v: 3 | 4, bug?: 'two transactions'): {x: Extraction, file: string} => {
  const file = v === 4 && !bug ? bankFile : inProject(v, 'bank.ts', v === 4 ? bank4(bug) : bank3(bug))
  return {x: extractEffect(file, {entry: 'make'}), file}
}
export const bankLaws = (r: Any): Law[] => [
  r.law('the money is conserved', ({checking, savings}: Any) => checking.plus(savings).eq(100)),
  r.law('checking is never overdrawn', ({checking}: Any) => checking.atLeast(0)),
]
// Two saves of 10 at once on Effect's runtime (real fibers, the sleep between the two transactions real too), and what
// the accounts hold after: the service run as written, its make effect also handing out its refs to read them.
export async function raceSaves(v: 3 | 4, file: string): Promise<{checking: number, savings: number}> {
  const ref = v === 4 ? 'TxRef' : 'TRef'
  const code = `${readFileSync(file, 'utf8').replace(/return \{save, spend\}/, 'return {save, spend, checking, savings}')}
export const race = () => Effect.runPromise(Effect.gen(function* () {
  const bank = yield* make
  yield* Effect.all([bank.save(10), bank.save(10)], {concurrency: 'unbounded'})
  return {checking: yield* ${ref}.get(bank.checking), savings: yield* ${ref}.get(bank.savings)}
}))
`
  const mod = await import(inProject(v, 'race.ts', code)) as {race: () => Promise<{checking: number, savings: number}>}
  return mod.race()
}

if (import.meta.main) {
  const results: [string, boolean, boolean][] = [], runs: string[] = []
  for (const v of [4, 3] as const) {
    const {x} = readBank(v), r = x.rule as Any
    results.push([`bank (Effect ${v}): read and checked on the runtime (${x.evidence?.requests} requests)`, x.ok, true])
    for (const l of bankLaws(r)) { const p = proveRule(r, [...x.invariants ?? [], l]); results.push([`bank (Effect ${v}): ${l.name}`, p.proven && p.checked, true]) }
    const b = readBank(v, 'two transactions'), br = b.x.rule as Any
    results.push([`bank with save in two transactions (Effect ${v}): read as every fiber's steps`, b.x.ok && /every fiber/.test(br?.machine.name ?? ''), true])
    const bv = proveRule(br, [...b.x.invariants ?? [], bankLaws(br)[0]!])
    results.push([`bank with save in two transactions (Effect ${v}): the money is conserved`, bv.proven, false])
    const raced = await raceSaves(v, b.file)
    if (bv.run) runs.push(`two transactions (Effect ${v}): ${fiberRun(b.x, bv.run).join('; ')}; on the runtime, two saves of 10 at once leave checking ${raced.checking} and savings ${raced.savings}: ${raced.checking + raced.savings} in all`)
    results.push([`bank with save in two transactions (Effect ${v}): two saves at once on the runtime keep 100`, raced.checking + raced.savings === 100, false])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  for (const r of runs) console.log(`     ${r}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
