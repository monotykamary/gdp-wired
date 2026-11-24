// Model-based testing with @xstate/graph from a proven rule (core/xstate.ts):
//   - Credit wallet rule (no XState in the app): reservations never exceed credits, proven from any state.
//   - toLogic(wallet) presents the proven rule as XState v5 ActorLogic (copied states via rule.interpreter(), canonical
//     serializeState over scalars and maps, small-edge default event generator).
//   - @xstate/graph's TestModel generates shortest paths covering reachable states and drives a hand-written wallet
//     implementation along each path: the correct implementation passes every path; a buggy one (reserve without the
//     credits check) fails.
//   - The broken twin's proveRule counterexample run becomes XState events via runToEvents -> getPathsFromEvents ->
//     testPath, turning the prover's refutation into a regression test that fails the buggy wallet and passes the
//     correct one.
import {TestModel} from '@xstate/graph'
import {nat, oneOf, proveRule, rule, when} from '../core/dsl.ts'
import {type RuleEvent, runToEvents, toLogic} from '../core/xstate.ts'

export const makeWallet = (broken = false) => rule('credit wallet')
  .inputs({op: oneOf('reserve', 'release', 'spend', 'topUp'), id: nat, amount: nat})
  .state({credits: 0, reserved: 0})
  .maps({Held: 0})
  .flags(({op, id, amount, credits, reserved, Held}) => ({
    reserves: op.is('reserve').and(amount.gt(0), Held.at(id).eq(0), broken ? amount.gt(0) : reserved.plus(amount).atMost(credits)),
    releases: op.is('release').and(Held.at(id).gt(0)),
    spends: op.is('spend').and(Held.at(id).gt(0)),
  }))
  .step(({op, id, amount, credits, reserved, Held, reserves, releases, spends}) => ({
    credits: when(spends, credits.minus(Held.at(id)), when(op.is('topUp'), credits.plus(amount), credits)),
    reserved: when(reserves, reserved.plus(amount), when(releases.or(spends), reserved.minus(Held.at(id)), reserved)),
    Held: Held.set(id, when(reserves, amount, when(releases.or(spends), 0, Held.at(id)))),
  }))

export const wallet = makeWallet()
export const uncheckedWallet = makeWallet(true)
export const walletCovered = wallet.law('reservations never exceed the credits', ({credits, reserved}) => reserved.atMost(credits))

// A hand-written wallet implementation (the real app under test). Bug modes:
//   - true / 'no-credits-check': reserve forgets `reserved + amount <= credits` (missing guard, self-loop in model)
//   - 'reserve-skips-reserved': reserve records Held without updating `reserved` (caught by getShortestPaths)
//   - 'spend-keeps-reserved': spend forgets to decrement `reserved` (caught by transition coverage / getAdjacencyMap)
export type WalletBug = false | true | 'no-credits-check' | 'reserve-skips-reserved' | 'spend-keeps-reserved'
export class AppWallet {
  credits = 0
  reserved = 0
  held = new Map<number, number>()
  constructor(private readonly bug: WalletBug = false) {}

  topUp(amount: number): void { this.credits += amount }
  reserve(id: number, amount: number): boolean {
    if (amount <= 0 || (this.held.get(id) ?? 0) !== 0) return false
    const skipCheck = this.bug === true || this.bug === 'no-credits-check'
    if (!skipCheck && this.reserved + amount > this.credits) return false
    if (this.bug !== 'reserve-skips-reserved') this.reserved += amount
    this.held.set(id, amount)
    return true
  }
  release(id: number): boolean {
    const h = this.held.get(id) ?? 0
    if (h <= 0) return false
    this.reserved -= h
    this.held.delete(id)
    return true
  }
  spend(id: number): boolean {
    const h = this.held.get(id) ?? 0
    if (h <= 0) return false
    this.credits -= h
    if (this.bug !== 'spend-keeps-reserved') this.reserved -= h
    this.held.delete(id)
    return true
  }
  snapshot(): {credits: number, reserved: number, Held: Record<string, number>} {
    const entries = [...this.held.entries()].filter(([, v]) => v !== 0).sort((a, b) => a[0] - b[0])
    return {credits: this.credits, reserved: this.reserved, Held: Object.fromEntries(entries.map(([k, v]) => [String(k), v]))}
  }
}

export function walletHarness(bug: WalletBug = false) {
  let app = new AppWallet(bug)
  const payload = (ev: unknown) => ev as RuleEvent & {id: number, amount: number}
  return {
    states: {
      '*': (snap: {context: Record<string, unknown>}) => {
        const got = app.snapshot()
        const want = {credits: snap.context.credits, reserved: snap.context.reserved, Held: snap.context.Held}
        if (JSON.stringify(got) !== JSON.stringify(want)) {
          throw new Error(`app wallet ${JSON.stringify(got)} !== proven rule ${JSON.stringify(want)}`)
        }
      },
    },
    events: {
      'xstate.init': () => { app = new AppWallet(bug) },
      topUp: ({event}: {event: unknown}) => { app.topUp(payload(event).amount) },
      reserve: ({event}: {event: unknown}) => { const e = payload(event); app.reserve(e.id, e.amount) },
      release: ({event}: {event: unknown}) => { app.release(payload(event).id) },
      spend: ({event}: {event: unknown}) => { app.spend(payload(event).id) },
    },
  }
}

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const proved = proveRule(wallet, [walletCovered], {from: 'any'})
  results.push(['wallet proven from any state', proved.proven && proved.checked && !proved.assumes, true])

  const brokenLaw = uncheckedWallet.law('reservations never exceed the credits', ({credits, reserved}) => reserved.atMost(credits))
  const broken = proveRule(uncheckedWallet, [brokenLaw])
  results.push(['broken wallet refuted with a run', !broken.proven && !!broken.run, true])

  const logic = toLogic(wallet, {maxValue: 2})
  const model = new TestModel(logic, logic.options)
  const paths = model.getShortestPaths()
  results.push([`generated ${paths.length} shortest paths`, paths.length > 10, true])

  let correctOk = true
  for (const p of paths) {
    try { await model.testPath(p, walletHarness(false)) }
    catch { correctOk = false; break }
  }
  results.push(['correct hand-written wallet passes every shortest path', correctOk, true])

  // Transition coverage (shortest paths extended by every outgoing edge from getAdjacencyMap, including self-loops
  // where the proven rule ignores an over-budget reserve) catches missing guards as well as wrong state updates.
  const adj = model.getAdjacencyMap()
  const transitionPaths = model.getShortestPaths({allowDuplicatePaths: true}).flatMap(p =>
    Object.values(adj[logic.serializeState(p.state) as keyof typeof adj]?.transitions ?? {}).map(t => ({
      ...p, state: t.state, steps: [...p.steps, {event: t.event, state: t.state}], weight: p.weight + 1,
    })),
  )
  let buggyFailed = false
  for (const p of transitionPaths) {
    try { await model.testPath(p, walletHarness('no-credits-check')) }
    catch { buggyFailed = true; break }
  }
  results.push(['buggy hand-written wallet (no credits check) fails transition coverage', buggyFailed, true])

  const ceEvents = runToEvents(uncheckedWallet, broken.run!)
  const cePaths = model.getPathsFromEvents(ceEvents)
  let ceCorrectOk = true
  try { await model.testPath(cePaths[0]!, walletHarness(false)) } catch { ceCorrectOk = false }
  let ceBuggyFailed = false
  try { await model.testPath(cePaths[0]!, walletHarness('no-credits-check')) } catch { ceBuggyFailed = true }
  results.push(['counterexample regression path passes correct wallet', ceCorrectOk, true])
  results.push(['counterexample regression path fails buggy wallet', ceBuggyFailed, true])

  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
