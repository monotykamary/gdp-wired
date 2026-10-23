// The extractor (core/extract.ts): rules read from TypeScript and JavaScript, each checked against the code it was read
// from. The subset's shapes extract and agree with the code on every request; programs where a naive reading would be
// wrong (aliasing, mutation through a reference, overflow, floats, NaN, short-circuit effects, a throw mid-update,
// getters with effects, closures over mutable state) are each refused with the reason, or extracted and checked.
import {expect, test} from 'bun:test'
import {extract, type Extraction} from './extract.ts'
import {proveRule} from './dsl.ts'

const budget = {runs: 60, depth: 10, states: 150}
const ok = (x: Extraction) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}`)
  expect(x.evidence!.mismatch).toBeUndefined()
  return x
}
const refused = (x: Extraction, why: RegExp) => {
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toMatch(why)
}
const ts = (code: string, entry: string, more = {}) => extract(code, {file: 'case.ts', entry, check: budget, ...more})

// --- the subset -----------------------------------------------------------------------------------------------------
test('a reducer over a discriminated union: switch, spreads, Math.max, a throw as the assumption', () => {
  const x = ok(ts(`
    type State = {count: number, step: number}
    type Action = {type: 'increment'} | {type: 'decrement'} | {type: 'setStep', step: number} | {type: 'reset'}
    export const initialState: State = {count: 0, step: 1}
    export function reducer(state: State, action: Action): State {
      switch (action.type) {
        case 'increment': return {...state, count: state.count + state.step}
        case 'decrement': return {...state, count: Math.max(0, state.count - state.step)}
        case 'setStep':
          if (action.step < 1) throw new Error('step must be positive')
          return {...state, step: action.step}
        case 'reset': return initialState
      }
    }`, 'reducer'))
  expect(x.source).toContain(".assume(({type, action_step}) => type.is('setStep').implies(action_step.atLeast(1)))")
  expect(x.source).toContain('action_step: nat')
  expect(x.evidence!.requests).toBeGreaterThan(0)
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms - 1) // the switch's no-case arm: the union's types rule it out
  const r = x.rule!
  expect(proveRule(r, [r.law('the step stays at least 1', ({step}: any) => step.atLeast(1))]).proven).toBe(true)
})

test('a class with a keyed map: get or create, refill by elapsed seconds, a result kept', () => {
  const x = ok(ts(`
    type Bucket = {tokens: number, last: number}
    export class KeyedLimiter {
      private buckets = new Map<string, Bucket>()
      constructor(private readonly capacity: number, private readonly refillPerSec: number) {
        if (capacity < 1) throw new Error('capacity must be at least 1')
        if (refillPerSec < 0) throw new Error('refill must not be negative')
      }
      tryRemove(key: string, n: number): boolean {
        if (n < 1) throw new Error('n must be at least 1')
        const now = Date.now()
        let b = this.buckets.get(key)
        if (!b) { b = {tokens: this.capacity, last: now}; this.buckets.set(key, b) }
        const elapsed = Math.max(0, Math.floor((now - b.last) / 1000))
        b.tokens = Math.min(this.capacity, b.tokens + elapsed * this.refillPerSec)
        b.last = now
        if (b.tokens < n) return false
        b.tokens -= n
        return true
      }
    }`, 'KeyedLimiter'))
  expect(x.source).toContain('.pre(({capacity, refillPerSec}) => all(capacity.atLeast(1), refillPerSec.atLeast(0)))')
  expect(x.source).toContain('record({has: bool, tokens: nat, last: nat})')
  expect(x.evidence!.coverage).toMatchObject({hit: 10, arms: 10})
  // Its representation: a key the map doesn't hold holds the defaults, inductive.
  expect(x.invariants!.map(l => l.name)).toEqual(["buckets: a key it doesn't hold holds the defaults"])
  expect(proveRule(x.rule!, x.invariants!)).toMatchObject({proven: true, checked: true})
})

test('a wallet: debit refused past the balance, a getter, a counter of calls', () => {
  const x = ok(ts(`
    export class Wallet {
      balance = 0
      ops = 0
      get spendable(): number { return this.balance }
      credit(x: number): void { if (x <= 0) throw new Error('positive'); this.balance += x; this.ops++ }
      debit(x: number): boolean {
        if (x <= 0) throw new Error('positive')
        if (x > this.spendable) return false
        this.balance -= x
        this.ops++
        return true
      }
    }`, 'Wallet'))
  const r = x.rule!
  expect(x.source).toContain('balance: 0')
  expect(proveRule(r, [r.law('the balance never goes below 0', ({balance}: any) => balance.atLeast(0))]).proven).toBe(true)
})

test('plain JavaScript: a Redux reducer with an untyped action and a default for unknown actions', () => {
  const x = ok(extract(`
    export default function counter(state = 0, action) {
      switch (action.type) {
        case 'INCREMENT': return state + 1
        case 'DECREMENT': return state - 1
        default: return state
      }
    }`, {file: 'counter.js', entry: 'default', check: budget}))
  expect(x.source).toContain("type: oneOf('INCREMENT', 'DECREMENT', '@@other')")
  expect(x.source).toContain('state: int.from(0)')
  expect(x.evidence!.coverage.missed).toEqual([])
})

test('useReducer: the initial state from the hook, a string-literal union, an exhaustive throw', () => {
  const x = ok(ts(`
    type Phase = 'idle' | 'running' | 'done'
    type State = {phase: Phase, ticks: number}
    type Action = {type: 'start'} | {type: 'tick'} | {type: 'stop'}
    function reducer(state: State, action: Action): State {
      if (action.type === 'start') { if (state.phase !== 'idle') throw new Error('already started'); return {phase: 'running', ticks: 0} }
      if (action.type === 'tick') return state.phase === 'running' ? {...state, ticks: state.ticks + 1} : state
      return {...state, phase: state.phase === 'running' ? 'done' : state.phase}
    }
    export function Timer() { const [s, dispatch] = useReducer(reducer, {phase: 'idle', ticks: 0}); return s }
    declare function useReducer<S, A>(r: (s: S, a: A) => S, init: S): [S, (a: A) => void]`, 'reducer'))
  expect(x.source).toContain("phase: oneOf('idle', 'running', 'done').from('idle')")
})

test('functions over one record, each an event; a Record keyed by strings with ?? 0', () => {
  ok(ts(`
    type Ledger = {balances: Record<string, number>, total: number}
    export function deposit(l: Ledger, who: string, amount: number): Ledger {
      if (amount <= 0) throw new Error('positive')
      return {...l, balances: {...l.balances, [who]: (l.balances[who] ?? 0) + amount}, total: l.total + amount}
    }
    export function withdraw(l: Ledger, who: string, amount: number): Ledger {
      const have = l.balances[who] ?? 0
      if (amount <= 0 || amount > have) throw new Error('refused')
      return {...l, balances: {...l.balances, [who]: have - amount}, total: l.total - amount}
    }`, 'deposit', {functions: ['deposit', 'withdraw'], init: {balances: {}, total: 0}}))
})

test('what the subset does not read is refused where it is, with the reason', () => {
  refused(ts('export function r(s: {xs: number[]}, a: {type: "push"}) { return s }', 'r', {init: {xs: []}}), /an array/)
  refused(ts('export function r(s: {n: number}, a: {k: number}): {n: number} { for (let i = 0; i < a.k; i++) {} return s }', 'r', {init: {n: 0}}), /a loop/)
  refused(ts('export class C { n = 0; async go(): Promise<void> { this.n++ } }', 'C'), /async/)
  refused(ts('export function r(s: {n: number}, a: {k: number}): {n: number} { try { return s } catch { return s } }', 'r', {init: {n: 0}}), /try\/catch/)
  refused(ts("export function r(s: {n: number}, a: {k: string}): {n: number} { return {n: s.n + a.k.length} }", 'r', {init: {n: 0}}), /length/)
})

// --- adversarial: where a naive extraction would be wrong -----------------------------------------------------------
test('aliasing: a write through a second name for a fresh copy is the copy\'s', () => {
  const x = ok(ts(`
    export function r(s: {a: number, b: number}, e: {type: 'go'}): {a: number, b: number} {
      const next = {...s}
      const alias = next
      alias.a = s.a + 1
      return next
    }`, 'r', {init: {a: 0, b: 0}}))
  expect(x.source).toContain('a: a.plus(1)')
})

test('aliasing that depends on the path: a write through one of two objects is seen through every name for it', () => {
  // x is p where flip holds: the write to x is p's there, and q (always x) sees it.
  const x = ok(ts(`
    export function r(s: {a: number, b: number}, e: {flip: boolean}): {a: number, b: number} {
      const x = {...s}, y = {...s}
      const p = e.flip ? x : y
      x.a = 7
      p.b = p.a + 1
      const q = x
      return {a: q.a, b: q.b}
    }`, 'r', {init: {a: 0, b: 0}}))
  expect(x.source).toContain('b: when(flip, lit(7).plus(1), b)')
})

test('mutation through a reference to the state a reducer is given is refused', () => {
  refused(ts(`
    export function r(s: {n: number}, e: {type: 'inc'}): {n: number} { const t = s; t.n++; return t }`, 'r', {init: {n: 0}}), /state it was given/)
  // A shallow copy shares the nested object: writing it writes the caller's state.
  refused(ts(`
    export function r(s: {inner: {x: number}}, e: {type: 'set'}): {inner: {x: number}} { const c = {...s}; c.inner.x = 1; return c }`, 'r', {init: {inner: {x: 0}}}), /state it was given/)
  // So does a Map's own set on the state's map.
  refused(ts(`
    export function r(s: {m: Map<string, number>}, e: {k: string}): {m: Map<string, number>} { s.m.set(e.k, 1); return s }`, 'r', {init: {m: new Map()}}), /state it was given/)
})

test('two names into one map: a write through one is seen through the other at the same key', () => {
  ok(ts(`
    type Cell = {n: number}
    export class Two {
      cells = new Map<number, Cell>()
      put(k: number): void { if (k < 0) throw new Error('key'); this.cells.set(k, {n: 0}) }
      bump(k1: number, k2: number): number {
        if (k1 < 0 || k2 < 0) throw new Error('key')
        const a = this.cells.get(k1), b = this.cells.get(k2)
        if (!a || !b) return 0
        a.n = a.n + 1
        return b.n
      }
    }`, 'Two'))
})

test('a reference into a map held across a set is refused', () => {
  refused(ts(`
    type Cell = {n: number}
    export class Stale {
      cells = new Map<string, Cell>()
      go(k: string): void {
        const b = this.cells.get(k)
        if (!b) return
        this.cells.set(k, {n: 0})
        b.n = 5
      }
    }`, 'Stale'), /read before the map was set/)
})

test('overflow: past 2^53 the code rounds where the rule\'s runtime refuses; the claim stops there and says so', () => {
  const x = ok(ts(`export class Doubler { n = 1; twice(): void { this.n = this.n * 2 } }`, 'Doubler', {check: {runs: 20, depth: 60, states: 100}}))
  expect(x.evidence!.outside).toBeGreaterThan(0)
})

test('floating point and division are refused', () => {
  refused(ts('export class A { b = 100; grow(): void { this.b = this.b * 1.05 } }', 'A'), /safe integer/)
  refused(ts('export class A { b = 100; half(): void { this.b = this.b / 2 } }', 'A'), /division/)
  // Math.floor of x / k for a constant k is in: floor division, also below 0.
  ok(ts('export class A { b = -7; half(): void { this.b = Math.floor(this.b / 2) } down(): void { this.b = this.b - 5 } }', 'A'))
})

test('JavaScript\'s % on a value that may be negative is refused; on a natural it is the remainder', () => {
  refused(ts('export class A { b = 0; dec(): void { this.b = this.b - 1 } wrap(): void { this.b = this.b % 3 } }', 'A'), /remainder takes the sign/)
  ok(ts('export class A { b = 0; inc(): void { this.b = (this.b + 1) % 3 } }', 'A'))
})

test('NaN and Infinity: none of the ways to make them is read', () => {
  refused(ts('export class A { avg = NaN; set(): void { this.avg = 0 } }', 'A'), /NaN/)
  refused(ts('export class A { lo = 0; reset(): void { this.lo = Math.min() } }', 'A'), /of nothing/)
  refused(ts('export class A { t = 0; c = 0; add(x: number): void { this.t += x; this.c++ } mean(): number { return this.t / this.c } }', 'A'), /division/)
})

test('short-circuit effects: the right side runs only where the left does not decide', () => {
  ok(ts(`
    export class Gate {
      open = false
      used = 0
      private take(): boolean { this.used++; return this.used <= 3 }
      enter(): boolean { return this.open && this.take() }
      toggle(): void { this.open = !this.open }
      peek(): boolean { return this.open || this.take() }
    }`, 'Gate'))
})

test('an exception mid-update: a method that throws after writing a field is refused', () => {
  refused(ts(`
    export class Account {
      balance = 10
      debit(x: number): void { this.balance -= x; if (this.balance < 0) throw new Error('overdrawn') }
    }`, 'Account'), /throws after writing balance/)
  // A reducer's throw after building its new state leaves the old one: extracted.
  ok(ts(`
    export function r(s: {n: number}, e: {type: 'inc'}): {n: number} { const next = {...s, n: s.n + 1}; if (next.n > 10) throw new Error('cap'); return next }`, 'r', {init: {n: 0}}))
})

test('a getter with effects runs where it is read', () => {
  const x = ok(ts(`
    export class Meter {
      reads = 0
      used = 0
      get remaining(): number { this.reads++; return 10 - this.used }
      use(): boolean { if (this.remaining > 0) { this.used++; return true } return false }
    }`, 'Meter'))
  expect(x.source).toContain('reads: reads.plus(1)') // read once a call, on every path
})

test('closures and module state over mutable values are refused', () => {
  refused(ts(`
    let calls = 0
    export function r(s: {n: number}, e: {type: 'inc'}): {n: number} { calls = calls + 1; return {n: s.n + calls} }`, 'r', {init: {n: 0}}), /outside the step|module-level let/)
  refused(ts(`
    const shared = {n: 0}
    export function r(s: {n: number}, e: {type: 'inc'}): {n: number} { shared.n++; return {n: s.n + shared.n} }`, 'r', {init: {n: 0}}), /module-level object/)
  refused(ts(`
    export function r(s: {n: number}, e: {type: 'inc'}): {n: number} { const f = () => s.n + 1; return {n: f()} }`, 'r', {init: {n: 0}}), /function value/)
})

test('time: Date.now() is an input read once; twice in one step is refused; Math.random is refused', () => {
  ok(ts('export class T { last = 0; hits = 0; hit(): void { const now = Date.now(); if (now - this.last >= 1000) { this.hits = 0; this.last = now } this.hits++ } }', 'T'))
  refused(ts('export class T { a = 0; b = 0; go(): void { this.a = Date.now(); this.b = Date.now() } }', 'T'), /read twice/)
  refused(ts('export class T { a = 0; go(): void { this.a = Math.floor(Math.random()) } }', 'T'), /random/)
})

test('loose equality of a number with a string, and a string as a condition, are refused', () => {
  refused(ts('export class T { n = 0; go(s: string): void { if (this.n == (s as any)) this.n++ } }', 'T'), /comparison of a num with a str|string/)
  refused(ts('export class T { n = 0; go(s: string): void { if (s) this.n++ } }', 'T'), /string as a condition/)
})

test('truthiness of 0, fall-through, and a postfix increment\'s old value', () => {
  ok(ts(`
    type S = {n: number, old: number, flag: boolean}
    export function r(s: S, e: {type: 'a' | 'b' | 'c'}): S {
      let n = s.n
      switch (e.type) {
        case 'a': n += 1
        case 'b': n += 2; break
        default: n = s.n ? 0 : 5
      }
      const old = n++
      return {n, old, flag: !s.flag}
    }`, 'r', {init: {n: 0, old: 0, flag: false}}))
})

test('a check that finds a difference refuses the extraction with it', () => {
  // The rule's numbers are integers; a method that leaves them (here, by a getter Date.now() can't reach) is refused by
  // the check, never adopted: here, a negative key into a map keyed by naturals is refused before it gets that far.
  refused(ts('export class M { m = new Map<number, number>(); put(k: number): void { this.m.set(k, 1) } }', 'M'), /negative/)
})

// --- XState ---------------------------------------------------------------------------------------------------------
import * as xstate from 'xstate'
import {extractXState} from './extract.ts'
const machineFile = (body: string) => `import {setup, assign, stateIn} from 'xstate'\n${body}`

test('an XState machine: guards and assign actions read from setup(), the chart run beside XState\'s actor', () => {
  const x = extractXState(machineFile(`
    export const order = setup({
      guards: {canRetry: ({context}) => context.retries < 2, unshipped: stateIn({active: 'paid'})},
      actions: {count: assign({retries: ({context}) => context.retries + 1}), notify: () => {}},
    }).createMachine({
      id: 'order', initial: 'new', context: {retries: 0},
      states: {
        new: {on: {PAY: 'active', FAIL: {target: 'new', guard: 'canRetry', actions: ['count', 'notify']}}},
        active: {initial: 'paid', states: {paid: {on: {SHIP: 'shipped'}}, shipped: {}}, on: {REFUND: {target: 'refunded', guard: 'unshipped'}}},
        refunded: {type: 'final'},
      },
    })`), {file: 'order.ts', entry: 'order', xstate, check: {runs: 100, depth: 12}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.source).toContain('"canRetry": ({retries}) => retries.lt(2)')
  expect(x.source).toContain('"unshipped": env => env.in("active.paid")')
  expect(x.evidence!.events).toBe(1200)
  const c = x.chart!
  expect(c.prove([c.law('the retries stay within 2', ({retries}: any) => retries.atMost(2))])).toMatchObject({proven: true, checked: true})
})

test('XState: a payload read by a guard and an action; a context that goes below 0 is an integer', () => {
  const x = extractXState(machineFile(`
    export const tally = setup({
      types: {} as {context: {total: number}, events: {type: 'ADD', amount: number} | {type: 'TAKE'} | {type: 'CLOSE'}},
      guards: {small: ({event}) => event.type === 'ADD' && event.amount <= 3},
      actions: {add: assign({total: ({context, event}) => context.total + (event.type === 'ADD' ? event.amount : 0)}), take: assign({total: ({context}) => context.total - 1})},
    }).createMachine({id: 'tally', initial: 'open', context: {total: 0}, states: {open: {on: {ADD: {target: 'open', guard: 'small', actions: 'add'}, TAKE: {actions: 'take'}, CLOSE: 'closed'}}, closed: {type: 'final'}}})`),
  {file: 'tally.ts', entry: 'tally', xstate, check: {runs: 60, depth: 10}})
  // event.type isn't a payload field: reading it is refused (fromXState gives each event's transitions their own guard).
  expect(x.ok).toBe(false)
  const y = extractXState(machineFile(`
    export const tally = setup({
      types: {} as {context: {total: number}, events: {type: 'ADD', amount: number} | {type: 'TAKE', amount: number} | {type: 'CLOSE', amount: number}},
      guards: {small: ({event}) => event.amount <= 3},
      actions: {add: assign({total: ({context, event}) => context.total + event.amount}), take: assign({total: ({context}) => context.total - 1})},
    }).createMachine({id: 'tally', initial: 'open', context: {total: 0}, states: {open: {on: {ADD: {target: 'open', guard: 'small', actions: 'add'}, TAKE: {actions: 'take'}, CLOSE: 'closed'}}, closed: {type: 'final'}}})`),
  {file: 'tally.ts', entry: 'tally', xstate, check: {runs: 60, depth: 10}})
  if (!y.ok) throw new Error(JSON.stringify(y.refusals))
  expect(y.source).toContain('context: {total: int.from(0)}')
  expect(y.source).toContain('inputs: {amount: int}')
})

test('XState: v4 cond, a machine made by a function, and what fromXState refuses, each refused with the reason', () => {
  const v4 = extractXState(machineFile(`export const m = setup({guards: {ok: () => true}}).createMachine({initial: 'a', states: {a: {on: {GO: {target: 'b', cond: 'ok'}}}, b: {}}})`), {file: 'm.ts', entry: 'm', xstate})
  expect(v4.refusals[0]!.what).toMatch(/v4 `cond`/)
  const fn = extractXState(machineFile(`export function makeM() { return setup({}).createMachine({initial: 'a', states: {a: {}}}) }`), {file: 'm.ts', entry: 'makeM', xstate})
  expect(fn.refusals[0]!.what).toMatch(/made by a function/)
  const after = extractXState(machineFile(`export const m = setup({}).createMachine({initial: 'a', states: {a: {after: {1000: 'b'}}, b: {}}})`), {file: 'm.ts', entry: 'm', xstate})
  expect(after.refusals[0]!.what).toMatch(/fromXState: .*`after`/)
})

test('XState: inline assign actions and an inline guard, given by their place in the config; a machine with no states', () => {
  const x = extractXState(`import {createMachine, assign} from 'xstate'
    export const counter = createMachine({
      id: 'counter', context: {count: 0},
      on: {
        increment: {actions: assign({count: ({context}) => context.count + 1})},
        decrement: {guard: ({context}) => context.count > 0, actions: assign({count: ({context}) => context.count - 1})},
      },
    })`, {file: 'counter.ts', entry: 'counter', xstate, check: {runs: 80, depth: 12}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.source).toContain('counter.config.on.increment.actions, ({count}) => ({count: count.plus(1)})')
  expect(x.source).toContain('[counter.config.on.decrement.guard, ({count}) => count.gt(0)]')
  // The guard keeps the count a natural: the decrement's minus is proven at most the count.
  expect(x.source).not.toContain('int.from')
  const c = x.chart!
  expect(c.prove([c.law('the count never goes below 0', ({count}: any) => count.atLeast(0))])).toMatchObject({proven: true, checked: true})
})

// --- widened: strings, other files, Redux Toolkit -------------------------------------------------------------------
import * as rtk from '@reduxjs/toolkit'

test('a string field: set and compared, nothing else read of it', () => {
  const x = ok(ts(`
    type S = {owner: string, locked: boolean}
    export function r(s: S, a: {type: 'claim', who: string} | {type: 'release', who: string}): S {
      if (a.type === 'claim') { if (s.locked) throw new Error('taken'); return {owner: a.who, locked: true} }
      if (!s.locked || s.owner !== a.who) throw new Error('not yours')
      return {owner: '', locked: false}
    }`, 'r', {init: {owner: '', locked: false}}))
  expect(x.source).toContain("owner: str().from('')")
})

test('constants from another file of the repository: read, and loaded in the check', () => {
  const x = ok(extract(`
    import {ADD, RESET} from './types'
    export default function count(state = 0, action) {
      switch (action.type) { case ADD: return state + 1; case RESET: return 0; default: return state }
    }`, {file: 'count.js', entry: 'default', files: {'./types.js': "export const ADD = 'count/add'\nexport const RESET = 'count/reset'\n"}, check: budget}))
  expect(x.source).toContain("type: oneOf('count/add', 'count/reset', '@@other')")
  expect(x.source).toContain('rule("count")')
  refused(extract(`import {ADD} from './types'\nexport default function c(state = 0, action) { return action.type === ADD ? state + 1 : state }`, {file: 'c.js', entry: 'default', check: budget}), /from another module \('.\/types'\)/)
})

test('a Redux Toolkit slice: case reducers on the draft, a thunk\'s cases, checked against Redux Toolkit itself', () => {
  const code = `
    import {createAsyncThunk, createSlice, type PayloadAction} from '@reduxjs/toolkit'
    type S = {value: number, status: 'idle' | 'loading' | 'failed'}
    const initialState: S = {value: 0, status: 'idle'}
    export const load = createAsyncThunk('counter/load', async (n: number) => n)
    export const counter = createSlice({
      name: 'counter', initialState,
      reducers: {
        increment: state => { state.value += 1 },
        decrement: state => { if (state.value > 0) state.value -= 1 },
        set: (state, action: PayloadAction<number>) => ({...state, value: action.payload}),
      },
      extraReducers: builder => {
        builder.addCase(load.pending, state => { state.status = 'loading' }).addCase(load.fulfilled, (state, action) => { state.status = 'idle'; state.value += action.payload })
      },
    })`
  const x = ok(extract(code, {file: 'counter.ts', entry: 'counter', check: {...budget, modules: {'@reduxjs/toolkit': rtk}}}))
  expect(x.source).toContain("'counter/increment', 'counter/decrement', 'counter/set', 'counter/load/pending', 'counter/load/fulfilled', '@@other'")
  // Writing the draft and returning another value: immer throws, so the extractor refuses it.
  refused(extract(code.replace("set: (state, action: PayloadAction<number>) => ({...state, value: action.payload})", "set: (state, action: PayloadAction<number>) => { state.status = 'idle'; return {...state, value: action.payload} }"),
    {file: 'counter.ts', entry: 'counter', check: {...budget, modules: {'@reduxjs/toolkit': rtk}}}), /immer throws/)
})
