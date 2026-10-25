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
  refused(ts('export function r(s: {xs: {a: number}[]}, a: {type: "push"}) { return s }', 'r', {init: {xs: []}}), /an array of records/)
  refused(ts('export function r(s: {n: number}, a: {k: number}): {n: number} { for (let i = 0; i < a.k; i++) {} return s }', 'r', {init: {n: 0}}), /a loop/)
  refused(ts('export class C { n = 0; async go(): Promise<void> { this.n++ } }', 'C'), /async/)
  refused(ts("import {Mixin} from 'somewhere'\nexport class C extends Mixin(Object) { n = 0; go(): void { this.n++ } }", 'C'), /a class a call makes \(a mixin\), not one the files read declare/)
  // `implements` is a type's only: read.
  ok(ts('interface Counter { go(): void }\nexport class C implements Counter { n = 0; go(): void { this.n++ } }', 'C'))
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

test('loose equality of a number with a string is refused; a string as a condition is whether it is empty', () => {
  refused(ts('export class T { n = 0; go(s: string): void { if (this.n == (s as any)) this.n++ } }', 'T'), /comparison of a num with a str|string/)
  ok(ts('export class T { n = 0; go(s: string): void { if (s) this.n++ } }', 'T'))
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
  // event.type is which event it is: the chart's own event
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.source).toContain('"small": ({event, amount}) => all(event.is(\'ADD\'), amount.atMost(3))')
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
  expect(v4.refusals[0]!.what).toMatch(/v4's `cond` in an XState v5 machine/)
  const after = extractXState(machineFile(`export const m = setup({}).createMachine({initial: 'a', states: {a: {after: {1000: 'b', 2000: 'c'}}, b: {}, c: {}}})`), {file: 'm.ts', entry: 'm', xstate})
  expect(after.refusals[0]!.what).toMatch(/fromXState: .*two timers in one state/)
})

test('XState: guards and actions from another file (amplify\'s): an imported object, its entries by name and spread; only those the config names read', () => {
  const files = {'./impl.ts': `import {assign} from 'xstate'
    const canGo = ({context}: {context: {n: number}}) => context.n < 2
    // (another machine's: it reads what this one's context doesn't have, so it can't be read here)
    const elsewhere = ({context}: {context: any}) => context.other.deep > 1
    function stopped({context}: {context: {n: number}}) { return context.n === 9 }
    export const base = {count: assign({n: ({context}: {context: {n: number}}) => context.n + 1})}
    const GUARDS = {canGo, elsewhere, stopped}
    export default GUARDS`}
  const x = extractXState(machineFile(`
    import guards, {base} from './impl'
    export const m = setup({
      types: {} as {context: {n: number}, events: {type: 'GO'} | {type: 'HALT'}},
      guards,
      actions: {...base, note: () => {}},
    }).createMachine({id: 'm', initial: 'a', context: {n: 0}, states: {a: {on: {GO: {target: 'a', guard: 'canGo', actions: ['count', 'note']}, HALT: {target: 'b', guard: 'stopped'}}}, b: {}}})`),
  {file: 'm.ts', entry: 'm', xstate, files, check: {runs: 60, depth: 10}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.source).toContain('"canGo": ({n}) => n.lt(2)')
  expect(x.notes.join(' ')).toMatch(/1 guards of the object the config never names, not read/)
  const c = x.chart!
  expect(c.prove([c.law('n stays at most 2', ({n}: any) => n.atMost(2))])).toMatchObject({proven: true, checked: true})
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

// --- inheritance: one class extending another, each member resolved statically ---------------------------------------
test('inheritance: an override reached through the base, super calls with side effects, constructors in order', () => {
  // The base's take() calls this.cost(), which the derived class overrides: the object's own cost runs (a naive reading
  // of the base alone would charge 1). The derived pay() calls super.pay() (which writes) and then writes again; the
  // derived constructor's field initializer runs after super(...) and reads what the base's constructor wrote.
  const x = ok(ts(`
    class Meter {
      used = 0
      limit: number
      constructor(limit: number) { if (limit < 1) throw new Error('limit'); this.limit = limit }
      cost(): number { return 1 }
      take(): boolean { const c = this.cost(); if (this.used + c > this.limit) return false; this.used += c; return true }
      pay(n: number): void { this.used = Math.max(0, this.used - n) }
    }
    export class Double extends Meter {
      paid = 0
      spare = this.limit * 2
      constructor(limit: number) { super(limit + 1) }
      override cost(): number { return 2 }
      override pay(n: number): void { super.pay(n); this.paid += n }
    }`, 'Double'))
  // super(limit + 1): the base's constructor refuses below 1, so the derived one below 0 (its precondition)
  expect(x.source).toContain('.pre(({limit}) => limit.plus(1).atLeast(1))')
  // the override: two a take
  expect(x.source).toContain('used.plus(2)')
  // super.pay() then the derived write
  expect(x.source).toContain('Int.of(used).minus(pay_n).clamped')
  expect(x.source).toContain('paid.plus(pay_n)')
  expect(x.notes.join(' ')).toContain('Double extends Meter')
})

test('a class that extends a generic one with its type arguments (upstash\'s Ratelimit<RegionContext>): the fields at the types given', () => {
  const x = ok(ts(`
    abstract class Base<T> {
      protected readonly limit: T
      protected used = 0
      constructor(limit: T) { this.limit = limit }
      protected over(n: number, at: T): boolean { return this.used + n > (at as unknown as number) }
    }
    export class Meter extends Base<number> {
      constructor(cap: number) { if (cap < 0 || cap > 1000) throw new Error('cap'); super(cap) }
      take(n: number): boolean { if (n < 0 || n > 1000 || this.over(n, this.limit)) return false; this.used += n; return true }
    }`, 'Meter'))
  expect(x.source).toContain('.params({cap: nat})')
  // the type parameter left open (the class read alone): refused where it is
  refused(ts('export abstract class Base<T> { protected readonly limit: T; constructor(l: T) { this.limit = l } go(): void {} }', 'Base'), /T is not in the subset/)
})

test('a field holding a function (an injected clock): each call an input, one a step, the same in every method', () => {
  const x = ok(ts(`
    export class Window {
      private hits = 0
      private start = 0
      constructor(private readonly limit: number, private readonly clock: () => number) {}
      private roll(now: number): void { if (now - this.start >= 1000) { this.start = now; this.hits = 0 } }
      hit(): boolean {
        const now = this.clock()
        this.roll(now)
        if (this.hits >= this.limit) return false
        this.hits++
        return true
      }
      reset(): void { this.roll(this.clock()); this.hits = 0 }
    }`, 'Window'))
  expect(x.notes.join(' ')).toMatch(/this.clock\(\): the answer of the function the field holds/)
  expect(x.source!.match(/clock: int/g)?.length).toBe(1)
  const r = x.rule! as any
  expect(proveRule(r, [r.law('within the limit', ({hits, limit}: any) => limit.atLeast(hits).or(hits.eq(0)))]).proven).toBe(true)
  // a default written there, replaced by the one given
  ok(ts('export class Ids { last = 0; private gen: () => number = () => 7\n constructor(g: () => number) { this.gen = g }\n next(): void { this.last = this.gen() } }', 'Ids'))
  // whether an optional one was given: the check always gives one, so the claim would be narrower than the code
  refused(ts('export class Ids { last = 0; private gen: () => number = () => 7\n constructor(g?: () => number) { if (g) { this.gen = g } }\n next(): void { this.last = this.gen() } }', 'Ids'), /whether a function was given to the constructor/)
})

test('a field holding a function: called twice in a step, set by a method, called while made, or read as a value, refused', () => {
  const C = (body: string) => ts(`export class C { n = 0; constructor(private f: () => number) {} ${body} }`, 'C')
  refused(C('go(): void { this.n = this.f() + this.f() }'), /called twice in one step/)
  refused(C('go(): void { this.f = () => 1 }'), /set by a method/)
  refused(ts('export class C { n = 0; f: () => number = () => 1\n constructor() { this.n = this.f() }\n go(): void { this.n++ } }', 'C'), /called while the object is made/)
  refused(C('go(): void { const g = this.f; this.n = g() }'), /this.f: no field f the step can read/)
  refused(ts('export class C { n = 0; f: () => number = makeF()\n go(): void { this.n = this.f() } }\nfunction makeF(): () => number { return () => 1 }', 'C'), /starts as makeF\(\)/)
  refused(C('go(): void { this.n = this.f() }').ok ? ts('export class C { n = 0; constructor(private f: () => {a: number}) {} go(): void { this.n = this.f().a } }', 'C') : C(''), /returns a compound value/)
})

test('a mixin of the files read: its class between the entry and the class it is given, members resolved in that order', () => {
  const x = ok(ts(`
    type Ctor<T = {}> = new (...args: any[]) => T
    class Counter { count = 0; constructor(readonly cap: number) {} bump(): void { if (this.count < this.cap) this.count++ } }
    function Resettable<B extends Ctor>(Base: B) {
      return class extends Base {
        resets = 0
        constructor(...args: any[]) { super(...args) }
        reset(): void { this.resets++ }
      }
    }
    const Named = <B extends Ctor>(Base: B) => class extends Base { on = false; flip(): void { this.on = !this.on } }
    export class Meter extends Named(Resettable(Counter)) {
      reset(): void { super.reset(); this.count = 0 }
    }`, 'Meter'))
  expect(x.notes.join(' ')).toMatch(/Meter extends/)
  const r = x.rule! as any
  expect(proveRule(r, [r.law('within the cap', ({count, cap}: any) => cap.atLeast(count).or(count.eq(0)))]).proven).toBe(true)
  // one mixin twice in the chain; a mixin that does more than make a class; one that extends other than its parameter
  refused(ts('class B { n = 0 }\nconst M = <T extends new (...a: any[]) => {}>(X: T) => class extends X { m = 0 }\nexport class C extends M(M(B)) { go(): void { this.n++ } }', 'C'), /a mixin applied twice/)
  refused(ts('class B { n = 0 }\nlet made = 0\nfunction M<T extends new (...a: any[]) => {}>(X: T) { made++; return class extends X { m = 0 } }\nexport class C extends M(B) { go(): void { this.n++ } }', 'C'), /more than a class/)
  refused(ts('class B { n = 0 }\nclass D { n = 0 }\nconst M = <T extends new (...a: any[]) => {}>(X: T) => class extends D { m = 0 }\nexport class C extends M(B) { go(): void { this.n++ } }', 'C'), /extends other than its parameter/)
})

test('inheritance: a mixin, a class from another module, a field declared again and a missing super(...) are refused', () => {
  // a mixin of the files read over a class from another module: refused at that class
  refused(ts('const Mixin = (b: any) => class extends b {}\nexport class C extends Mixin(Object) { n = 0; go(): void { this.n++ } }', 'C'), /extends Object, a class from another module|no class of the files read/)
  refused(ts("import {EventEmitter} from 'node:events'\nexport class C extends EventEmitter { n = 0; go(): void { this.n++ } }", 'C'), /another module|no class of the files read/)
  refused(ts('class B { n = 0 }\nexport class C extends B { n = 1; go(): void { this.n++ } }', 'C'), /declared again/)
  refused(ts('class B { constructor(public n: number) {} }\nexport class C extends B { constructor(k: number) { if (k > 0) super(k); else super(0) } go(): void { this.n++ } }', 'C'), /no super\(\.\.\.\) at its top level/)
  // a static method named as the entry's event: a function of the class, not a step of an object
  refused(ts('export class C { n = 0; static make(): C { return new C() } go(): void { this.n++ } }', 'C', {methods: ['make']}), /make is static/)
})

// --- a Map given to the constructor, and results kept ----------------------------------------------------------------
test('a Map given to the constructor starts empty, as the callers make it; results: a record, a value or null', () => {
  const x = ok(ts(`
    export class Cache {
      private readonly cache: Map<string, number>
      constructor(cache: Map<string, number>) { this.cache = cache }
      isBlocked(id: string): {blocked: boolean, reset: number} {
        if (!this.cache.has(id)) return {blocked: false, reset: 0}
        const reset = this.cache.get(id)!
        if (reset < Date.now()) { this.cache.delete(id); return {blocked: false, reset: 0} }
        return {blocked: true, reset}
      }
      blockUntil(id: string, reset: number): void { this.cache.set(id, reset) }
      get(key: string): number | null { return this.cache.get(key) || null }
    }`, 'Cache'))
  expect(x.source).toContain('isBlocked_result_blocked: bool.from(false)')
  expect(x.source).toContain('get_result_missing: bool.from(false)')
  expect(x.notes.join(' ')).toContain('it starts empty here')
  // one Map given to two fields: one object in two places (a write through one is the other's)
  refused(ts('export class C { a: Map<string, number>; b: Map<string, number>; constructor(m: Map<string, number>) { this.a = m; this.b = m } put(k: string): void { this.a.set(k, 1) } }', 'C'), /given to two fields/)
  // a record returned that is the object's own: the caller would share it
  refused(ts('type P = {x: number}\nexport class C { p: P = {x: 0}; bump(): P { this.p.x++; return this.p } }', 'C'), /an object of the state's own/)
})

// --- Dates: a Date is its time, read by getTime() and set by setTime(), made by new Date() ---------------------------
test('Dates as naturals: new Date(), getTime(), setTime() where the Date is held; a second name for one is refused', () => {
  const x = ok(ts(`
    type Client = {hits: number, reset: Date}
    export class Window {
      windowMs = 1000
      clients = new Map<string, Client>()
      hit(key: string): number {
        const now = new Date()
        const c = this.clients.get(key)
        if (!c) { this.clients.set(key, {hits: 1, reset: new Date(now.getTime() + this.windowMs)}); return 1 }
        if (c.reset.getTime() <= now.getTime()) { c.hits = 0; c.reset.setTime(now.getTime() + this.windowMs) }
        c.hits++
        return c.hits
      }
    }`, 'Window'))
  expect(x.source).toContain('reset: nat')
  // a Date held under a second name: a setTime through one moves the other
  refused(ts('export class W { a = new Date(0); b = new Date(0); go(): void { this.b = this.a } }', 'W'), /a Date held elsewhere/)
  refused(ts('export class W { a = new Date(0); go(): void { const d = this.a; d.setTime(5) } }', 'W'), /a second name for a Date/)
  refused(ts('type C = {d: Date}\nexport class W { m = new Map<string, C>(); go(k: string): void { const c = this.m.get(k); if (c) this.m.set(k + "x", {...c}) } }', 'W'), /a spread of an object holding a Date|string concatenation/)
  refused(ts('export class W { a = new Date(0); b = new Date(0); same(): boolean { return this.a === this.b } }', 'W'), /whether they are one object/)
  // the clock read twice in a step (the two reads may differ)
  refused(ts('export class W { a = 0; go(): void { const t = new Date(); this.a = Date.now() - t.getTime() } }', 'W'), /read twice/)
})

// --- an object a factory makes: its state is what its functions close over -------------------------------------------
test('a factory\'s object: the variables its functions close over are its state, a helper writing them inlined', () => {
  const x = ok(ts(`
    export function counter(limit: number) {
      if (limit < 1) throw new Error('limit')
      let n = 0
      const seen = new Map<string, number>()
      function bump(by: number): void { n += by }
      return {
        inc(by: number): boolean { if (by < 1) throw new Error('by'); if (n + by > limit) return false; bump(by); return true },
        get: (): number => n,
        mark(k: string): void { seen.set(k, n) },
      }
    }`, 'counter'))
  expect(x.source).toContain('.params({limit: nat})')
  expect(x.source).toContain('.pre(({limit}) => limit.atLeast(1))')
  expect(x.source).toContain('.maps({seen:')
  expect(x.notes.join(' ')).toContain('its state is what they close over (limit, n, seen)')
  // a law over the extracted rule: the count never passes the limit
  const r = x.rule!, v = proveRule(r, [...(x.invariants ?? []), r.law('n stays within the limit', ({n, limit}: any) => n.atMost(limit))])
  expect(v).toMatchObject({proven: true, checked: true})
})

test('a factory\'s object: state outside the factory, this, a value beside the functions and async are refused', () => {
  // closed over a module-level let: every object would share it (and the check's fresh objects would part from the rule)
  refused(ts('let total = 0\nexport function make() { let n = 0; return {inc(): void { n++; total++ }} }', 'make'), /a module-level let/)
  refused(ts('export function make() { let n = 0; return {inc(): void { n++ }, peek(): number { return this.inc.length } } }', 'make'), /this in an object a factory makes/)
  refused(ts('export function make() { let n = 0; return {inc(): void { n++ }, size: 3} }', 'make'), /a value the object returns beside its functions/)
  refused(ts('export function make() { let n = 0; return {async inc(): Promise<void> { n++ }} }', 'make'), /async/)
  refused(ts('export function make() { let n = 0; for (let i = 0; i < 2; i++) n++; return {inc(): void { n++ }} }', 'make'), /a factory read here declares its state/)
  refused(ts('export function make() { const n = 0; return {inc(): void { // @ts-ignore\n n++ }} }', 'make'), /is a const/)
})

// --- arrays, as lists --------------------------------------------------------------------------------------------------
test('arrays as lists: push, pop, length, an item read and set within the array; a reducer\'s [...xs, x]', () => {
  const x = ok(ts(`
    export class Recent {
      limit = 3
      xs: number[] = []
      add(v: number): number { if (v < 0) throw new Error('v'); if (this.xs.length >= this.limit) return this.xs.length; return this.xs.push(v) }
      last(): number { const y = this.xs.pop(); return y ?? 0 }
      bump(i: number): void { if (i >= 0 && i < this.xs.length) { const a = this.xs; a[i] = this.xs[i]! + 1 } }
      first(): number { return this.xs[0] ?? 0 }
    }`, 'Recent'))
  expect(x.source).toContain('.items({xs: nat})')
  expect(x.source).toMatch(/\.\.\.xs\.apply\(xs\.push\(/)
  const r = x.rule!, v = proveRule(r, [...(x.invariants ?? []), r.law('at most three items', ({xs}: any) => xs.len.atMost(3))])
  expect(v).toMatchObject({proven: true, checked: true})
  const y = ok(ts(`
    type S = {xs: number[], n: number}
    export function r(s: S, a: {type: 'add', v: number} | {type: 'count'}): S {
      switch (a.type) {
        case 'add': return a.v < 0 ? s : {...s, xs: [...s.xs, a.v]}
        case 'count': return {...s, n: s.xs.length}
      }
    }`, 'r', {init: {xs: [], n: 0}}))
  // the item pushed is an integer input (the code doesn't refuse it below 0: it leaves the state as it is)
  expect(y.source).toContain('.items({xs: int})')
  expect(y.source).toContain("...xs.apply(xs.push(v, all(type.is('add'), v.atLeast(0))))")
})

test('arrays: one array in two places, a write to the state given, past the end, two writes, a read after a write are refused', () => {
  // two fields holding one array: a push through one is the other's (the rule's lists are two)
  refused(ts('export class C { xs: number[] = []; ys: number[] = []; tie(): void { this.ys = this.xs } add(): void { this.xs.push(1) } }', 'C'), /another array \(one array in two places/)
  // React and Redux keep the old state
  refused(ts('type S = {xs: number[]}\nexport function r(s: S, a: {type: "add"}): S { s.xs.push(1); return {xs: s.xs} }', 'r', {init: {xs: []}}), /in the state it was given/)
  // an index the code doesn't keep within the array: past the end the array grows with holes
  refused(ts('export class C { xs: number[] = []; put(i: number): void { this.xs[i] = 1 } }', 'C'), /an index the code doesn't keep within the array/)
  refused(ts('export class C { xs: number[] = []; two(): void { this.xs.push(1); this.xs.push(2) } }', 'C'), /a second write to xs in one step|read after it is written/)
  refused(ts('export class C { xs: number[] = []; n = 0; go(): void { this.xs.push(1); this.n = this.xs.length } }', 'C'), /read after it is written in one step/)
  refused(ts('export class C { xs: number[] = [1, 2]; go(): void { this.xs.push(1) } }', 'C'), /starts with items/)
  refused(ts('export class C { xs: number[] = []; has(v: number): boolean { return this.xs.includes(v) } }', 'C'), /the array method includes/)
  refused(ts('export class C { xs: string[] = []; go(): void {} }', 'C'), /an array of strings/)
})

// --- XState: machines made by a function, actors, timers, eventless transitions, maybes, v4 ---------------------------
import * as xstate4 from 'xstate4'
test('XState: a machine a factory makes, its answers from outside an input; an actor, a timer and always run as XState', () => {
  const x = extractXState(`import {setup, assign, fromPromise} from 'xstate'
    export interface Deps { upload: () => Promise<void>, latched: () => boolean, log: (n: number) => void }
    export function makeUploader(deps: Deps) {
      return setup({
        types: {} as {context: {tries: number, note: string | null}, events: {type: 'START'} | {type: 'RETRY'} | {type: 'STOP'}},
        actors: {upload: fromPromise(() => deps.upload())},
        guards: {latched: () => deps.latched(), canRetry: ({context}) => context.tries < 2, noted: ({context}) => Boolean(context.note)},
        actions: {count: assign({tries: ({context}) => context.tries + 1}), say: () => deps.log(1), note: assign({note: ({event}) => (event.type === 'STOP' ? 'stopped' : null)})},
      }).createMachine({
        id: 'up', initial: 'idle', context: {tries: 0, note: null},
        states: {
          idle: {on: {START: [{guard: 'latched', target: 'done'}, {target: 'busy'}], STOP: {actions: 'note'}}, always: {guard: 'noted', target: 'done'}},
          busy: {entry: 'say', invoke: {src: 'upload', onDone: 'done', onError: [{guard: 'canRetry', target: 'wait', actions: 'count'}, {target: 'failed'}]}},
          wait: {after: {1000: 'busy'}, on: {STOP: {target: 'idle', actions: 'note'}}},
          done: {type: 'final'}, failed: {type: 'final'},
        },
      })
    }`, {file: 'up.ts', entry: 'makeUploader', xstate, check: {runs: 120, depth: 12}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.source).toContain('inputs: {latched: bool}')
  expect(x.source).toContain('note: maybe(str()).from(null)')
  expect(x.source).toContain('"latched": ({latched}) => latched')
  expect(x.evidence!.events).toBeGreaterThan(1000)
  const c = x.chart!
  expect(c.prove([c.law('at most two retries', ({tries}: any) => tries.atMost(2))])).toMatchObject({proven: true, checked: true})
})

test('XState: a factory argument with untyped functions (of type any), called only by an actor: outside the machine', () => {
  const src = (guard: string) => `import {setup, fromPromise} from 'xstate'
    export function make(services: {submit: any, check: () => boolean}) {
      return setup({
        types: {} as {context: {tries: number}, events: {type: 'GO'} | {type: 'RESET'}},
        actors: {send: fromPromise(() => services.submit())},
        guards: {ok: ${guard}},
      }).createMachine({
        initial: 'idle', context: {tries: 0},
        states: {idle: {on: {GO: {target: 'busy', guard: 'ok'}}}, busy: {invoke: {src: 'send', onDone: 'done', onError: 'idle'}}, done: {on: {RESET: 'idle'}}},
      })
    }`
  const x = extractXState(src('() => services.check()'), {file: 'm.ts', entry: 'make', xstate, check: {runs: 60, depth: 10}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.notes.join(' ')).toMatch(/submit of type any, called only where an actor runs/)
  expect(x.evidence!.events).toBeGreaterThan(300)
  // a guard that calls the untyped one: its answer has no type the subset reads
  const bad = extractXState(src('() => services.submit()'), {file: 'm.ts', entry: 'make', xstate})
  expect(bad.ok).toBe(false)
  expect(bad.refusals[0]!.what).toMatch(/no type the subset reads/)
})

test('XState: what a factory or a machine could not run the same way is refused, with the reason', () => {
  const m = (body: string) => `import {setup, assign} from 'xstate'\n${body}`
  // a factory's own mutable state, closed over by a guard: every machine made shares it (and the check's would part)
  const closure = extractXState(m(`export function make() { let n = 0; return setup({guards: {ok: () => n++ < 3}}).createMachine({initial: 'a', states: {a: {on: {GO: {target: 'b', guard: 'ok'}}}, b: {}}}) }`), {file: 'm.ts', entry: 'make', xstate})
  expect(closure.refusals[0]!.what).toMatch(/does more than return the machine/)
  // an outside answer read in two places: each call may answer differently
  const twice = extractXState(m(`export function make(d: {ok: () => boolean}) { return setup({guards: {a: () => d.ok(), b: () => d.ok()}}).createMachine({initial: 'a', states: {a: {on: {GO: [{target: 'b', guard: 'a'}, {target: 'c', guard: 'b'}]}}, b: {}, c: {}}}) }`), {file: 'm.ts', entry: 'make', xstate})
  expect(twice.refusals[0]!.what).toMatch(/read in two places/)
  // a context field outside the subset, read by a guard: refused where it is read (left out only where nothing reads it)
  const obj = extractXState(m(`export const mm = setup({types: {} as {context: {err: Error | null}}, guards: {bad: ({context}) => !context.err}}).createMachine({initial: 'a', context: {err: null}, states: {a: {on: {GO: {target: 'b', guard: 'bad'}}}, b: {}}})`), {file: 'm.ts', entry: 'mm', xstate})
  expect(obj.refusals[0]!.what).toMatch(/read as a condition/)
  // two timers in a state fire in the order of their delays: refused; a guard writing the context from outside: an effect
  const timers = extractXState(m(`export const mm = setup({}).createMachine({initial: 'a', states: {a: {after: {100: 'b', 200: 'c'}}, b: {}, c: {}}})`), {file: 'm.ts', entry: 'mm', xstate})
  expect(timers.refusals[0]!.what).toMatch(/two timers in one state/)
  // raise sends to the machine itself: refused
  const raise = extractXState(`import {setup, raise} from 'xstate'\nexport const mm = setup({actions: {again: raise({type: 'GO'})}}).createMachine({initial: 'a', states: {a: {on: {GO: {target: 'b', actions: 'again'}}}, b: {}}})`, {file: 'm.ts', entry: 'mm', xstate})
  expect(raise.refusals[0]!.what).toMatch(/sends to the machine itself/)
})

test('XState v4: cond, (context, event) guards and actions, services, after; a field written from an unread payload left out', () => {
  const x = extractXState(`import {createMachine, assign} from 'xstate'
    type Ctx = {retries: number, limit: number, token?: string}
    export const conn = createMachine<Ctx, {type: 'OPEN'} | {type: 'DROP'} | {type: 'CLOSE'}>({
      id: 'conn', initial: 'idle', predictableActionArguments: true, context: {retries: 0, limit: 3, token: undefined},
      states: {
        idle: {on: {OPEN: 'auth'}},
        auth: {invoke: {id: 'auth', src: 'auth', onDone: {target: 'up', actions: 'keep'}, onError: 'down'}},
        up: {on: {DROP: [{target: 'wait', cond: 'under'}, {target: 'down'}]}},
        wait: {after: {500: {target: 'auth', actions: 'count'}}},
        down: {type: 'final'},
      },
    }, {
      services: {auth: async () => ({token: 't'})},
      actions: {keep: assign({token: (_c, e: any) => e.data.token}), count: assign({retries: (c) => c.retries + 1})},
      guards: {under: (c) => c.retries < c.limit},
    })`, {file: 'conn.ts', entry: 'conn', xstate: xstate4 as never, check: {runs: 120, depth: 12}})
  if (!x.ok) throw new Error(JSON.stringify(x.refusals))
  expect(x.source).toContain('ignore: ["token"]')
  expect(x.source).toContain('"under": ({retries, limit}) => retries.lt(limit)')
  // CLOSE: declared by the machine's type, taken by no state (a step that changes nothing)
  expect(x.source).toContain('"CLOSE"')
  const c = x.chart!
  expect(c.prove([c.law('the retries stay within the limit', ({retries, limit}: any) => retries.atMost(limit))])).toMatchObject({proven: true, checked: true})
})
