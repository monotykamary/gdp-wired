// The laws of each example the extractor reads (sources.json), proven of the extracted rule and of a rule written by
// hand as research/realworld writes them (mirroring the code's params, inputs, state and step): the same verdict on
// each side for every law, true laws and false ones, invariants and step laws.
//
//   bun research/extract/verdicts.ts --out runs/extract/<name>
//
// A verdict is `proven` (proven and checked), `refuted` (a counterexample) or `unknown`; agreement is the same verdict.
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import * as xstate from 'xstate'
import {extract, extractXState} from '../../core/extract.ts'
import {fetchSource, importsOf} from './fetch.ts'
import {type Verdict, bool, forall, int, nat, oneOf, proveRule, proveSteps, record, rule, str, when} from '../../core/dsl.ts'
import * as rtk from '@reduxjs/toolkit'
import {chart} from '../../core/chart.ts'
import type {Law} from '../../core/machine.ts'
import type {StepLaw} from '../../kernel/kernel.ts'

const here = import.meta.dir, args = process.argv.slice(2), outAt = args.indexOf('--out')
const out = outAt >= 0 ? args[outAt + 1]! : join(here, '../../runs/extract/verdicts-local')
mkdirSync(out, {recursive: true})
type Src = {id: string, repo: string, commit: string, path: string, lines?: string, file?: string, entry: string, shape?: string, init?: unknown, domains?: Record<string, 'nat' | 'int'>}
const sources = JSON.parse(readFileSync(join(here, 'sources.json'), 'utf8')) as Src[]
const code = async (s: Src) => {
  const text = await fetchSource(s)
  if (!s.lines) return text
  const [a, b] = s.lines.split('-').map(Number) as [number, number]
  return text.split('\n').slice(a - 1, b).join('\n')
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
// Each law alone, so each gets its own verdict.
const verdictOf = (v: Verdict): 'proven' | 'refuted' | 'unknown' => (v.proven && v.checked ? 'proven' : v.witness || v.run ? 'refuted' : 'unknown')
const ruleProve = (r: Any, laws: Law[], steps: StepLaw[]) => (steps.length ? proveSteps(r, laws, steps) : proveRule(r, laws))
const chartProve = (c: Any, laws: Law[], steps: StepLaw[]) => c.prove(laws, steps)

type Case = {id: string, hand: () => Any, laws: [string, 'true' | 'false', (r: Any) => Law | StepLaw][], kind: 'rule' | 'chart'}
const cases: Case[] = [
  {id: 'react.dev/useReducer/counter', kind: 'rule',
    // useReducer.md:130-137: incremented_age adds one; any other action throws.
    hand: () => rule('react.dev counter').inputs({type: oneOf('incremented_age')}).state({age: 42}).step(({age}) => ({age: age.plus(1)})),
    laws: [
      ['the age never goes below 42', 'true', r => r.law('the age never goes below 42', ({age}: Any) => age.atLeast(42))],
      ['the age stays at most 100', 'false', r => r.law('the age stays at most 100', ({age}: Any) => age.atMost(100))],
      ['each action adds one', 'true', r => r.stepLaw('each action adds one', ({age}: Any, after: Any) => after.age.eq(age.plus(1)))],
    ]},
  {id: 'react.dev/useReducer/form', kind: 'rule',
    // useReducer.md:263-279: incremented_age adds one to the age, changed_name sets the name; any other throws.
    hand: () => rule('react.dev form').inputs({type: oneOf('incremented_age', 'changed_name'), nextName: str()}).state({name: str().from('Taylor'), age: 42})
      .step(({type, name, nextName, age}) => ({name: when(type.is('changed_name'), nextName, name), age: when(type.is('incremented_age'), age.plus(1), age)})),
    laws: [
      ['the age never goes below 42', 'true', r => r.law('the age never goes below 42', ({age}: Any) => age.atLeast(42))],
      ['the name stays Taylor', 'false', r => r.law('the name stays Taylor', ({name}: Any) => name.eq('Taylor'))],
      ['incremented_age keeps the name', 'true', r => r.stepLaw('incremented_age keeps the name', ({name}: Any, a: Any) => a.name.eq(name), ({type}: Any) => type.is('incremented_age'))],
    ]},
  {id: 'redux/shopping-cart/cart', kind: 'rule',
    // cart.js:24-31: ADD_TO_CART counts one more of the product; any other action keeps the quantities.
    hand: () => rule('cart quantities').inputs({type: oneOf('ADD_TO_CART', 'OTHER'), productId: nat}).maps({state: record({has: bool, value: nat}).from({has: false, value: 0})})
      .step(({type, productId, state}) => ({state: state.set(productId, {has: state.at(productId).has.or(type.is('ADD_TO_CART')), value: when(type.is('ADD_TO_CART'), state.at(productId).value.plus(1), state.at(productId).value)})})),
    laws: [
      ['a quantity never goes down', 'true', r => r.stepLaw('a quantity never goes down', ({state}: Any, a: Any) => forall(k => state.at(k).value.atMost(a.state.at(k).value)))],
      ['an add counts one more of its product', 'true', r => r.stepLaw('an add counts one more of its product', ({state, productId}: Any, a: Any) => a.state.at(productId).value.eq(state.at(productId).value.plus(1)), ({type}: Any) => type.is('ADD_TO_CART'))],
      ['no product is added twice', 'false', r => r.law('no product is added twice', ({state}: Any) => forall(k => state.at(k).value.atMost(1)))],
    ]},
  {id: 'redux/todos/visibilityFilter', kind: 'rule',
    // visibilityFilter.js:3-10: SET_VISIBILITY_FILTER sets the filter; any other action keeps it.
    hand: () => rule('visibility filter').inputs({type: oneOf('SET_VISIBILITY_FILTER', 'OTHER'), filter: str()}).state({state: str().from('SHOW_ALL')})
      .step(({type, filter, state}) => ({state: when(type.is('SET_VISIBILITY_FILTER'), filter, state)})),
    laws: [
      ['another action keeps the filter', 'true', r => r.stepLaw('another action keeps the filter', ({state}: Any, a: Any) => a.state.eq(state), ({type}: Any) => type.is('SET_VISIBILITY_FILTER').not())],
      ['the filter is always SHOW_ALL', 'false', r => r.law('the filter is always SHOW_ALL', ({state}: Any) => state.eq('SHOW_ALL'))],
    ]},
  {id: 'redux/counter/counterSlice', kind: 'rule',
    // counterSlice.ts:29-62: increment, decrement, incrementByAmount; the fetch's pending, fulfilled and rejected.
    hand: () => rule('counter slice').inputs({type: oneOf('counter/increment', 'counter/decrement', 'counter/incrementByAmount', 'counter/fetchCount/pending', 'counter/fetchCount/fulfilled', 'counter/fetchCount/rejected', 'OTHER'), payload: int})
      .state({value: int.from(0), status: oneOf('idle', 'loading', 'failed').from('idle')})
      .step(({type, payload, value, status}) => ({
        value: when(type.is('counter/increment'), value.plus(1), when(type.is('counter/decrement'), value.minus(1), when(type.is('counter/incrementByAmount').or(type.is('counter/fetchCount/fulfilled')), value.plus(payload), value))),
        status: when(type.is('counter/fetchCount/pending'), status.of('loading'), when(type.is('counter/fetchCount/fulfilled'), status.of('idle'), when(type.is('counter/fetchCount/rejected'), status.of('failed'), status))),
      })),
    laws: [
      ['the value never goes below 0', 'false', r => r.law('the value never goes below 0', ({value}: Any) => value.atLeast(0))],
      ['a pending fetch is loading', 'true', r => r.stepLaw('a pending fetch is loading', (_: Any, a: Any) => a.status.is('loading'), ({type}: Any) => type.is('counter/fetchCount/pending'))],
      ['the status is never failed', 'false', r => r.law('the status is never failed', ({status}: Any) => status.is('failed').not())],
      ['an increment adds one', 'true', r => r.stepLaw('an increment adds one', ({value}: Any, a: Any) => a.value.eq(value.plus(1)), ({type}: Any) => type.is('counter/increment'))],
    ]},
  {id: 'xstate/examples/toggle', kind: 'chart',
    hand: () => chart('toggle').states({inactive: {}, active: {}}).on('toggle', {from: 'inactive', to: 'active'}).on('toggle', {from: 'active', to: 'inactive'}),
    laws: [
      ['a toggle from inactive goes to active', 'true', c => c.stepLaw('a toggle from inactive goes to active', (_: Any, a: Any) => a.in('active'), (b: Any) => b.in('inactive').and(b.event.is('toggle')))],
      ['it is never active', 'false', c => c.law('it is never active', (env: Any) => env.in('active').not())],
    ]},
  {id: 'xstate/examples/counter', kind: 'chart',
    hand: () => chart('counter').context({count: {kind: int, init: 0}}).states({counting: {}})
      .on('increment', {from: 'counting', set: ({count}: Any) => ({count: count.plus(1)})}).on('decrement', {from: 'counting', set: ({count}: Any) => ({count: count.minus(1)})}),
    laws: [
      ['the count never goes below 0', 'false', c => c.law('the count never goes below 0', ({count}: Any) => count.atLeast(0))],
      ['an increment adds one', 'true', c => c.stepLaw('an increment adds one', ({count}: Any, a: Any) => a.count.eq(count.plus(1)), (b: Any) => b.event.is('increment'))],
      ['a decrement takes one', 'true', c => c.stepLaw('a decrement takes one', ({count}: Any, a: Any) => a.count.eq(count.minus(1)), (b: Any) => b.event.is('decrement'))],
    ]},
  {id: 'xstate/examples/7guis-counter-react', kind: 'chart',
    hand: () => chart('counter').context({count: 0}).states({counting: {}}).on('INCREMENT', {from: 'counting', set: ({count}: Any) => ({count: count.plus(1)})}),
    laws: [
      ['the count never goes below 0', 'true', c => c.law('the count never goes below 0', ({count}: Any) => count.atLeast(0))],
      ['the count stays at most 5', 'false', c => c.law('the count stays at most 5', ({count}: Any) => count.atMost(5))],
    ]},
  {id: 'xstate/examples/7guis-counter-vue', kind: 'chart',
    hand: () => chart('Counter').context({count: 0}).states({ready: {}}).on('increase', {from: 'ready', to: 'ready', set: ({count}: Any) => ({count: count.plus(1)})}),
    laws: [
      ['the count never goes below 0', 'true', c => c.law('the count never goes below 0', ({count}: Any) => count.atLeast(0))],
      ['an increase adds one', 'true', c => c.stepLaw('an increase adds one', ({count}: Any, a: Any) => a.count.eq(count.plus(1)), (b: Any) => b.event.is('increase'))],
    ]},
  {id: 'xstate/examples/express-workflow', kind: 'chart',
    hand: () => chart('counter').context({cycles: 0}).states({green: {}, yellow: {}, red: {}})
      .on('TIMER', {from: 'green', to: 'yellow'}).on('TIMER', {from: 'yellow', to: 'red'}).on('TIMER', {from: 'red', to: 'green', set: ({cycles}: Any) => ({cycles: cycles.plus(1)})}),
    laws: [
      ['a timer at red turns green and counts a cycle', 'true', c => c.stepLaw('a timer at red turns green and counts a cycle', ({cycles}: Any, a: Any) => a.in('green').and(a.cycles.eq(cycles.plus(1))), (b: Any) => b.in('red').and(b.event.is('TIMER')))],
      ['a cycle is counted only on the way to green', 'true', c => c.stepLaw('a cycle is counted only on the way to green', ({cycles}: Any, a: Any) => a.cycles.eq(cycles).or(a.in('green')))],
      ['the cycles stay below 3', 'false', c => c.law('the cycles stay below 3', ({cycles}: Any) => cycles.lt(3))],
    ]},
  {id: 'xstate/examples/stopwatch', kind: 'chart',
    // stopwatchMachine.ts: start/stop between stopped and running; the invoked ticker's TICK (an event from outside, as
    // the actor sends it while running) counts one; the root's reset zeroes it and stops.
    hand: () => chart('stopwatch').context({elapsed: 0}).states({stopped: {}, running: {}})
      .on('start', {from: 'stopped', to: 'running'}).on('TICK', {from: 'running', set: ({elapsed}: Any) => ({elapsed: elapsed.plus(1)})}).on('stop', {from: 'running', to: 'stopped'})
      .on('reset', {from: ['stopped', 'running'], to: 'stopped', set: () => ({elapsed: 0})}),
    laws: [
      ['the time never goes back but on a reset', 'true', c => c.stepLaw('the time never goes back but on a reset', ({elapsed}: Any, a: Any) => elapsed.atMost(a.elapsed), (b: Any) => b.event.is('reset').not())],
      ['a reset stops it at zero', 'true', c => c.stepLaw('a reset stops it at zero', (_: Any, a: Any) => a.in('stopped').and(a.elapsed.eq(0)), (b: Any) => b.event.is('reset'))],
      ['a tick while stopped changes nothing', 'true', c => c.stepLaw('a tick while stopped changes nothing', ({elapsed}: Any, a: Any) => a.elapsed.eq(elapsed).and(a.in('stopped')), (b: Any) => b.in('stopped').and(b.event.is('TICK')))],
      ['the time stays at most 100', 'false', c => c.law('the time stays at most 100', ({elapsed}: Any) => elapsed.atMost(100))],
    ]},
  {id: 'xstate/examples/timer', kind: 'chart',
    // timerMachine.ts: minute and second add time while stopped; start runs it with time left; each TICK (the invoked
    // ticker's) takes a second, and the eventless transition stops it at 0; the root's reset (with time left) zeroes it,
    // which the eventless transition then stops.
    hand: () => chart('timer').context({seconds: int.from(0)}).states({stopped: {}, running: {}})
      .on('start', {from: 'stopped', to: 'running', when: ({seconds}: Any) => seconds.gt(0)})
      .on('minute', {from: 'stopped', set: ({seconds}: Any) => ({seconds: seconds.plus(60)})}).on('second', {from: 'stopped', set: ({seconds}: Any) => ({seconds: seconds.plus(1)})})
      .on('stop', {from: 'running', to: 'stopped'})
      .on('TICK', {from: 'running', to: 'stopped', when: ({seconds}: Any) => seconds.eq(1), set: ({seconds}: Any) => ({seconds: seconds.minus(1)})}).on('TICK', {from: 'running', set: ({seconds}: Any) => ({seconds: seconds.minus(1)})})
      .on('reset', {from: 'running', to: 'stopped', when: ({seconds}: Any) => seconds.gt(0), set: () => ({seconds: 0})}).on('reset', {from: 'stopped', when: ({seconds}: Any) => seconds.gt(0), set: () => ({seconds: 0})}),
    laws: [
      ['the seconds never go below 0', 'true', c => c.law('the seconds never go below 0', ({seconds}: Any) => seconds.atLeast(0))],
      ['it runs only with time left', 'true', c => c.law('it runs only with time left', (env: Any) => env.in('running').implies(env.seconds.atLeast(1)))],
      ['the last tick stops it', 'true', c => c.stepLaw('the last tick stops it', (_: Any, a: Any) => a.in('stopped'), (b: Any) => b.in('running').and(b.event.is('TICK'), b.seconds.eq(1)))],
      ['the seconds stay at most 60', 'false', c => c.law('the seconds stay at most 60', ({seconds}: Any) => seconds.atMost(60))],
    ]},
]

const rows: Record<string, unknown>[] = []
for (const k of cases) {
  const s = sources.find(x => x.id === k.id)!
  const text = await code(s), file = s.file ?? s.path.split('/').pop()!
  const files = s.lines ? {} : await importsOf(s, text)
  const x = k.kind === 'chart' ? extractXState(text, {file, entry: s.entry, xstate: xstate as never}) : extract(text, {file, entry: s.entry, ...(s.init !== undefined ? {init: s.init} : {}), ...(s.domains ? {domains: s.domains} : {}),
    ...(Object.keys(files).length ? {files} : {}), check: {modules: {'@reduxjs/toolkit': rtk, xstate}}})
  if (!x.ok) { rows.push({id: k.id, extracted: false, refusal: x.refusals[0]}); console.log(`${k.id}: not extracted (${x.refusals[0]?.what})`); continue }
  const extracted: Any = k.kind === 'chart' ? (x as Any).chart : (x as Any).rule, hand = k.hand()
  // The extracted rule's representation invariants (each key a map doesn't hold holds the defaults): proven, and beside
  // each law there, as its laws are about the code's states.
  const inv: Law[] = (x as Any).invariants ?? []
  if (inv.length) { const v = proveRule(extracted, inv); rows.push({id: k.id, invariants: inv.map(l => l.name), proven: v.proven && v.checked}); console.log(`${k.id}: its invariants ${v.proven && v.checked ? 'proven' : 'NOT proven'}`) }
  for (const [name, expect, mk] of k.laws) {
    const verdicts = [extracted, hand].map(r => {
      const l = mk(r), isStep = 'then' in l, given = r === extracted ? inv : []
      const t0 = performance.now(), v = (k.kind === 'chart' ? chartProve : ruleProve)(r, isStep ? given : [...given, l as Law], isStep ? [l as StepLaw] : [])
      return {verdict: verdictOf(v), ms: Math.round(performance.now() - t0)}
    })
    const row = {id: k.id, law: name, expect, extracted: verdicts[0], hand: verdicts[1], agree: verdicts[0]!.verdict === verdicts[1]!.verdict}
    rows.push(row)
    console.log(`${row.agree ? 'agree   ' : 'DISAGREE'} ${k.id}: ${name} (${expect}): extracted ${verdicts[0]!.verdict}, by hand ${verdicts[1]!.verdict}`)
  }
}
writeFileSync(join(out, 'verdicts.jsonl'), rows.map(r => JSON.stringify(r)).join('\n') + '\n')
const laws = rows.filter(r => 'law' in r)
console.log(`${laws.length} laws over ${new Set(laws.map(r => r.id)).size} examples: ${laws.filter(r => r.agree).length} agree, ${laws.filter(r => !r.agree).length} disagree`)
