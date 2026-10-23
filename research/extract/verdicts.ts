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
import {type Verdict, int, oneOf, proveRule, proveSteps, rule} from '../../core/dsl.ts'
import {chart} from '../../core/chart.ts'
import type {Law} from '../../core/machine.ts'
import type {StepLaw} from '../../kernel/kernel.ts'

const here = import.meta.dir, args = process.argv.slice(2), outAt = args.indexOf('--out')
const out = outAt >= 0 ? args[outAt + 1]! : join(here, '../../runs/extract/verdicts-local')
mkdirSync(out, {recursive: true})
type Src = {id: string, repo: string, commit: string, path: string, lines?: string, file?: string, entry: string, shape?: string, init?: unknown}
const sources = JSON.parse(readFileSync(join(here, 'sources.json'), 'utf8')) as Src[]
const code = async (s: Src) => {
  const cache = join(here, '.cache', s.repo, s.commit, s.path)
  let text: string
  try { text = readFileSync(cache, 'utf8') } catch {
    const res = await fetch(`https://raw.githubusercontent.com/${s.repo}/${s.commit}/${s.path}`)
    text = await res.text()
    mkdirSync(join(cache, '..'), {recursive: true}); writeFileSync(cache, text)
  }
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
]

const rows: Record<string, unknown>[] = []
for (const k of cases) {
  const s = sources.find(x => x.id === k.id)!
  const text = await code(s), file = s.file ?? s.path.split('/').pop()!
  const x = k.kind === 'chart' ? extractXState(text, {file, entry: s.entry, xstate: xstate as never}) : extract(text, {file, entry: s.entry, ...(s.init !== undefined ? {init: s.init} : {})})
  if (!x.ok) { rows.push({id: k.id, extracted: false, refusal: x.refusals[0]}); console.log(`${k.id}: not extracted (${x.refusals[0]?.what})`); continue }
  const extracted: Any = k.kind === 'chart' ? (x as Any).chart : (x as Any).rule, hand = k.hand()
  for (const [name, expect, mk] of k.laws) {
    const verdicts = [extracted, hand].map(r => {
      const l = mk(r), isStep = 'then' in l
      const t0 = performance.now(), v = (k.kind === 'chart' ? chartProve : ruleProve)(r, isStep ? [] : [l as Law], isStep ? [l as StepLaw] : [])
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
