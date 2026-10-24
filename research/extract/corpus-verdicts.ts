// The real-world corpus's laws (research/realworld/items/*.ts) on the rules gdp-wired/extract reads from the corpus's
// own code, beside the same laws on the item's rule by hand: each law stated again in the extracted rule's terms (its
// events are XState's own names, its context the code's fields), proven the corpus's way (lib.ts: the default search
// at the budget given, a liveness law with no rank), and the two verdicts compared. A law that reads what the code
// doesn't keep (a ghost counter the item adds) has no statement on the code's own rule: listed, not compared.
//
//   bun research/extract/corpus-verdicts.ts --jobs > research/extract/corpus-jobs.json    one job per law
//   bun research/extract/corpus-verdicts.ts --one <case> <k> [--ms 60000]                 one law, both sides (a job)
//   bun research/extract/corpus-verdicts.ts --from <dir>                                  the rows of a batch
import {readFileSync, readdirSync} from 'node:fs'
import {join} from 'node:path'
import * as xstate5 from 'xstate'
import * as xstate4 from 'xstate4'
import {extract, extractXState} from '../../core/extract.ts'
import {type Verdict, same} from '../../core/dsl.ts'
import type {Chart} from '../../core/chart.ts'
import {fetchSource, importsOf} from './fetch.ts'
import {corpus} from '../realworld/corpus.ts'
import {type RealLaw, chartLaw, chartStep, leadsTo} from '../realworld/lib.ts'

const here = import.meta.dir, args = process.argv.slice(2)
const arg = (k: string) => { const i = args.indexOf(k); return i < 0 ? undefined : args[i + 1] }
const ms = Number(arg('--ms') ?? 60_000)
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
type Real = {item: string, path: string, export: string, repo: string, commit: string, language: string}
const sources = JSON.parse(readFileSync(join(here, 'realworld-sources.json'), 'utf8')) as Real[]
const v4 = (code: string) => !/\bsetup\s*\(/.test(code) && /\bcond\s*:|predictableActionArguments|\bInterpreter\b|\bservices\s*:|\bschema\s*:/.test(code)
// The machine the code makes, read as run.ts reads it (the whole file, its relative imports).
async function chartOf(path: string): Promise<Chart<Any, Any, Any>> {
  const s = sources.find(x => x.path === path)!
  const code = await fetchSource(s), files = await importsOf(s, code), entry = /^[\w$]+/.exec(s.export.trim())![0]
  const x = extractXState(code, {file: s.path.split('/').pop()!, entry, xstate: (v4(code) ? xstate4 : xstate5) as never, files, check: {runs: 200, depth: 16}})
  if (!x.ok) throw new Error(`${path} not extracted: ${JSON.stringify(x.refusals)}`)
  return x.chart as Chart<Any, Any, Any>
}
// A law on the extracted chart, or why it has no statement there.
type Stated = RealLaw | {unstated: string}
type Case = {id: string, item: string, path: string, laws: (c: Chart<Any, Any, Any>, ev: (e: string) => number) => Stated[]}
const ghost = (what: string): Stated => ({unstated: `it reads ${what}, a ghost the item adds (the code keeps no such value)`})
const finals = ['succeeded', 'failed', 'aborted'] as const
const cases: Case[] = [
  {id: 'vef', item: 'xstate/vef-framework-react/uploader', path: 'packages/core/src/storage/uploader-machine.ts', laws: (c, ev) => {
    const done = (s: string) => `xstate.done.actor.0.uploader.${s}`, error = (s: string) => `xstate.error.actor.0.uploader.${s}`
    return [
      ghost('uploads (the parts uploaded)'), ghost('aborts (the backend sessions aborted)'), ghost('failures (recordFailure\'s calls)'),
      ...finals.map(f => chartStep(c, c.stepLaw(`${f} is never left`, (_, after) => after.in(f), b => b.in(f)), 'step', 'docs', '')),
      chartStep(c, c.stepLaw('an abort in an active phase always tears the session down', (_, after) => after.in('aborting'), b => b.event.is('ABORT').and(b.in('initializing').or(b.in('uploading'), b.in('completing')))), 'step', 'docs', ''),
      chartStep(c, c.stepLaw('a phase that rejects always ends in failed', (_, after) => after.in('failed'), b => b.event.is(error('initializing')).and(b.in('initializing')).or(b.event.is(error('uploading')).and(b.in('uploading')), b.event.is(error('completing')).and(b.in('completing')))), 'step', 'docs', ''),
      ghost('aborts (beside idle: the state part alone is another law)'),
      leadsTo(c.rule, c.rule.leadsTo('a started upload ends succeeded, failed or aborted', {
        from: env => c.in(env, 'initializing').or(c.in(env, 'uploading'), c.in(env, 'completing'), c.in(env, 'aborting')),
        to: env => c.in(env, 'succeeded').or(c.in(env, 'failed'), c.in(env, 'aborted')),
        helpful: [
          {when: env => c.in(env, 'initializing'), request: () => ({event: ev(done('initializing'))})},
          {when: env => c.in(env, 'uploading'), request: () => ({event: ev(done('uploading'))})},
          {when: env => c.in(env, 'completing'), request: () => ({event: ev(done('completing'))})},
          {when: env => c.in(env, 'aborting'), request: () => ({event: ev(done('aborting'))})},
        ],
      }), 'docs', ''),
    ]
  }},
  {id: 'radio', item: 'xstate/radio-room/radioStream', path: 'apps/web/src/machines/radioStreamMachine.ts', laws: (c, ev) => {
    // The hand's url is maybe(nat) (0 the empty string), its hasError whether the error is set: here the url is the
    // code's string | null, the error the code's string | null.
    const hasUrl = (url: Any) => url.isSome.and(url.inner.eq('').not())
    return [
      chartLaw(c, c.law('the retries stay within 3', ({retries}) => retries.atMost(3)), 'safety', 'docs', ''),
      chartStep(c, c.stepLaw('a fourth consecutive failure gives up', (_, after) => after.in('failed'), b => b.in('active').and(b.retries.eq(3), b.event.is('ELEMENT_ERROR').or(b.event.is('ELEMENT_ENDED')))), 'step', 'docs', ''),
      chartStep(c, c.stepLaw('reaching playback resets the retries', (_, after) => after.retries.eq(0), b => b.in('active.loading').and(b.event.is('ELEMENT_PLAYING'))), 'step', 'docs', ''),
      chartStep(c, c.stepLaw('a stream fails with its error set', (_, after) => after.error.isSome, b => b.in('failed').not().and(b.event.is('ELEMENT_ERROR').or(b.event.is('ELEMENT_ENDED')), b.in('active'), b.retries.atLeast(3))), 'step', 'inferred', ''),
      chartLaw(c, c.law('the stream connects only with a url', env => env.in('active').implies(hasUrl(env.url))), 'safety', 'tests', ''),
      chartStep(c, c.stepLaw('TEARDOWN drops the stream and forgets the url', (_, after) => after.in('idle').and(after.url.isNone, after.playing.not(), after.retries.eq(0)), b => b.event.is('TEARDOWN')), 'step', 'docs', ''),
      chartStep(c, c.stepLaw('an element event outside active changes nothing', (b, after) => after.in('active').not().and(after.retries.eq(b.retries), same(after.error.isSome, b.error.isSome), same(after.mseRejected, b.mseRejected)), b => b.in('active').not().and(b.event.is('ELEMENT_ERROR').or(b.event.is('ELEMENT_ENDED'), b.event.is('ELEMENT_PLAYING'), b.event.is('MSE_FALLBACK')))), 'step', 'inferred', ''),
      leadsTo(c.rule, c.rule.leadsTo('a reconnect wait always ends', {from: env => c.in(env, 'reconnecting'), to: env => c.in(env, 'reconnecting').not(), helpful: () => ({event: ev('xstate.after.1200.radioStream.reconnecting')})}), 'docs', ''),
    ]
  }},
  {id: 'gapless', item: 'xstate/gapless.js/track', path: 'src/machines/track.machine.ts', laws: (c, ev) => [
    chartStep(c, c.stepLaw('DEACTIVATE from any state lands in idle', (_, after) => after.in('idle'), b => b.event.is('DEACTIVATE')), 'step', 'tests', ''),
    chartStep(c, c.stepLaw('DEACTIVATE keeps the buffer\'s loading state', (b, after) => same(after.webAudioLoadingState, b.webAudioLoadingState), b => b.event.is('DEACTIVATE')), 'step', 'tests', ''),
    ghost('fetches (the children spawned)'),
    chartLaw(c, c.law('Web Audio plays only a loaded buffer', env => env.in('webaudio').implies(env.webAudioLoadingState.is('LOADED'))), 'safety', 'docs', ''),
    chartLaw(c, c.law('while Web Audio plays the track reports WEBAUDIO', env => env.in('webaudio').implies(env.playbackType.is('WEBAUDIO'))), 'safety', 'tests', ''),
    chartStep(c, c.stepLaw('a buffer ready while preloading never leaves the track in loading', (_, after) => after.in('loading').not(), b => b.in('loading').and(b.event.is('BUFFER_READY'))), 'step', 'tests', ''),
    chartStep(c, c.stepLaw('a buffer error while Web Audio plays changes nothing', (b, after) => after.in('webaudio').and(same(after.webAudioLoadingState, b.webAudioLoadingState), same(after.isPlaying, b.isPlaying)), b => b.in('webaudio').and(b.event.is('BUFFER_ERROR'))), 'step', 'inferred', ''),
    leadsTo(c.rule, c.rule.leadsTo('a pending play starts on Web Audio or is dropped once the buffer is ready', {from: ({pendingPlay}) => pendingPlay, to: env => env.pendingPlay.not().or(c.in(env, 'webaudio')), helpful: () => ({event: ev('BUFFER_READY')})}), 'docs', ''),
  ]},
  {id: 'opendecision', item: 'xstate/open-decision/websocket', path: 'packages/tree/sync/src/websocket.machine.ts', laws: (c, ev) => [
    chartLaw(c, c.law('the retries stay within the retry limit', ({retries, retryLimit}) => retries.atMost(retryLimit)), 'safety', 'inferred', ''),
    chartStep(c, c.stepLaw('error is never left', (_, after) => after.in('error'), b => b.in('error')), 'step', 'docs', ''),
    chartStep(c, c.stepLaw('a dropped connection under the limit is retried', (_, after) => after.in('retry'), b => b.in('connected').and(b.event.is('connection.error'), b.retries.lt(b.retryLimit))), 'step', 'inferred', ''),
    chartStep(c, c.stepLaw('OPEN while connected changes nothing', (b, after) => after.in('connected').and(after.retries.eq(b.retries)), b => b.in('connected').and(b.event.is('OPEN'))), 'step', 'inferred', ''),
    chartStep(c, c.stepLaw('CLOSE ends an open connection', (_, after) => after.in('connected').not(), b => b.in('connected').and(b.event.is('CLOSE'))), 'step', 'docs', ''),
    chartStep(c, c.stepLaw('a synced connection resets the retries', (_, after) => after.retries.eq(0), b => b.in('connected').and(b.event.is('connection.ready'))), 'step', 'inferred', ''),
    leadsTo(c.rule, c.rule.leadsTo('an opening connection ends connected or failed', {
      from: env => c.in(env, 'retry').or(c.in(env, 'authenticating')),
      to: env => c.in(env, 'connected').or(c.in(env, 'error')),
      helpful: [{when: env => c.in(env, 'retry'), request: () => ({event: ev('xstate.after(retry_delay)#websocketMachine.retry')})}, {when: env => c.in(env, 'authenticating'), request: () => ({event: ev('done.invoke.authenticate')})}],
    }), 'inferred', ''),
  ]},
]
// The rule the corpus's upstash item proves its laws of is the token bucket with the block cache together (single.ts
// and cache.ts); the source extracted is the cache alone, whose laws are none of the item's.
const NOT_COMPARED = [{item: 'rate limit/upstash-ratelimit/tokenBucket', path: 'src/cache.ts', why: "the item's rule is the token bucket (single.ts, its Lua) with the cache: its laws are about both; the source extracted is the cache alone"}]

const verdictOf = (v: Verdict, decision = false): string => (v.proven && v.checked ? 'proven' : v.run || (decision && v.stuck === 'sat' && v.witness) ? 'refuted' : 'unknown')
const prove = (l: RealLaw): {verdict: string, ms: number, error?: string} => {
  const t = performance.now()
  try { return {verdict: verdictOf(l.prove(ms), l.form === 'decision'), ms: Math.round(performance.now() - t)} } catch (e) { return {verdict: 'error', ms: Math.round(performance.now() - t), error: String((e as Error).message).slice(0, 300)} }
}

if (args.includes('--jobs')) {
  const q = (s: string) => `'${s.replace(/'/g, `'\\''`)}'`
  const jobs = cases.flatMap(k => corpus.find(i => i.id === k.item)!.laws.map((_, j) => ({
    name: `corpus-${k.id}-${j}`,
    cmd: `bun install --frozen-lockfile >/dev/null 2>&1; timeout -s KILL 280 bun research/extract/corpus-verdicts.ts --one ${q(k.id)} ${j} --ms 60000 2>&1 | tail -1`,
    cpu: 2.0, timeout: 330,
  })))
  console.log(JSON.stringify(jobs, null, 1))
  process.exit(0)
}
const oneAt = args.indexOf('--one')
if (oneAt >= 0) {
  const k = cases.find(x => x.id === args[oneAt + 1])!, j = Number(args[oneAt + 2]), item = corpus.find(i => i.id === k.item)!, law = item.laws[j]!
  const c = await chartOf(k.path), events = (c.rule as Any).spec.inputs.find(([n]: [string]) => n === 'event')[1].values as string[]
  const ev = (e: string) => { const i = events.indexOf(e); if (i < 0) throw new Error(`the extracted chart has no event ${e}`); return i }
  const stated = k.laws(c, ev)[j]!
  const hand = prove(law)
  const row = 'unstated' in stated
    ? {case: k.id, item: k.item, law: j, name: law.name, hand, extracted: {verdict: 'unstated', why: stated.unstated}}
    : {case: k.id, item: k.item, law: j, name: law.name, hand, extracted: prove(stated), agree: undefined as boolean | undefined}
  if ('agree' in row) row.agree = row.hand.verdict === row.extracted.verdict
  console.log(JSON.stringify(row))
  process.exit(0)
}
const from = arg('--from')
if (from) {
  const rows = readdirSync(from).filter(f => f.endsWith('.log')).map(f => { const l = readFileSync(join(from, f), 'utf8').trim().split('\n').at(-1)!; try { return JSON.parse(l) } catch { return {file: f, error: l.slice(0, 300)} } })
  for (const r of rows) console.log(JSON.stringify(r))
  for (const n of NOT_COMPARED) console.log(JSON.stringify({item: n.item, path: n.path, notCompared: n.why}))
  const stated = rows.filter(r => r.agree !== undefined)
  console.log(`${rows.length} laws: ${stated.length} stated on the extracted rule (${stated.filter(r => r.agree).length} agree, ${stated.filter(r => !r.agree).length} disagree), ${rows.filter(r => r.extracted?.verdict === 'unstated').length} unstated`)
}
