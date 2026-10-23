// vef-framework-react (coldsmirk), the resumable multipart uploader's lifecycle, XState v5. Apache-2.0, (c) coldsmirk.
// https://github.com/coldsmirk/vef-framework-react/blob/82b2a9e063a378f7b7da1c5c88633493beb2fbae/packages/core/src/storage/uploader-machine.ts
//
// START opens (or resumes) a multipart session, uploads every part, completes the session; each phase that rejects
// ends in `failed` (the session kept for a resume), an ABORT in any active phase tears the session down (`aborting`,
// then `aborted` either way). An abort latched before the run sends START straight to aborting.
//
// fromXState refuses the machine (repro/xstate-refusals.ts): `invoke` on initializing first; also inline `params`
// functions on recordFailure. The chart is by hand, one transition per transition of the code:
//   - each invoked promise's onDone / onError is an event (PREPARE_DONE / PREPARE_ERROR, PARTS_DONE / PARTS_ERROR,
//     COMPLETE_DONE / COMPLETE_ERROR, ABORT_DONE / ABORT_ERROR), sent only in the state that invoked it (leaving the
//     state stops the actor);
//   - the guard abortRequested reads the Uploader (deps.abortRequested()): sent in with START as `latched`;
//   - ghost counters (not the code's) count the side effects: each phase's promise started (entering its state), the
//     failures recorded (recordFailure), the transports killed (aborting's entry). repro/conform-vef.ts runs the
//     ORIGINAL machine with controlled promises beside the chart and compares the state and these counts.
import {bool} from '../../../core/dsl.ts'
import {chart} from '../../../core/chart.ts'
import {type RealItem, chartLaw, chartStep, leadsTo} from '../lib.ts'

const src = {repo: 'coldsmirk/vef-framework-react', commit: '82b2a9e063a378f7b7da1c5c88633493beb2fbae', licence: 'Apache-2.0', author: 'coldsmirk', language: 'TypeScript'}

export const events = ['START', 'ABORT', 'PREPARE_DONE', 'PREPARE_ERROR', 'PARTS_DONE', 'PARTS_ERROR', 'COMPLETE_DONE', 'COMPLETE_ERROR', 'ABORT_DONE', 'ABORT_ERROR'] as const
export const uploader = () => chart('uploader')
  .events(...events)
  .inputs({latched: bool}) // deps.abortRequested() at START (:82-84)
  // ghost: prepareSession, uploadParts, completeSession, abortSession started; recordFailure calls; killTransport calls
  .context({prepares: 0, uploads: 0, completes: 0, aborts: 0, failures: 0, kills: 0})
  // :85-145, in the code's order
  .states({idle: {}, initializing: {}, uploading: {}, completing: {}, aborting: {}, succeeded: {final: true}, failed: {final: true}, aborted: {final: true}})
  // :89-94 START: [{guard abortRequested, target aborting}, {target initializing}]; aborting's entry kills the transport
  // and invokes abortSession; initializing invokes prepareSession
  .on('START', {from: 'idle', to: 'aborting', when: ({latched}) => latched, set: ({aborts, kills}) => ({aborts: aborts.plus(1), kills: kills.plus(1)})})
  .on('START', {from: 'idle', to: 'initializing', set: ({prepares}) => ({prepares: prepares.plus(1)})})
  // :96-108 initializing: onDone → uploading (invokes uploadParts), onError → failed (recordFailure), ABORT → aborting
  .on('PREPARE_DONE', {from: 'initializing', to: 'uploading', set: ({uploads}) => ({uploads: uploads.plus(1)})})
  .on('PREPARE_ERROR', {from: 'initializing', to: 'failed', set: ({failures}) => ({failures: failures.plus(1)})})
  // :109-118 uploading: onDone → completing (invokes completeSession), onError → failed, ABORT → aborting
  .on('PARTS_DONE', {from: 'uploading', to: 'completing', set: ({completes}) => ({completes: completes.plus(1)})})
  .on('PARTS_ERROR', {from: 'uploading', to: 'failed', set: ({failures}) => ({failures: failures.plus(1)})})
  // :119-128 completing: onDone → succeeded, onError → failed, ABORT → aborting
  .on('COMPLETE_DONE', {from: 'completing', to: 'succeeded'})
  .on('COMPLETE_ERROR', {from: 'completing', to: 'failed', set: ({failures}) => ({failures: failures.plus(1)})})
  .on('ABORT', {from: ['initializing', 'uploading', 'completing'], to: 'aborting', set: ({aborts, kills}) => ({aborts: aborts.plus(1), kills: kills.plus(1)})})
  // :129-137 aborting: abortSession settles either way into aborted
  .on('ABORT_DONE', {from: 'aborting', to: 'aborted'})
  .on('ABORT_ERROR', {from: 'aborting', to: 'aborted'})

const c = uploader()
const ev = (e: (typeof events)[number]) => events.indexOf(e)
const finals = ['succeeded', 'failed', 'aborted'] as const
export const items: RealItem[] = [{
  id: 'xstate/vef-framework-react/uploader',
  domain: 'xstate',
  source: {...src, path: 'packages/core/src/storage/uploader-machine.ts', lines: '65-147', export: 'createUploaderMachine'},
  summary: 'A resumable multipart upload: open the session, upload the parts, complete; a phase failure ends in failed (session kept for resume), an abort in any active phase tears the session down.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'invoke of four fromPromise actors (prepareSession, uploadParts, completeSession, abortSession): their onDone/onError are events from outside, sent only in the invoking state; the parts\' own worker pool and retries (deps.uploadParts) are outside the machine'},
    {gap: 'chart-subset', blocks: 'part', detail: 'fromXState refuses it: invoke on initializing (first); also an action with inline `params` functions (recordFailure, :103-105); the chart is by hand'},
    {gap: 'external', blocks: 'part', detail: 'the guard abortRequested reads the Uploader (deps.abortRequested(), :82-84): sent in with START'},
  ],
  laws: [
    chartLaw(c, c.law('the parts are uploaded at most once', ({uploads}) => uploads.atMost(1)),
      'safety', 'inferred', 'an uploaded file is never re-uploaded: START is accepted only in idle (:88-95) and every end state is final'),
    chartLaw(c, c.law('the backend session is aborted at most once', ({aborts}) => aborts.atMost(1)),
      'safety', 'docs', ':27-29 "Best-effort backend `abort_upload` ... the machine lands in `aborted` either way"'),
    chartLaw(c, c.law('a failure is recorded exactly when the upload failed', env => env.in('failed').implies(env.failures.eq(1)).and(env.in('failed').not().implies(env.failures.eq(0)))),
      'safety', 'docs', ':38-41 "Record the error a phase rejected with; `start()` rejects with it once the machine reaches `failed`"'),
    ...finals.map(f => chartStep(c, c.stepLaw(`${f} is never left`, (_, after) => after.in(f), b => b.in(f)),
      'step', 'docs', `:142-144 ${f}: {type: 'final'}`)),
    chartStep(c, c.stepLaw('an abort in an active phase always tears the session down', (_, after) => after.in('aborting'), b => b.event.is('ABORT').and(b.in('initializing').or(b.in('uploading'), b.in('completing')))),
      'step', 'docs', ':56-57 "a caller abort always transitions to `aborting` (backend session torn down)"'),
    chartStep(c, c.stepLaw('a phase that rejects always ends in failed', (_, after) => after.in('failed'), b => b.event.is('PREPARE_ERROR').and(b.in('initializing')).or(b.event.is('PARTS_ERROR').and(b.in('uploading')), b.event.is('COMPLETE_ERROR').and(b.in('completing')))),
      'step', 'docs', ':55-56 "a phase rejection always means failure (`onError` → `failed`, session kept alive for resume)"'),
    chartStep(c, c.stepLaw('ABORT while idle changes nothing', (b, after) => after.in('idle').and(after.aborts.eq(b.aborts)), b => b.in('idle').and(b.event.is('ABORT'))),
      'step', 'inferred', 'idle (:88-95) has no ABORT transition: the abort is latched by the Uploader (abortRequested), not the machine'),
    leadsTo(c.rule, c.rule.leadsTo('a started upload ends succeeded, failed or aborted', {
      from: env => c.in(env, 'initializing').or(c.in(env, 'uploading'), c.in(env, 'completing'), c.in(env, 'aborting')),
      to: env => c.in(env, 'succeeded').or(c.in(env, 'failed'), c.in(env, 'aborted')),
      helpful: [
        {when: env => c.in(env, 'initializing'), request: () => ({event: ev('PREPARE_DONE')})},
        {when: env => c.in(env, 'uploading'), request: () => ({event: ev('PARTS_DONE')})},
        {when: env => c.in(env, 'completing'), request: () => ({event: ev('COMPLETE_DONE')})},
        {when: env => c.in(env, 'aborting'), request: () => ({event: ev('ABORT_DONE')})},
      ],
    }), 'docs', ':50-52 "State names are exactly the public `UploadStatus` values"; every phase settles (onDone/onError) into the next phase or an end state; fairness: each settles eventually'),
  ],
}]
