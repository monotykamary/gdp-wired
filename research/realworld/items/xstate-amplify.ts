// AWS Amplify UI (aws-amplify/amplify-ui), the Authenticator's forgot-password actor, XState v4 (^4.33.6). Apache-2.0,
// (c) Amazon.com, Inc. https://github.com/aws-amplify/amplify-ui/blob/1150de70d59e9f9879693e93d2f8e3dcef464fc7/packages/ui/src/machines/authenticator/actors/forgotPassword.ts
// (the machine), ../guards.ts and ../actions.ts (what its named guards and actions do).
//
// A two-step password reset: enter the username (forgotPassword: edit, then submit asks Cognito to send a code), then
// the code and the new password (confirmResetPassword: a validation region re-validating the fields on every change,
// beside a submission region that validates, submits, or resends the code); `resolved` (final) hands the next step
// to the parent. A parent that already knows the step (RESET_PASSWORD, CONFIRM_RESET_PASSWORD_WITH_CODE) starts in
// confirmResetPassword.
//
// fromXState refuses the machine (repro/xstate-refusals.ts): `always` on init first; it also has a parallel state
// below the root (confirmResetPassword), `invoke` (four promise services), entry and exit actions that write the
// context (clearError, clearTouched, clearFormValues), the v4 `cond` (not read by fromXState) and `sendUpdate`. The
// chart is by hand:
//   - init's `always` (:21-35) is the event INIT, only in init, choosing by the parent's step (the param `startStep`);
//   - the parallel confirmResetPassword is flattened: the submission region is its states, the validation region
//     (pending / valid / invalid, :78-110) the context field `validation`;
//   - each invoked service's onDone / onError is an event, only in the state that invoked it: RESET_DONE/ERROR
//     (forgotPassword.submit), RESEND_DONE/ERROR (submission.resendCode), CHECK_DONE/ERROR (submission.validate's
//     validateFields), FIELDS_DONE/ERROR (the validation region's validateFields, while it is pending),
//     CONFIRM_DONE/ERROR (submission.pending); a service's result is the payload `next` (nextStep.resetPasswordStep);
//   - entry and exit writes are folded into the transitions that enter or leave those states;
//   - the context's form values, touched fields and messages as whether the error and field errors are set; ghost
//     counters (not the code's) count the code requests (handleResetPassword) and the confirmations sent
//     (handleConfirmResetPassword).
import {oneOf} from '../../../core/dsl.ts'
import {chart} from '../../../core/chart.ts'
import {type RealItem, chartLaw, chartStep, leadsTo} from '../lib.ts'

const src = {repo: 'aws-amplify/amplify-ui', commit: '1150de70d59e9f9879693e93d2f8e3dcef464fc7', licence: 'Apache-2.0', author: 'Amazon.com, Inc. (aws-amplify)', language: 'TypeScript'}

export const events = ['INIT', 'SUBMIT', 'CHANGE', 'BLUR', 'RESEND', 'RESET_DONE', 'RESET_ERROR', 'FIELDS_DONE', 'FIELDS_ERROR', 'CHECK_DONE', 'CHECK_ERROR', 'RESEND_DONE', 'RESEND_ERROR', 'CONFIRM_DONE', 'CONFIRM_ERROR'] as const
const Step = oneOf('RESET_PASSWORD', 'CONFIRM_RESET_PASSWORD_WITH_CODE', 'RESET_PASSWORD_COMPLETE', 'SIGN_IN', 'OTHER')
const B = (init: boolean) => ({kind: oneOf('no', 'yes'), init: init ? 'yes' : 'no'})
export const forgotPassword = () => chart('forgotPasswordActor')
  .events(...events)
  .params({startStep: oneOf('RESET_PASSWORD', 'CONFIRM_RESET_PASSWORD_WITH_CODE', 'OTHER')}) // the parent's context.step
  .inputs({next: oneOf('DONE', 'CONFIRM_RESET_PASSWORD_WITH_CODE')}) // a service's nextStep.resetPasswordStep
  .context({
    // the parent's step at spawn is `startStep`; `step` starts as OTHER here, and every way to resolved sets it
    step: {kind: Step, init: 'OTHER'}, remoteError: B(false), fieldErrors: B(false),
    validation: {kind: oneOf('pending', 'valid', 'invalid'), init: 'pending'},
    requests: 0, confirms: 0, // ghost
  })
  .states({
    init: {},
    forgotPassword: {states: {edit: {}, submit: {}}},
    confirmResetPassword: {states: {idle: {}, validate: {}, resendCode: {}, pending: {}}},
    resolved: {final: true},
  })
  // :21-35 always: [{cond shouldResetPassword (step === 'RESET_PASSWORD')}, {cond shouldConfirmResetPassword}] →
  // confirmResetPassword, else forgotPassword. Entering confirmResetPassword enters validation.pending (its
  // validateFields invoked) and submission.idle
  .on('INIT', {from: 'init', to: 'confirmResetPassword', when: ({startStep}) => startStep.is('OTHER').not(), set: () => ({validation: 'pending'})})
  .on('INIT', {from: 'init', to: 'forgotPassword'})
  // :43-48 edit: SUBMIT → submit (handleSubmit); CHANGE (handleInput), BLUR (handleBlur): the form only. submit's entry
  // (:51) clears the error and invokes handleResetPassword
  .on('SUBMIT', {from: 'forgotPassword.edit', to: 'forgotPassword.submit', set: ({requests}) => ({remoteError: 'no', requests: requests.plus(1)})})
  .on('CHANGE', {from: 'forgotPassword.edit'})
  .on('BLUR', {from: 'forgotPassword.edit'})
  // :52-66 onDone → #confirmResetPassword (forgotPassword's exit clears the error, :40; setNextResetPasswordStep,
  // actions.ts:141-146: 'RESET_PASSWORD_COMPLETE' on DONE, else the step); onError → edit (setRemoteError)
  .on('RESET_DONE', {from: 'forgotPassword.submit', to: 'confirmResetPassword', when: ({next}) => next.is('DONE'), set: () => ({remoteError: 'no', step: 'RESET_PASSWORD_COMPLETE', validation: 'pending'})})
  .on('RESET_DONE', {from: 'forgotPassword.submit', to: 'confirmResetPassword', set: () => ({remoteError: 'no', step: 'CONFIRM_RESET_PASSWORD_WITH_CODE', validation: 'pending'})})
  .on('RESET_ERROR', {from: 'forgotPassword.submit', to: 'forgotPassword.edit', set: () => ({remoteError: 'yes'})})
  // :78-110 the validation region: validateFields done → valid (clearValidationError), error → invalid
  // (setFieldErrors); CHANGE and BLUR (in any submission state) → .pending, validated again
  .on('FIELDS_DONE', {from: 'confirmResetPassword', when: ({validation}) => validation.is('pending'), set: () => ({validation: 'valid', fieldErrors: 'no'})})
  .on('FIELDS_ERROR', {from: 'confirmResetPassword', when: ({validation}) => validation.is('pending'), set: () => ({validation: 'invalid', fieldErrors: 'yes'})})
  .on('CHANGE', {from: 'confirmResetPassword', set: () => ({validation: 'pending'})})
  .on('BLUR', {from: 'confirmResetPassword', set: () => ({validation: 'pending'})})
  // :114-122 submission.idle: SUBMIT → validate (handleSubmit), RESEND → resendCode (entry: clearError, invokes
  // handleResetPassword)
  .on('SUBMIT', {from: 'confirmResetPassword.idle', to: 'confirmResetPassword.validate'})
  .on('RESEND', {from: 'confirmResetPassword.idle', to: 'confirmResetPassword.resendCode', set: ({requests}) => ({remoteError: 'no', requests: requests.plus(1)})})
  // :123-136 validate: validateFields done → pending (clearValidationError; pending's entry clears the error and invokes
  // handleConfirmResetPassword), error → idle (setFieldErrors)
  .on('CHECK_DONE', {from: 'confirmResetPassword.validate', to: 'confirmResetPassword.pending', set: ({confirms}) => ({fieldErrors: 'no', remoteError: 'no', confirms: confirms.plus(1)})})
  .on('CHECK_ERROR', {from: 'confirmResetPassword.validate', to: 'confirmResetPassword.idle', set: () => ({fieldErrors: 'yes'})})
  // :137-145 resendCode: done → idle, error → idle (setRemoteError)
  .on('RESEND_DONE', {from: 'confirmResetPassword.resendCode', to: 'confirmResetPassword.idle'})
  .on('RESEND_ERROR', {from: 'confirmResetPassword.resendCode', to: 'confirmResetPassword.idle', set: () => ({remoteError: 'yes'})})
  // :146-163 pending: done → resolved, [{cond hasCompletedResetPassword: setNextResetPasswordStep}, {setSignInStep}]
  // (confirmResetPassword's exit, :73, clears the error); error → idle (setRemoteError)
  .on('CONFIRM_DONE', {from: 'confirmResetPassword.pending', to: 'resolved', when: ({next}) => next.is('DONE'), set: () => ({step: 'RESET_PASSWORD_COMPLETE', remoteError: 'no'})})
  .on('CONFIRM_DONE', {from: 'confirmResetPassword.pending', to: 'resolved', set: () => ({step: 'SIGN_IN', remoteError: 'no'})})
  .on('CONFIRM_ERROR', {from: 'confirmResetPassword.pending', to: 'confirmResetPassword.idle', set: () => ({remoteError: 'yes'})})

const c = forgotPassword()
const ev = (e: (typeof events)[number]) => events.indexOf(e)
export const items: RealItem[] = [{
  id: 'xstate/amplify-ui/forgotPassword',
  domain: 'xstate',
  source: {...src, path: 'packages/ui/src/machines/authenticator/actors/forgotPassword.ts', lines: '13-200', export: 'forgotPasswordActor'},
  also: [{...src, path: 'packages/ui/src/machines/authenticator/actions.ts', lines: '33-243', export: 'ACTIONS'}, {...src, path: 'packages/ui/src/machines/authenticator/guards.ts', lines: '47-95', export: 'GUARDS'}],
  summary: 'The Authenticator\'s password reset: request a code for the username, then validate and submit the code and new password (or resend the code), resolving with the next step for the parent.',
  expressible: 'partial',
  gaps: [
    {gap: 'other', blocks: 'part', detail: 'a parallel state below the root (confirmResetPassword: validation beside submission): a chart runs regions only at the top, so the validation region is the context field `validation`'},
    {gap: 'async', blocks: 'part', detail: 'invoke of handleResetPassword, validateFields (twice: one per region), handleConfirmResetPassword: their onDone/onError are events from outside, only in the invoking state'},
    {gap: 'other', blocks: 'part', detail: 'fromXState refuses it: `always` on init (first; here the event INIT); also the nested parallel state, invoke, entry/exit actions writing the context (folded into transitions), v4 `cond` (fromXState reads only v5 `guard`), sendUpdate'},
    {gap: 'other', blocks: 'part', detail: 'form values, touched fields, username and the error messages (records and strings) as whether the error and the field errors are set'},
  ],
  laws: [
    chartStep(c, c.stepLaw('resolved is never left', (_, after) => after.in('resolved'), b => b.in('resolved')),
      'step', 'docs', ':167-170 resolved: {type: \'final\'}'),
    chartLaw(c, c.law('it resolves only after a confirmation was sent', env => env.in('resolved').implies(env.confirms.atLeast(1))),
      'safety', 'inferred', 'resolved is entered only from submission.pending\'s handleConfirmResetPassword onDone (:146-160)'),
    chartStep(c, c.stepLaw('a new password is sent only after the fields validate', (b, after) => after.confirms.atMost(b.confirms).or(b.in('confirmResetPassword.validate').and(b.event.is('CHECK_DONE')))),
      'step', 'inferred', ':123-131 submission.validate invokes validateFields, onDone → pending'),
    chartStep(c, c.stepLaw('a completed reset resolves as RESET_PASSWORD_COMPLETE', (_, after) => after.in('resolved').and(after.step.is('RESET_PASSWORD_COMPLETE')), b => b.in('confirmResetPassword.pending').and(b.event.is('CONFIRM_DONE'), b.next.is('DONE'))),
      'step', 'inferred', 'guards.ts:47-48 hasCompletedResetPassword (resetPasswordStep === \'DONE\'), actions.ts:141-146 setNextResetPasswordStep'),
    chartStep(c, c.stepLaw('every request to Cognito starts with the error cleared', (_, after) => after.remoteError.is('no'), (b) => b.event.is('SUBMIT').and(b.in('forgotPassword.edit')).or(b.event.is('RESEND').and(b.in('confirmResetPassword.idle')), b.event.is('CHECK_DONE').and(b.in('confirmResetPassword.validate')))),
      'step', 'inferred', ':51, :139, :148 entry clearError on submit, resendCode and pending'),
    chartStep(c, c.stepLaw('a code is never requested while a confirmation is pending', (b, after) => after.requests.eq(b.requests), b => b.in('confirmResetPassword.pending').or(b.in('confirmResetPassword.validate'))),
      'step', 'inferred', 'RESEND is handled only in submission.idle (:118)'),
    leadsTo(c.rule, c.rule.leadsTo('a submitted new password ends resolved or back at the form', {
      from: env => c.in(env, 'confirmResetPassword.validate').or(c.in(env, 'confirmResetPassword.pending')),
      to: env => c.in(env, 'resolved').or(c.in(env, 'confirmResetPassword.idle')),
      helpful: [{when: env => c.in(env, 'confirmResetPassword.validate'), request: () => ({event: ev('CHECK_DONE')})}, {when: env => c.in(env, 'confirmResetPassword.pending'), request: () => ({event: ev('CONFIRM_DONE')})}],
    }), 'inferred', 'each invoked service settles (onDone/onError) into the next submission state'),
  ],
}]
