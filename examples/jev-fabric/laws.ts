// jev-fabric's laws (native/tests/proofs.bend, policy-proofs.bend, time-proofs.bend, decision-proofs.bend) stated
// over the port in policy.ts, each with a deliberately broken variant of the rule that must be refused; then the laws
// gdp-wired adds over runs (extras), which the Bend proofs do not state.
import {type Cond, type Fun, type Term, type TermLike, forall, min, yes} from '../../core/dsl.ts'
import {type Case, decisionCase, machineCase} from '../harness.ts'
import * as P from './policy.ts'

/* eslint-disable @typescript-eslint/no-explicit-any */
type Env = any
export type Kind = 'decide' | 'relate' | 'law' | 'step law' | 'k-step law' | 'liveness' | 'list/set' | 'outside'
export type Entry = {
  n: number // 1..59: the Bend law's place; 0 for an extra
  bend: string // file: law (or the extra's name)
  says: string
  fns: string
  kind: Kind
  encoding: 'exact' | 'interned' | 'abstracted' // exact: numbers, enums and bits only; interned: strings as names; abstracted: a string/list computation is the runtime's answer
  note?: string
  how?: 'automatic' | 'added fact' | 'added invariant'
  case: () => Case
  witness?: () => {breaks: boolean, detail: string} // the broken variant run at a concrete input, where random draws cannot reach a break
}

// A law about a function (a decision about what it returns): given (over its arguments, and its result), then (its
// result); the broken variant is the function built with `bug`.
type Out = Record<string, Term>
function D(n: number, file: string, law: string, says: string, fns: string, encoding: Entry['encoding'], mk: (bug?: any) => Fun<any, any, any>,
  given: (env: Env, o: Out) => Cond | Cond[], then: (o: Out, env: Env) => Cond, bug: string, extra: Partial<Entry> = {}): Entry {
  const name = n ? `${file}: ${law}` : law
  return {n, bend: name, says, fns, kind: 'decide', encoding, how: 'automatic', ...extra,
    case: () => decisionCase(name, says, [mk().law(name, given, then)], [{name: bug, why: says, decision: mk(bug).law(name, given, then)}])}
}
// Concrete breaks the random runs cannot reach: values past 2^32, and maps whose cells hold values (the harness draws a
// carried map as a set, cells 0 or 1).
const capWitness = () => {
  const left = 4294967296 + 5, local = 10, got = P.cap('narrows before capping').run({left, local}).out!
  const want = P.cap().run({left, local}).out!
  return {breaks: got !== want && want === Math.min(left, local), detail: `left 2^32 + 5, local 10: the broken rule gives ${got}, the law ${want}`}
}
const mergeWitness = (which: 'whole' | 'irrelevant') => () => {
  const r = P.merge('providerOptions merged recursively'), gen = r.compiled(), PO = P.KEY.providerOptions
  const st = gen.step({}, gen.init({}), r.encodeInput({baseObject: 1, overObject: 1, Base: new Map([[PO, 2]]), BaseB: new Map([[PO, 5]]), Over: new Map([[PO, 1]])} as never))
  const out = st.maps.Out?.get(PO) ?? 0, outB = st.maps.OutB?.get(PO) ?? 0
  return which === 'whole'
    ? {breaks: out !== 1, detail: `base {providerOptions: v2}, override {providerOptions: v1}: merged providerOptions is v${out}`}
    : {breaks: out !== outB, detail: `bases differing only at providerOptions (v2, v5), override v1: merges give v${out} and v${outB}`}
}
const eqAll = (o: Record<string, Term>, want: Record<string, TermLike>): Cond => yes.and(...Object.entries(want).map(([k, v]) => o[k]!.eq(v)))
const none = (): Cond[] => []

// ===================================================================================================================
// The Bend laws
// ===================================================================================================================
const pf = 'proofs.bend', pp = 'policy-proofs.bend', tp = 'time-proofs.bend', dp = 'decision-proofs.bend'
const S = P.stateIndex, N = P.nextIndex
const terminal = (n: number, file: string, s: 'Cancelled' | 'Completed' | 'Failed' | 'TimedOut', law: string) =>
  D(n, file, law, `settle(${s}, result) = ${s}: a ${s} job ignores later results`, 'Core.settle', 'exact', P.settle,
    ({state}) => state.is(s), o => o.out!.eq(S(s)), `settle reopens ${s}`)

const channel = P.channel(), channelFields = ['emitted', 'batches', 'pending', 'omitted', 'clips', 'from', 'to', 'previous'] as const
const sameChannel = (b: Env, a: Env) => yes.and(...channelFields.map(f => a[f].eq(b[f])), a.outs.eq(0))
const channelCase = (name: string, says: string, laws: (r: any) => any[], steps: (r: any) => any[], broken: [string, P.ChannelBug][]) => () =>
  machineCase(name, says, P.channel(), laws(P.channel()), broken.map(([why, bug]) => ({name: bug, why, rule: P.channel(bug), laws: laws(P.channel(bug)), steps: steps(P.channel(bug))})), {steps: steps(P.channel()), bound: 3, depth: 14})
void channel

const queueSteps = {
  order: (r: any) => r.stepsLaw('two writes into an empty queue drain in arrival order', 2,
    (_b: Env, after: Env, reqs: Env[]) => after.Q.at(0).eq(reqs[0].chunk).and(after.Q.at(1).eq(reqs[1].chunk), after.Q_len.eq(2)),
    ({Q_len, admitted}: Env, j: number) => (j === 0 ? Q_len.eq(0).and(admitted) : admitted)),
  drained: (r: any) => r.stepLaw('draining empties the queue', (_b: Env, after: Env) => after.Q_len.eq(0).and(after.total.eq(0)), ({draining}: Env) => draining),
}
const queueLaws = (r: any) => [r.law('nothing past the end', ({Q}: Env) => Q.within())]

export const bendLaws: Entry[] = [
  D(1, pf, 'exhausted_never_reserves', 'a budget with no evaluations left reserves nothing', 'Core.reserve', 'exact', P.reserve,
    ({remaining}) => remaining.eq(0), o => o.some!.eq(0), 'reserve lets an empty budget through'),
  terminal(2, pf, 'Cancelled', 'cancelled_is_terminal'),
  terminal(3, pf, 'Completed', 'completed_is_terminal'),
  D(4, pf, 'unknown_requires_inspection', 'an Unknown receipt asks for inspection', 'Core.after', 'exact', P.after,
    ({receipt}) => receipt.is('Unknown'), o => o.out!.eq(N('Inspect')), 'after reobserves Unknown'),
  D(5, pf, 'dispatch_requires_verification', 'an Executed receipt asks for verification', 'Core.after', 'exact', P.after,
    ({receipt}) => receipt.is('Executed'), o => o.out!.eq(N('Verify')), 'after escalates Executed'),

  D(6, pp, 'denied_reservation_has_no_budget', 'reserve_if(..., False) is None', 'Core.reserve_if', 'exact', P.reserveIf,
    ({allowed}) => allowed.not(), o => o.some!.eq(0), 'reserve_if ignores allowed'),
  D(7, pp, 'reservation_consumes_one', 'with one evaluation and token limit 1 at 0 spent, a reservation uses exactly one evaluation', 'Core.reserve', 'exact', P.reserve,
    ({remaining, tokens, limit}) => [remaining.atLeast(1), tokens.eq(0), limit.eq(1)],
    (o, {remaining, used}) => eqAll(o, {some: 1, remaining: remaining.minus(1), evaluations: used.plus(1), tokens: 0, limit: 1}), 'reserve counts no call'),
  D(8, pp, 'zero_token_budget_blocks', 'token limit 0 blocks a reservation', 'Core.reserve', 'exact', P.reserve,
    ({remaining, tokens, limit}) => [remaining.atLeast(1), tokens.eq(0), limit.eq(0)], o => o.some!.eq(0), 'reserve ignores the token limit'),
  D(9, pp, 'accounting_never_refunds_a_call', 'account adds the reported tokens and leaves the rest', 'Core.account', 'exact', P.account,
    none, (o, {remaining, used, tokens, limit, reported}) => eqAll(o, {remaining, evaluations: used, tokens: tokens.plus(reported), limit}), 'account drops the report'),
  terminal(10, pp, 'Failed', 'failure_is_terminal'),
  terminal(11, pp, 'TimedOut', 'timeout_is_terminal'),
  D(12, pp, 'terminal_monitor_never_polls', 'a terminal watch stops as finished', 'MonitorCore.terminal_decision', 'interned', P.monitorTerminal,
    ({terminal: tm}) => tm, o => eqAll(o, {stop: 1, reason: 0, terminal: 1}), 'limit checked before the receipt', {note: 'Stop{"finished", True}: the reason string is one of three, a oneOf', witness: () => {
      const o = P.monitorTerminal('limit checked before the receipt').run({terminal: true, lines: P.TOTAL_MAX, elapsed: 0, duration: 1})
      return {breaks: o.reason !== 0, detail: `a terminal receipt at 1024 lines: the broken rule stops with reason ${P.REASONS[o.reason!]}`}
    }}),
  D(13, pp, 'limited_monitor_never_polls', 'an output-limited watch stops', 'MonitorCore.limit_decision', 'interned', P.monitorLimit,
    ({over}) => over, o => eqAll(o, {stop: 1, reason: 1, terminal: 0}), 'output limit only stops at the deadline'),
  D(14, pp, 'expired_monitor_never_polls', 'an expired watch stops', 'MonitorCore.deadline_decision', 'interned', P.monitorDeadline,
    ({expired}) => expired, o => eqAll(o, {stop: 1, reason: 2, terminal: 0}), 'deadline keeps polling'),
  D(15, pp, 'disabled_filter_emits_nothing', 'a disabled filter emits nothing, whatever the text', 'MonitorCore.limited_match, Core.monitor', 'abstracted', P.limitedMatch,
    ({allowed}) => allowed.not(), o => o.some!.eq(0), 'disabled filter still matches', {note: 'Core.monitor (trim, contains, equality on strings) is the runtime\'s answer `hit`; the law does not read it'}),
  {n: 16, bend: `${pp}: full_channel_cannot_emit`, says: 'a push to a channel at its 1024-line cap changes nothing and emits nothing', fns: 'MonitorCore.push, accepted, finish_push, flush', kind: 'step law', encoding: 'abstracted', how: 'automatic',
    note: 'push is the step of a channel machine (total = total_max() as a param, 1024 in jev-fabric); line strings interned, the string tests the runtime\'s answer; pending lines kept as their count',
    case: channelCase(`${pp}: full_channel_cannot_emit`, 'at the cap a push changes nothing',
      () => [], r => [r.stepLaw('a full channel cannot emit', sameChannel, ({emitted, total}: Env) => emitted.eq(total))], [['the cap is not checked', 'full channel still emits']])},
  D(17, pp, 'encoding_without_fuel_fails', 'encoding any JSON value with zero fuel fails with code 22', 'JSON.write_with_fuel, JSON.encode.go', 'abstracted', P.writeWithFuel,
    ({fuel}) => fuel.eq(0), o => eqAll(o, {ok: 0, code: 22, msg: P.ENCODE_MSG}), 'zero fuel still writes', {note: 'the JSON value is a name; one expansion step (string work) the runtime\'s answer'}),
  D(18, pp, 'rejected_http_has_no_request', 'rejected HTTP configuration makes no request plan', 'HttpCore.request_allowed', 'interned', P.requestAllowed,
    ({allowed}) => allowed.not(), o => eqAll(o, {ok: 0, code: 1, msg: P.HTTP_MSG, key: 0, body: 0}), 'rejected config still planned'),
  D(19, pp, 'rejected_credential_exposes_no_key', 'a rejected credential is a fixed error that carries no key', 'CredentialCore.checked', 'interned', P.credentialChecked,
    ({valid}) => valid.not(), o => eqAll(o, {ok: 0, code: 1, msg: P.CRED_MSG, value: 0, exposed: 0}), 'error carries the key'),
  D(20, pp, 'failed_transport_rejects_bytes', 'failed or truncated transport rejects its bytes', 'HttpCore.capture_ok', 'abstracted', P.captureOk,
    ({ok}) => ok.not(), o => eqAll(o, {ok: 0, code: 1, msg: 1, value: 0}), 'failed transport still parsed', {note: 'the bytes are a name; the status parse the runtime\'s answer'}),
  D(21, pp, 'reported_overshoot_disables_calls', 'an oversized usage report zeroes the evaluations and saturates the tokens at limit + 1', 'JevCore.add_usage', 'interned', P.addUsage,
    ({oversized}) => oversized, (o, {settings, key, used, limit}) => eqAll(o, {settings, key, remaining: 0, used, tokens: limit.plus(1), limit, ok: 0, msg: 1}), 'overshoot leaves calls enabled'),
  D(22, pp, 'invalid_typed_reply_stays_failed', 'an invalid typed reply leaves the client as it was and fails', 'JevCore.response_ready', 'abstracted', P.responseReady,
    ({responseOk}) => responseOk.not(), (o, {settings, key, remaining, used, spent, limit}) => eqAll(o, {settings, key, remaining, used, tokens: spent, limit, ok: 0, msg: 2}), 'invalid reply is accounted'),
  D(23, pp, 'receipt_finishes_follow', 'a terminal receipt finishes a follow, ceiling or not', 'JobsCore.follow_decision', 'exact', P.followDecision,
    ({finished}) => finished, o => o.out!.eq(1), 'expiry beats a receipt'),
  D(24, pp, 'expired_follow_without_receipt_times_out', 'a follow past its ceiling without a receipt expires', 'JobsCore.follow_decision', 'exact', P.followDecision,
    ({finished, expired}) => [finished.not(), expired], o => o.out!.eq(2), 'expiry ignored'),
  D(25, pp, 'followed_event_is_never_repeated', 'an event at or before the cursor prints nothing and keeps the cursor', 'JobsCore.fresh', 'interned', P.fresh,
    ({unseen}) => unseen.not(), (o, {cursor}) => o.cursor!.eq(cursor).and(o.outs!.eq(0)), 'a seen event is printed again'),
  D(26, pp, 'newer_store_is_refused', 'a home of store format 2 or more is refused with newer(shown)', 'StoreCore.versioned', 'interned', P.versioned,
    ({found}) => found.atLeast(2), (o, {shown}) => eqAll(o, {out: 2, msg: 2, shown}), 'newer store adopted'),
  D(27, pp, 'current_store_is_accepted', 'a home of store format 1 is accepted', 'StoreCore.versioned', 'interned', P.versioned,
    ({found}) => found.eq(1), o => eqAll(o, {out: 0, msg: 0}), 'current store refused'),
  D(28, pp, 'writer_adopts_unmarked_home', 'a writing verb adopts an unmarked home', 'StoreCore.missing', 'exact', P.missing,
    ({mutating}) => mutating, o => o.out!.eq(1), 'writer leaves unmarked home'),
  D(29, pp, 'reader_leaves_old_home_unmarked', 'a read-only verb leaves an old unmarked home unmarked', 'StoreCore.missing', 'exact', P.missing,
    ({mutating, created}) => [mutating.not(), created.not()], o => o.out!.eq(0), 'reader adopts'),
  D(30, pp, 'minus_self', 'Spool.minus(n, n) = 0 (by induction in Bend)', 'SpoolCore.minus, less', 'exact', P.minus,
    ({a, b}) => a.eq(b), o => o.out!.eq(0), 'minus floors at one', {note: 'minus is ∸ here; that SpoolCore.less is ∸ is a fact of the encoding (an induction), held by the differential test'}),
  D(31, pp, 'read_from_start_discloses_loss', 'a read from offset 0 discloses every byte below the window as omitted', 'SpoolCore.span, from, minus', 'exact', P.span,
    ({offset}) => offset.eq(0), (o, {retained}) => o.omitted!.eq(retained), 'omitted measured from the window'),
  D(32, pp, 'nothing_lost_nothing_omitted', 'with nothing lost a read omits nothing, at every offset', 'SpoolCore.span, from, minus', 'exact', P.span,
    ({retained}) => retained.eq(0), o => o.omitted!.eq(0), 'omitted measured from the window'),
  D(33, pp, 'ended_stream_holds_nothing_back', 'an ended stream returns every byte', 'SpoolCore.kept', 'abstracted', P.kept,
    ({ended}) => ended, (o, {len}) => o.len!.eq(len), 'ended stream still holds back', {note: 'kept returns a prefix (List.take); the bytes as their length, the UTF-8 hold-back (a walk over the list) the runtime\'s answer'}),
  D(34, pp, 'long_poll_answers_at_its_ceiling', 'a long poll past its ceiling answers', 'SpoolCore.answer_now', 'exact', P.answerNow,
    ({expired}) => expired, o => o.out!.eq(1), 'ceiling ignored'),
  D(35, pp, 'session_child_is_cut_to_its_connection', 'a session child lives min(requested, left)', 'ServeCore.child_lifetime', 'exact', P.childLifetime,
    ({requested}) => requested.isSome, (o, {requested, left}) => requested.match({none: () => yes, some: (r: Env) => o.out!.eq(min(r, left))}), 'requested time not cut'),
  D(36, pp, 'session_child_defaults_to_its_connection', 'with no request a child lives min(left, left)', 'ServeCore.child_lifetime', 'exact', P.childLifetime,
    ({requested}) => requested.isNone, (o, {left}) => o.out!.eq(min(left, left)), 'no request means no lifetime'),
  D(37, pp, 'closed_queue_refuses_writes', 'ended input refuses every write', 'JobsCore.admit', 'exact', P.admit,
    ({closed}) => closed, o => o.out!.eq(0), 'closed queue admits'),
  D(38, pp, 'queue_admits_up_to_its_bound', 'a queue filled exactly to its bound is admitted', 'JobsCore.admit, Nat.ge_refl', 'exact', P.admit,
    ({closed, total, max}) => [closed.not(), total.eq(max)], o => o.out!.eq(1), 'bound is strict'),
  D(39, pp, 'past_bound_is_not_within', 'Nat.is_ge(max, max + 1 + over) is false (by induction in Bend)', 'Nat.is_ge', 'exact', P.isGe,
    ({a, b}) => b.atLeast(a.plus(1)), o => o.out!.eq(0), 'is_ge off by one', {note: 'for every max, over ⇔ for every a, b ≥ a + 1'}),
  D(40, pp, 'queue_refuses_past_its_bound', 'one byte past the bound is refused', 'JobsCore.admit', 'exact', P.admit,
    ({closed, total, max}) => [closed.not(), total.atLeast(max.plus(1))], o => o.out!.eq(0), 'bound is off by one'),
  {n: 41, bend: `${pp}: queue_keeps_arrival_order`, says: 'drained(push(push(empty, a), b)) = a ++ b', fns: 'JobsCore.push, drained, empty_queue', kind: 'k-step law', encoding: 'abstracted', how: 'automatic',
    note: 'a queue is a list of chunks (each write interned as a name); a 2-step law from an empty queue: position 0 holds the first write, 1 the second. String concatenation of the chunks is the encoding',
    case: () => machineCase(`${pp}: queue_keeps_arrival_order`, 'arrival order', P.inputQueue(), queueLaws(P.inputQueue()),
      [{name: 'push prepends', why: 'arrival order', rule: P.inputQueue('push prepends'), laws: queueLaws(P.inputQueue('push prepends')), steps: [queueSteps.order(P.inputQueue('push prepends'))]}], {steps: [queueSteps.order(P.inputQueue())], bound: 3})},
  {n: 42, bend: `${pp}: draining_empties_the_queue`, says: 'drained(emptied(q)) = ""', fns: 'JobsCore.drained, emptied', kind: 'step law', encoding: 'abstracted', how: 'automatic',
    note: 'a drain is a step of the queue machine: no chunk and no byte left after it',
    case: () => machineCase(`${pp}: draining_empties_the_queue`, 'draining', P.inputQueue(), queueLaws(P.inputQueue()),
      [{name: 'drain keeps the bytes', why: 'draining', rule: P.inputQueue('drain keeps the bytes'), laws: queueLaws(P.inputQueue('drain keeps the bytes')), steps: [queueSteps.drained(P.inputQueue('drain keeps the bytes'))]}], {steps: [queueSteps.drained(P.inputQueue())], bound: 3})},

  D(43, tp, 'denied_timeout_never_becomes_a_limit', 'checked(ms, False) is the fixed timeout error', 'TimeCore.checked', 'interned', P.checked,
    ({valid}) => valid.not(), o => eqAll(o, {ok: 0, code: 2, msg: P.TIMEOUT_MSG}), 'denied timeout passes'),
  D(44, tp, 'omitted_configuration_uses_default', 'config("", fallback, max) is Done{fallback}', 'TimeCore.config', 'abstracted', P.config,
    ({rawEmpty}) => rawEmpty, (o, {fallback}) => eqAll(o, {ok: 1, value: fallback}), 'empty config is parsed', {note: 'the raw string: empty or not; parse(raw, max) the runtime\'s answer'}),
  D(45, tp, 'elapsed_time_is_subtracted_not_renewed', 'remaining(Budget{start, duration}, now) = duration ∸ (now ∸ start)', 'TimeCore.remaining', 'exact', P.remaining,
    none, (o, {started, duration, now}) => o.out!.eq(duration.minus(now.minus(started))), 'elapsed time measured from zero'),
  D(46, tp, 'local_cap_is_applied_before_narrowing', 'cap(left, local) = U32.from_nat(min(left, local))', 'TimeCore.cap, U32.from_nat', 'exact', P.cap,
    none, (o, {left, local, narrow}) => o.out!.eq(narrow(min(left, local))), 'narrows before capping',
    {note: 'U32.from_nat is x mod 2^32 (modBy), known by its facts', witness: capWitness}),
  D(47, tp, 'duplicate_timeout_is_rejected', 'a second timeout is rejected', 'Cli.unique', 'interned', P.unique,
    ({previous}) => previous.isSome, o => eqAll(o, {ok: 0, code: 2, msg: P.DUP_MSG}), 'second timeout replaces the first'),
  D(48, tp, 'rejected_label_is_never_stored', 'a rejected label is the fixed error, never stored', 'Cli.label_allowed', 'interned', P.labelAllowed,
    ({ok}) => ok.not(), o => eqAll(o, {ok: 0, value: 0, code: 2, msg: P.LABEL_MSG}), 'rejected label is stored'),
  D(49, tp, 'serve_connection_may_last_a_day', 'Cli.max("serve") = 86400000', 'Cli.max', 'interned', P.cliMax,
    ({command}) => command.is('serve'), o => o.out!.eq(86400000), 'serve keeps the one-hour cap', {note: 'the command string as a oneOf of the four literals and "other"'}),

  D(50, dp, 'explicit_profile_wins', 'a nonempty explicit profile is chosen', 'DecisionProfiles.choose_profile, DecisionConfig.fallback', 'interned', P.chooseProfile,
    ({explicit}) => explicit.isSome, (o, {explicit}) => explicit.match({none: () => yes, some: (e: Env) => o.some!.eq(1).and(o.id!.eq(e))}), 'provider beats explicit',
    {note: 'strings as maybe(name): "" is none, so SCon{head, tail} is some'}),
  D(51, dp, 'explicit_provider_suppresses_profiles', 'an explicit provider without an explicit profile chooses none', 'DecisionProfiles.choose_profile', 'interned', P.chooseProfile,
    ({explicit, provider}) => [explicit.isNone, provider], o => o.some!.eq(0), 'provider ignored'),
  D(52, dp, 'ambient_profile_wins_over_default', 'an ambient profile beats the document default', 'DecisionProfiles.choose_profile', 'interned', P.chooseProfile,
    ({explicit, provider, ambient}) => [explicit.isNone, provider.not(), ambient.isSome], (o, {ambient}) => ambient.match({none: () => yes, some: (a: Env) => o.some!.eq(1).and(o.id!.eq(a))}), 'default beats ambient'),
  D(53, dp, 'absent_selectors_use_document_default', 'with no selectors the document default is chosen', 'DecisionProfiles.choose_profile', 'interned', P.chooseProfile,
    ({explicit, provider, ambient}) => [explicit.isNone, provider.not(), ambient.isNone],
    (o, {default: d}) => d.match({none: () => o.some!.eq(0), some: (x: Env) => o.some!.eq(1).and(o.id!.eq(x))}), 'absent selectors give none'),
  {n: 54, bend: `${dp}: explicit_provider_bypasses_document`, says: 'an explicit-provider request bypasses every document entry', fns: 'DecisionProfiles.apply_document, selector, choose_profile, selected, remove', kind: 'list/set', encoding: 'abstracted', how: 'automatic',
    note: 'the request as a map from key to value; stated for every request with a provider and no profile member (Bend: the one-member request); a list search and name checks are the runtime\'s answers',
    case: () => {
      const law = (r: any) => r.stepLaw('an explicit provider bypasses the document', (_b: Env, after: Env) => forall(k => after.ok.eq(1).and(after.chosen.eq(0), after.Out.at(k).eq(_b.Req.at(k)))),
        ({reqObject, Req}: Env) => reqObject.and(Req.at(P.KEY.profile).eq(0), Req.at(P.KEY.provider).atLeast(1)))
      return machineCase(`${dp}: explicit_provider_bypasses_document`, 'bypass', P.applyDocument(), [],
        [{name: 'explicit provider still applies the profile', why: 'bypass', rule: P.applyDocument('explicit provider still applies the profile'), laws: [], steps: [law(P.applyDocument('explicit provider still applies the profile'))]}], {steps: [law(P.applyDocument())], bound: 3, depth: 1})
    }},
  {n: 55, bend: `${dp}: explicit_provider_discards_ambient_target`, says: 'with an explicit provider, changing both ambient values changes nothing', fns: 'DecisionConfig.configure_explicit', kind: 'relate', encoding: 'abstracted', how: 'automatic',
    note: 'noninterference, a decision about two calls (relate): with an explicit provider, any two ambient pairs give configure the same arguments (configure itself, string validation, is a function of them)',
    case: () => {
      const name = `${dp}: explicit_provider_discards_ambient_target`
      const law = (bug?: P.ProfileBug) => P.configureExplicit(bug).relate(name, (a, b) => [a.explicit, b.explicit], (oa, ob) => oa.model.eq(ob.model).and(oa.endpoint.eq(ob.endpoint)))
      return decisionCase(name, 'the ambient target is discarded', [law()], [{name: 'explicit provider keeps the ambient target', why: 'the ambient target is discarded', decision: law('explicit provider keeps the ambient target')}])
    }},
  {n: 56, bend: `${dp}: provider_options_replaced_whole`, says: 'merging {providerOptions: new} over {providerOptions: old} gives {providerOptions: new}', fns: 'DecisionProfiles.merge, missing', kind: 'list/set', encoding: 'abstracted', how: 'automatic',
    note: 'objects as maps from key to value id; stated at every key where the base is absent, and at providerOptions, whatever else the objects hold', witness: mergeWitness('whole'),
    case: () => {
      const law = (r: any) => r.stepLaw('providerOptions replaced whole', ({Base, Over}: Env, after: Env) => forall(k => after.ok.eq(1).and(k.eq(P.KEY.providerOptions).or(Base.at(k).eq(0)).implies(after.Out.at(k).eq(Over.at(k))))),
        ({baseObject, overObject, Over}: Env) => baseObject.and(overObject, Over.at(P.KEY.providerOptions).atLeast(1)))
      return machineCase(`${dp}: provider_options_replaced_whole`, 'whole', P.merge(), [], [{name: 'providerOptions merged recursively', why: 'whole', rule: P.merge('providerOptions merged recursively'), laws: [], steps: [law(P.merge('providerOptions merged recursively'))]}], {steps: [law(P.merge())], bound: 4, depth: 1})
    }},
  {n: 57, bend: `${dp}: shadowed_provider_options_are_irrelevant`, says: 'the shadowed providerOptions subtree does not affect the merge, with any other fields', fns: 'DecisionProfiles.merge, missing', kind: 'list/set', encoding: 'abstracted', how: 'automatic',
    note: 'two merges side by side (Base, BaseB); at every key where the bases agree, and at providerOptions, the merges agree. Member order (equal on both sides, a function of the keys) is left to the encoding', witness: mergeWitness('irrelevant'),
    case: () => {
      const law = (r: any) => r.stepLaw('shadowed providerOptions are irrelevant', ({Base, BaseB}: Env, after: Env) => forall(k => k.eq(P.KEY.providerOptions).or(Base.at(k).eq(BaseB.at(k))).implies(after.Out.at(k).eq(after.OutB.at(k)))),
        ({Over}: Env) => Over.at(P.KEY.providerOptions).atLeast(1))
      return machineCase(`${dp}: shadowed_provider_options_are_irrelevant`, 'irrelevant', P.merge(), [], [{name: 'providerOptions merged recursively', why: 'irrelevant', rule: P.merge('providerOptions merged recursively'), laws: [], steps: [law(P.merge('providerOptions merged recursively'))]}], {steps: [law(P.merge())], bound: 4, depth: 1})
    }},
  D(58, dp, 'canonical_idempotent_branch', 'given canonical(p) = pick(matched, "vercel", p) (twice), canonical is idempotent at p', 'DecisionConfig.canonical', 'interned', P.canonical,
    ({provider, matched}, o) => o.once!.eq(provider).and(matched.not()).or(o.once!.eq(P.NAME.vercel).and(matched)), o => o.twice!.eq(o.once!), 'canonical swaps the two names',
    {note: 'a helper of the Bend proof (a case split on String.eq); here one decision'}),
  D(59, dp, 'canonical_provider_is_idempotent', 'canonical(canonical(p)) = canonical(p)', 'DecisionConfig.canonical', 'interned', P.canonical,
    none, o => o.twice!.eq(o.once!), 'canonical swaps the two names', {note: '"vercel-ai-gateway" and "vercel" interned at fixed distinct names'}),
]

// ===================================================================================================================
// Extras: what gdp-wired states over runs that the Bend proofs do not
// ===================================================================================================================
const budgetLaws = (r: any) => [
  r.law('evaluations used and left never pass the cap', ({used, remaining, cap}: Env) => used.plus(remaining).atMost(cap)),
  r.law('a call in flight was reserved under the token limit', ({inflight, tokens, limit}: Env) => inflight.atMost(1).and(inflight.eq(1).implies(tokens.lt(limit)))),
  r.law('after an overshoot: no evaluation left, tokens past the limit', ({off, remaining, tokens, limit}: Env) => off.eq(1).implies(remaining.eq(0).and(limit.lt(tokens)))),
]
const budgetSteps = (r: any) => [
  r.stepLaw('no call is granted after an overshoot', ({granted}: Env) => granted.not(), ({off}: Env) => off.eq(1)),
  r.stepLaw('the spent-token count never goes down', ({tokens}: Env, after: Env) => tokens.atMost(after.tokens)),
]
const channelLaws = (r: any) => [
  r.law('never more than total_max lines emitted', ({emitted, total}: Env) => emitted.atMost(total)),
  r.law('fewer pending lines than a batch', ({pending, batch}: Env) => pending.lt(batch)),
  r.law('at most one record per push', ({outs}: Env) => outs.atMost(1)),
]
const channelSteps = (r: any) => [
  r.stepLaw('the line just emitted is never emitted again next', (b: Env, a: Env) => sameChannel(b, a), ({kept, previous}: Env) => kept.eq(previous)),
  r.stepLaw('batches never go down', ({batches}: Env, a: Env) => batches.atMost(a.batches)),
]
const followLaws = (r: any) => [
  r.law('nothing past the end', ({Printed}: Env) => Printed.within()),
  r.law('printed sequence numbers strictly increase (none printed twice)', ({Printed}: Env) => Printed.increasing()),
  r.law('every printed number is at most the cursor', ({Printed, cursor}: Env) => forall(k => k.lt(Printed.len).implies(Printed.at(k).atMost(cursor)))),
]
const followSteps = (r: any) => [
  r.stepLaw('an event at or before the cursor prints nothing, over any run', ({cursor, Printed_len}: Env, a: Env) => a.cursor.eq(cursor).and(a.outs.eq(0), a.Printed_len.eq(Printed_len)), ({unseen}: Env) => unseen.not()),
]
const queueAll = (r: any) => [...queueLaws(r), r.law('the queue never holds more than its bound', ({total, max}: Env) => total.atMost(max)), r.law('closed is a bit', ({closed}: Env) => closed.atMost(1))]
const queueAllSteps = (r: any) => [
  r.stepLaw('ended input stays ended', ({closed}: Env, a: Env) => closed.atMost(a.closed)),
  r.stepLaw('no write is admitted once input has ended', ({admitted}: Env) => admitted.not(), ({closed}: Env) => closed.eq(1)),
  r.stepLaw('an admitted write lands after every chunk before it', ({chunk, Q}: Env, a: Env) => forall(k => k.lt(Q.len).implies(a.Q.at(k).eq(Q.at(k))).and(a.Q.at(Q.len).eq(chunk), a.Q_len.eq(Q.len.plus(1)))), ({admitted}: Env) => admitted),
  queueSteps.order(r), queueSteps.drained(r),
]
const readerLaws = (r: any) => [
  r.law('every byte below the reader\'s offset was delivered or disclosed as lost', ({offset, delivered, lost}: Env) => offset.eq(delivered.plus(lost))),
  r.law('the reader never passes the bytes written', ({offset, count}: Env) => offset.atMost(count)),
]
const clockLaws = (r: any) => [
  r.law('the clock is at or past the start', ({last, started}: Env) => started.atMost(last)),
  r.law('what is left is the duration less the time elapsed', ({left, duration, last, started}: Env) => left.eq(duration.minus(last.minus(started)))),
]
const clockSteps = (r: any) => [r.stepLaw('time left never grows: an elapsed budget is never renewed', ({left}: Env, a: Env) => a.left.atMost(left))]

function M(name: string, says: string, fns: string, kind: Kind, mk: (bug?: any) => any, laws: (r: any) => any[], steps: (r: any) => any[], bugs: string[], opts: {bound?: number, depth?: number, how?: Entry['how'], note?: string, encoding?: Entry['encoding']} = {}): Entry {
  return {n: 0, bend: name, says, fns, kind, encoding: opts.encoding ?? 'exact', how: opts.how ?? 'automatic', ...(opts.note ? {note: opts.note} : {}),
    case: () => machineCase(name, says, mk(), laws(mk()), bugs.map(bug => ({name: bug, why: says, rule: mk(bug), laws: laws(mk(bug)), steps: steps(mk(bug))})), {steps: steps(mk()), ...(opts.bound ? {bound: opts.bound} : {}), ...(opts.depth ? {depth: opts.depth} : {})})}
}

export const extras: Entry[] = [
  D(0, '', 'reservation consumes one, at any spent tokens below the limit', 'the general form of reservation_consumes_one (deliberately not stated in Bend)', 'Core.reserve', 'exact', P.reserve,
    ({remaining, tokens, limit}) => [remaining.atLeast(1), tokens.lt(limit)], (o, {remaining, used, tokens, limit}) => eqAll(o, {some: 1, remaining: remaining.minus(1), evaluations: used.plus(1), tokens, limit}), 'reserve counts no call'),
  D(0, '', 'any spent budget blocks a reservation', 'the general form of zero_token_budget_blocks', 'Core.reserve', 'exact', P.reserve,
    ({tokens, limit}) => tokens.atLeast(limit), o => o.some!.eq(0), 'reserve ignores the token limit'),
  M('Jev client budget over a run', 'reserve before a call, report after it: evaluations never pass the cap, nothing is granted after an overshoot, spent tokens never go down',
    'Core.reserve, JevCore.account, add_usage', 'step law', P.clientBudget, budgetLaws, budgetSteps, ['reports need no reservation', 'overshoot leaves calls enabled', 'reservation refunds remaining'],
    {how: 'added invariant', note: 'needs "a call in flight was reserved under the token limit" and "after an overshoot ..." as laws; without the reserve-before-report protocol the saturating add_usage lowers the spent count'}),
  M('monitor channel over a run', 'over any pushes: at most total_max lines emitted (the aggregate bound docs/safe-bend.md lists as missing), fewer pending than a batch, the previous line never repeated next',
    'MonitorCore.push', 'step law', P.channel, channelLaws, channelSteps, ['full channel still emits', 'dedup forgotten', 'flush keeps the count'], {bound: 3, depth: 14, encoding: 'abstracted'}),
  M('follow over a run', 'the printed sequence numbers strictly increase: no event is printed twice, at any distance', 'JobsCore.sequenced, fresh', 'list/set', P.follow, followLaws, followSteps,
    ['prints an event equal to the cursor', 'cursor not advanced'], {bound: 3, how: 'added invariant', note: 'with "every printed number is at most the cursor" as a law'}),
  M('interactive input queue over a run', 'the queue never holds more than its bound, ended input stays ended and admits nothing, writes keep arrival order, a drain empties it',
    'JobsCore.admit, push, seal, drained, emptied (as Host applies them)', 'list/set', P.inputQueue, queueAll, queueAllSteps, ['admit ignores closed', 'admit skips the bound', 'drain reopens', 'push prepends', 'drain keeps the bytes'], {bound: 3, encoding: 'abstracted'}),
  D(0, '', 'a read-only verb never adopts a home it did not create', 'StoreCore.decide whole: whatever the marker says', 'StoreCore.decide, marked, missing, parsed', 'abstracted', P.storeDecide,
    ({mutating, lead}) => [mutating.not(), lead.is('plus').not()], o => o.out!.ne(1), 'reader adopts'),
  D(0, '', 'a newer home is refused whatever the verb and whoever created it', 'StoreCore.decide whole', 'StoreCore.decide, versioned', 'abstracted', P.storeDecide,
    ({lead, markerEmpty, parsed}) => [lead.is('empty').not(), markerEmpty.not(), parsed.match({none: () => yes.not(), some: (n: Env) => n.atLeast(2)})], o => o.out!.eq(2).and(o.msg!.eq(2)), 'newer store adopted'),
  D(0, '', 'a read starts in the window, at or past its offset, and returns at most max bytes, none past count', 'SpoolCore.span in general', 'SpoolCore.span', 'exact', P.span,
    none, (o, {retained, offset, count, max}) => o.start!.atLeast(retained).and(o.start!.atLeast(offset), o.length!.atMost(max), o.start!.atMost(count).implies(o.start!.plus(o.length!).atMost(count)), o.omitted!.eq(retained.minus(offset))), 'omitted measured from the window'),
  M('spool reader over a run', 'every byte below the reader\'s offset was delivered or disclosed as lost; the reader never passes what was written', 'SpoolCore.span, oldest (Spool.bend\'s read loop)', 'law', P.spoolReader, readerLaws, () => [], ['loss not disclosed', 'reader skips ahead'], {bound: 4, depth: 14}),
  D(0, '', 'a child with no request lives exactly what is left (not just min(left, left))', 'the form Bend could not reduce without a lemma', 'ServeCore.child_lifetime', 'exact', P.childLifetime,
    ({requested}) => requested.isNone, (o, {left}) => o.out!.eq(left), 'no request means no lifetime'),
  D(0, '', 'a child never outlives its connection', 'child_lifetime(r, left) ≤ left for every r', 'ServeCore.child_lifetime', 'exact', P.childLifetime,
    none, (o, {left}) => o.out!.atMost(left), 'requested time not cut'),
  D(0, '', 'capping loses nothing to narrowing', 'cap(left, local) = min(left, local): U32 narrowing never bites', 'TimeCore.cap, U32.from_nat', 'exact', P.capWithFact,
    none, (o, {left, local}) => o.out!.eq(min(left, local)), 'narrows before capping',
    {how: 'added fact', note: 'needs the fact x < 2^32 ⇒ x mod 2^32 = x (Lean: Nat.mod_eq_of_lt), which the decision assumes where it reads the function', witness: capWitness}),
  M('scope budget over time', 'as the clock advances, the time left never grows: an elapsed budget is never renewed', 'TimeCore.remaining (Scope.bend samples it)', 'step law', P.clock, clockLaws, clockSteps, ['renewed at each tick', 'clock may go back'],
    {how: 'added invariant', note: 'with "what is left is the duration less the time elapsed" as a law'}),
]
