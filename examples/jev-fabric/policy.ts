// jev-fabric's policy core (https://github.com/fabric-runtime/jev-fabric: native/*Core.bend, Cli.bend, the strict-JSON
// writer's fuel guard), ported to gdp-wired's builders, with the deliberately broken variants as `bug` arguments.
//
// Encoding:
//   - Nat is a natural, U32 a natural at most 2^32 − 1 (upTo), Bool a bit, a Bend enum a oneOf, Maybe a maybe.
//   - A String the law treats as a value (a label, a key, a URL, a profile name) is a name interned to a natural; a
//     possibly-empty string is maybe(name), "" being none. Interning is assumed injective (String.eq ⇔ equal ids).
//   - A string or list *computation* the law does not depend on (trim/contains, JSON parsing, UTF-8 hold-back, HTTP
//     status parsing) is an input the runtime computes, as a history's query is in gdp-wired: the rule takes its answer.
//   - A fixed error message is its index among the function's messages; a constructor's fields are the result's fields
//     (a Bool or a constructor tag as 0 or 1, as the Bend value's tag).
//   - A JSON object is a map from interned key to (value id + 1), 0 meaning absent (keys unique, as strict JSON reads them).
// A pure Bend function is a `fun`: its laws are decisions about the terms it returns, and `run` is the same terms compiled.
import {type Cond, type TermLike, bool, count, forall, fun, maybe, max, min, modBy, nat, oneOf, rule, upTo, when, yes} from '../../core/dsl.ts'

/* eslint-disable @typescript-eslint/no-explicit-any */
type Env = any
export const U32_MAX = 4294967295
export const u32 = upTo(U32_MAX)
const bit = (c: Cond) => count(c)

// A Maybe's value, 0 when missing (the encoding leaves it free; an output reads it only where present).
const valueOf = (m: Env): TermLike => m.match({none: () => 0, some: (x: TermLike) => x})

// ===================================================================================================================
// Core.bend
// ===================================================================================================================
export const STATES = ['Running', 'Completed', 'Attention', 'Failed', 'Cancelled', 'TimedOut'] as const
export const RECEIPTS = ['Executed', 'Stale', 'Blocked', 'Unknown'] as const
export const NEXTS = ['Verify', 'Reobserve', 'Escalate', 'Inspect'] as const
const S = (s: (typeof STATES)[number]) => STATES.indexOf(s)
const N = (s: (typeof NEXTS)[number]) => NEXTS.indexOf(s)

export type CoreBug = 'reserve_if ignores allowed' | 'reserve lets an empty budget through' | 'reserve counts no call' | 'reserve ignores the token limit'
  | 'account drops the report' | 'settle reopens Failed' | 'settle reopens TimedOut' | 'settle reopens Cancelled' | 'settle reopens Completed'
  | 'after reobserves Unknown' | 'after escalates Executed'
// Maybe<Budget>: some, then the budget's fields (0 when none).
const budgetOut = (allowed: Cond, remaining: TermLike, used: TermLike, tokens: TermLike, limit: TermLike) => ({
  some: bit(allowed), remaining: when(allowed, remaining, 0), evaluations: when(allowed, used, 0), tokens: when(allowed, tokens, 0), limit: when(allowed, limit, 0),
})
const reserveIfTerm = (bug?: CoreBug) => ({remaining, used, tokens, limit, allowed}: Env) =>
  budgetOut(bug === 'reserve_if ignores allowed' ? yes : allowed, remaining, used.plus(1), tokens, limit)
export const reserveIf = (bug?: CoreBug) => fun('Core.reserve_if').inputs({remaining: nat, used: nat, tokens: nat, limit: nat, allowed: bool}).returns(reserveIfTerm(bug))
export const reserveTerm = (bug?: CoreBug) => ({remaining, used, tokens, limit}: Env) => {
  const allowed = bug === 'reserve ignores the token limit' ? tokens.atMost(limit) : tokens.lt(limit)
  const has = bug === 'reserve lets an empty budget through' ? yes : remaining.atLeast(1)
  return budgetOut(has.and(allowed), remaining.minus(1), bug === 'reserve counts no call' ? used : used.plus(1), tokens, limit)
}
export const reserve = (bug?: CoreBug) => fun('Core.reserve').inputs({remaining: nat, used: nat, tokens: nat, limit: nat}).returns(reserveTerm(bug))
export const account = (bug?: CoreBug) => fun('Core.account').inputs({remaining: nat, used: nat, tokens: nat, limit: nat, reported: nat})
  .returns(({remaining, used, tokens, limit, reported}: Env) => ({remaining, evaluations: used, tokens: bug === 'account drops the report' ? tokens : tokens.plus(reported), limit}))
export const settle = (bug?: CoreBug) => fun('Core.settle').inputs({state: oneOf(...STATES), result: oneOf(...STATES)}).returns(({state, result}: Env) => {
  const reopened = bug?.startsWith('settle reopens ') ? state.is(bug.slice('settle reopens '.length)) : undefined
  const open = reopened ? state.is('Running').or(reopened) : state.is('Running')
  return {out: when(open, result.n, state.n)}
})
export const after = (bug?: CoreBug) => fun('Core.after').inputs({receipt: oneOf(...RECEIPTS)}).returns(({receipt}: Env) => ({out: receipt.match({
  Executed: () => N(bug === 'after escalates Executed' ? 'Escalate' : 'Verify'), Stale: () => N('Reobserve'), Blocked: () => N('Escalate'), Unknown: () => N(bug === 'after reobserves Unknown' ? 'Reobserve' : 'Inspect'),
})}))
export {S as stateIndex, N as nextIndex}

// The Jev client's budget over a run (Core.reserve before a call, JevCore.account/add_usage after it), as Jev.bend
// threads it: a report follows only a reservation granted earlier (`inflight`). Not stated in Bend.
export type BudgetBug = 'reports need no reservation' | 'overshoot leaves calls enabled' | 'reservation refunds remaining'
export const clientBudget = (bug?: BudgetBug) => rule('Jev client budget')
  .params({cap: nat, limit: nat})
  .inputs({op: oneOf('reserve', 'report'), input: nat, output: nat})
  .state({remaining: ({cap}) => cap, used: 0, tokens: 0, inflight: 0, off: 0, refused: 0})
  .flags(({op, remaining, tokens, limit, inflight}) => ({
    granted: op.is('reserve').and(remaining.atLeast(1), tokens.lt(limit), inflight.eq(0)),
    reporting: op.is('report').and(bug === 'reports need no reservation' ? yes : inflight.eq(1)),
  }))
  .flags(({reporting, input, output, limit}) => ({oversized: reporting.and(input.gt(limit).or(output.gt(limit)))}))
  .step(({granted, reporting, oversized, op, remaining, used, tokens, limit, input, output, off, inflight}) => ({
    remaining: when(granted, bug === 'reservation refunds remaining' ? remaining : remaining.minus(1), when(oversized, bug === 'overshoot leaves calls enabled' ? remaining : 0, remaining)),
    used: when(granted, used.plus(1), used),
    tokens: when(oversized, limit.plus(1), when(reporting, tokens.plus(input).plus(output), tokens)),
    inflight: when(granted, 1, when(reporting, 0, inflight)),
    off: when(oversized, 1, off),
    refused: bit(op.is('reserve').and(granted.not())),
  }))

// ===================================================================================================================
// TimeCore.bend and Cli.bend
// ===================================================================================================================
export const TIMEOUT_MSG = 1 // "timeout must be an integer within the operation limit"
export type TimeBug = 'denied timeout passes' | 'empty config is parsed' | 'elapsed time measured from zero' | 'narrows before capping'
  | 'second timeout replaces the first' | 'rejected label is stored' | 'serve keeps the one-hour cap'
// Result<(U32, String), U32>: ok, value (when ok), code and message index (when not).
const result = (ok: Cond, value: TermLike, code: number, msg: number) => ({ok: bit(ok), value: when(ok, value, 0), code: when(ok, 0, code), msg: when(ok, 0, msg)})
export const checked = (bug?: TimeBug) => fun('TimeCore.checked').inputs({ms: u32, valid: bool})
  .returns(({ms, valid}: Env) => result(bug === 'denied timeout passes' ? yes : valid, ms, 2, TIMEOUT_MSG))
// config(raw, fallback, max): raw "" or not; parse(raw, max), a string parse, is the runtime's answer (parsedOk, parsed).
export const config = (bug?: TimeBug) => fun('TimeCore.config').inputs({rawEmpty: bool, parsedOk: bool, parsed: u32, fallback: u32, max: u32})
  .returns(({rawEmpty, parsedOk, parsed, fallback}: Env) => {
    const empty = bug === 'empty config is parsed' ? rawEmpty.and(rawEmpty.not()) : rawEmpty
    return result(empty.or(parsedOk), when(empty, fallback, parsed), 2, TIMEOUT_MSG)
  })
export const remaining = (bug?: TimeBug) => fun('TimeCore.remaining').inputs({started: nat, duration: nat, now: nat})
  .returns(({started, duration, now}: Env) => ({out: duration.minus(bug === 'elapsed time measured from zero' ? now : now.minus(started))}))
// U32.from_nat wraps (it is U32.inc applied n times): x mod 2^32, a function known by its facts.
export const U32_RANGE = 4294967296
const capTerm = (bug?: TimeBug) => ({left, local, narrow}: Env) => ({out: bug === 'narrows before capping' ? min(narrow(left), local) : narrow(min(left, local))})
export const cap = (bug?: TimeBug) => fun('TimeCore.cap').inputs({left: nat, local: u32}).fns({narrow: modBy(U32_RANGE)}).returns(capTerm(bug))
// The fact Lean's omega proves of x % 2^32 (Nat.mod_eq_of_lt), added to the function so the stronger law goes through.
export const capWithFact = (bug?: TimeBug) => fun('TimeCore.cap').inputs({left: nat, local: u32}).fns({narrow: modBy(U32_RANGE)})
  .facts(({narrow}) => ({'x < 2^32 ⇒ x mod 2^32 = x': forall(x => x.lt(U32_RANGE).implies(narrow(x).eq(x)))}))
  .returns(capTerm(bug))
export const DUP_MSG = 3, LABEL_MSG = 4
export const unique = (bug?: TimeBug) => fun('Cli.unique').inputs({previous: maybe(u32), value: u32})
  .returns(({previous, value}: Env) => result(bug === 'second timeout replaces the first' ? yes : previous.isNone, value, 2, DUP_MSG))
export const labelAllowed = (bug?: TimeBug) => fun('Cli.label_allowed').inputs({text: nat, ok: bool})
  .returns(({text, ok}: Env) => result(bug === 'rejected label is stored' ? yes : ok, text, 2, LABEL_MSG))
export const COMMANDS = ['watch', 'events', 'start', 'serve', 'other'] as const
export const cliMax = (bug?: TimeBug) => fun('Cli.max').inputs({command: oneOf(...COMMANDS)}).returns(({command}: Env) => ({out: command.match({
  watch: () => 300000, events: () => 300000, start: () => 86400000, serve: () => (bug === 'serve keeps the one-hour cap' ? 3600000 : 86400000), other: () => 3600000,
})}))

// A scope's budget as the clock advances (Time.remaining read at each tick, the clock never going back). Not in Bend.
export const clock = (bug?: 'renewed at each tick' | 'clock may go back') => rule('scope budget over time')
  .params({started: nat, duration: nat})
  .inputs({now: nat})
  .state({last: ({started}) => started, left: ({duration}) => duration})
  .assume(({now, last}) => (bug === 'clock may go back' ? yes : now.atLeast(last)))
  .step(({now, started, duration}) => ({last: now, left: bug === 'renewed at each tick' ? duration.minus(now.minus(started)).plus(1) : duration.minus(now.minus(started))}))

// ===================================================================================================================
// MonitorCore.bend
// ===================================================================================================================
export const REASONS = ['finished', 'output-limit', 'deadline'] as const
const R = (s: (typeof REASONS)[number]) => REASONS.indexOf(s)
export const TOTAL_MAX = 1024
export type MonitorBug = 'limit checked before the receipt' | 'output limit only stops at the deadline' | 'deadline keeps polling' | 'disabled filter still matches'
// Decision: stop (0 Poll, 1 Stop), reason index, terminal bit.
const decision = (stop: TermLike, reason: TermLike, terminal: TermLike) => ({stop, reason, terminal})
const deadlineDecision = (bug?: MonitorBug) => (expired: Cond) =>
  decision(bit(bug === 'deadline keeps polling' ? expired.and(expired.not()) : expired), when(expired, R('deadline'), 0), 0)
const limitDecision = (bug?: MonitorBug) => (over: Cond, elapsed: Env, duration: Env) => {
  const dl = deadlineDecision(bug)(elapsed.atLeast(duration))
  if (bug === 'output limit only stops at the deadline') return dl
  return decision(when(over, 1, dl.stop), when(over, R('output-limit'), dl.reason), when(over, 0, dl.terminal))
}
const terminalDecision = (bug?: MonitorBug) => ({terminal, lines, elapsed, duration}: Env) => {
  const over = lines.atLeast(TOTAL_MAX), lim = limitDecision(bug)(over, elapsed, duration)
  if (bug === 'limit checked before the receipt') return decision(when(over, 1, when(terminal, 1, lim.stop)), when(over, R('output-limit'), when(terminal, R('finished'), lim.reason)), when(over, 0, when(terminal, 1, lim.terminal)))
  return decision(when(terminal, 1, lim.stop), when(terminal, R('finished'), lim.reason), when(terminal, 1, lim.terminal))
}
export const monitorTerminal = (bug?: MonitorBug) => fun('MonitorCore.terminal_decision').inputs({terminal: bool, lines: nat, elapsed: nat, duration: nat}).returns(terminalDecision(bug))
export const monitorLimit = (bug?: MonitorBug) => fun('MonitorCore.limit_decision').inputs({over: bool, elapsed: nat, duration: nat})
  .returns(({over, elapsed, duration}: Env) => limitDecision(bug)(over, elapsed, duration))
export const monitorDeadline = (bug?: MonitorBug) => fun('MonitorCore.deadline_decision').inputs({expired: bool}).returns(({expired}: Env) => deadlineDecision(bug)(expired))
// limited_match(text, literal, previous, allowed): Core.monitor(text, literal, previous) is string work (trim, contains,
// equality); the runtime answers it (hit) and interns the trimmed line (kept).
export const limitedMatch = (bug?: MonitorBug) => fun('MonitorCore.limited_match').inputs({allowed: bool, hit: bool, kept: nat})
  .returns(({allowed, hit, kept}: Env) => { const some = (bug === 'disabled filter still matches' ? yes : allowed).and(hit); return {some: bit(some), value: when(some, kept, 0)} })

// One channel stepped by MonitorCore.push. The line's string tests (nonempty, contains the literal) are the runtime's
// answer (textOk); the trimmed line is interned (kept), so Core.monitor's "not the previous line" is kept ≠ previous.
// total is total_max() (1024 in jev-fabric), batch the push's batch size; outs counts the records the push emits.
export type ChannelBug = 'full channel still emits' | 'dedup forgotten' | 'flush keeps the count'
export const channel = (bug?: ChannelBug) => rule('MonitorCore.push channel')
  .params({total: nat, batch: nat})
  .inputs({textOk: bool, kept: nat, clipped: bool, sequence: nat})
  .pre(({batch}) => batch.atLeast(1)) // batch_max() = 32 at every call
  .assume(({sequence}) => sequence.atMost(U32_MAX))
  .state({emitted: 0, batches: 0, pending: 0, omitted: 0, clips: 0, from: 0, to: 0, previous: 0, outs: 0})
  .flags(({textOk, kept, previous, emitted, total, pending, batch}) => ({
    hit: (bug === 'full channel still emits' ? yes : emitted.lt(total)).and(textOk, bug === 'dedup forgotten' ? yes : kept.ne(previous)),
    full: pending.plus(1).atLeast(batch),
  }))
  .step(({hit, full, kept, clipped, sequence, emitted, batches, pending, omitted, clips, from, to, previous}) => ({
    emitted: when(hit, emitted.plus(1), emitted),
    batches: when(hit.and(full), batches.plus(1), batches),
    pending: when(hit, when(full, bug === 'flush keeps the count' ? pending.plus(1) : 0, pending.plus(1)), pending),
    omitted: when(hit.and(full), 0, omitted),
    clips: when(hit, when(full, 0, clips.plus(clipped.n)), clips),
    from: when(hit, when(full, 0, when(from.eq(0), sequence, from)), from),
    to: when(hit, when(full, 0, sequence), to),
    previous: when(hit, kept, previous),
    outs: bit(hit.and(full)),
  }))

// ===================================================================================================================
// The strict-JSON writer's fuel guard (vendor/strict-json/json.bend, JSON.encode.go)
// ===================================================================================================================
// write_with_fuel(fuel, v) = encode.go(fuel, [v], []): no jobs left → Done; fuel 0 → Fail(22, "JSON encoding work
// limit"); otherwise one job is expanded (string work: the runtime's answer, stepOk) and the loop goes on.
export const ENCODE_MSG = 1
export const writeWithFuel = (bug?: 'zero fuel still writes') => fun('JSON.write_with_fuel').inputs({fuel: nat, value: nat, rest: bool})
  .returns(({fuel, value, rest}: Env) => result(bug === 'zero fuel still writes' ? rest : fuel.atLeast(1).and(rest), value, 22, ENCODE_MSG))
// rest: the answer of the remaining loop from fuel − 1 (a recursive string computation the law does not depend on).

// ===================================================================================================================
// HttpCore.bend, CredentialCore.bend, JevCore.bend
// ===================================================================================================================
export type IoBug = 'rejected config still planned' | 'error carries the key' | 'failed transport still parsed' | 'overshoot leaves calls enabled' | 'invalid reply is accounted'
export const HTTP_MSG = 1, CRED_MSG = 1
export const requestAllowed = (bug?: IoBug) => fun('HttpCore.request_allowed').inputs({url: nat, key: nat, body: nat, timeout: u32, allowed: bool})
  .returns(({url, key, body, timeout, allowed}: Env) => {
    const ok = bug === 'rejected config still planned' ? yes : allowed
    return {...result(ok, url, 1, HTTP_MSG), key: when(ok, key, 0), body: when(ok, body, 0), timeout: when(ok, timeout, 0)}
  })
export const credentialChecked = (bug?: IoBug) => fun('CredentialCore.checked').inputs({key: nat, valid: bool})
  .returns(({key, valid}: Env) => ({...result(valid, key, 1, CRED_MSG), exposed: bug === 'error carries the key' ? key : when(valid, key, 0)}))
export const TRANSPORT_MSG = 'Jev transport failed, was interrupted, or exceeded its output bound'
// capture_ok(bytes, ok): ok → status(reverse(bytes)), a byte parse (the runtime's answer: statusMsg, 0 when it parsed,
// else its message interned; message 1 is the transport's own, which no status parse returns).
export const captureOk = (bug?: IoBug) => fun('HttpCore.capture_ok').inputs({ok: bool, statusMsg: nat, body: nat}).assume(({statusMsg}: Env) => statusMsg.ne(1))
  .returns(({ok, statusMsg, body}: Env) => {
    const parsed = statusMsg.eq(0), through = bug === 'failed transport still parsed' ? parsed : ok.and(parsed)
    return {ok: bit(through), value: when(through, body, 0), code: when(through, 0, 1), msg: when(through, 0, when(bug === 'failed transport still parsed' ? parsed.not() : ok, statusMsg, 1))}
  })
export const JEV_MSGS = ['none', 'Jev reported-token budget exceeded; final request may still be billed', 'Invalid typed Jev response', 'Invalid Jev usage'] as const
// add_usage(settings, Budget{remaining, used, spent, limit}, key, response, input, output, oversized) -> (Client, Evaluation)
const addUsageTerm = (bug?: IoBug) => ({settings, remaining, used, spent, limit, key, response, input, output, oversized}: Env) => {
  const next = spent.plus(input).plus(output), within = next.atMost(limit), ok = oversized.not().and(within)
  return {
    settings, key, remaining: when(oversized, bug === 'overshoot leaves calls enabled' ? remaining : 0, remaining), used,
    tokens: when(oversized, limit.plus(1), next), limit, ok: bit(ok), value: when(ok, response, 0), msg: when(ok, 0, 1),
  }
}
export const addUsage = (bug?: IoBug) => fun('JevCore.add_usage').inputs({settings: nat, remaining: nat, used: nat, spent: nat, limit: nat, key: nat, response: nat, input: nat, output: nat, oversized: bool})
  .returns(addUsageTerm(bug))
// response_ready(settings, budget, key, response): Fail → the client unchanged and "Invalid typed Jev response";
// Done{reply} → usage_ready on the reply's usage (a parse: the runtime's answer usageOk, input, output) → account,
// which marks a report above the whole limit oversized → add_usage.
export const responseReady = (bug?: IoBug) => fun('JevCore.response_ready').inputs({settings: nat, remaining: nat, used: nat, spent: nat, limit: nat, key: nat, responseOk: bool, response: nat, usageOk: bool, input: nat, output: nat})
  .returns((env: Env) => {
    const {settings, remaining, used, spent, limit, key, responseOk, usageOk, input, output} = env
    const counted = addUsageTerm()({...env, oversized: input.gt(limit).or(output.gt(limit))})
    const pick = (field: string, onFail: TermLike, onUsage: TermLike) => when(responseOk.not(), onFail, when(usageOk.not(), onUsage, counted[field as keyof typeof counted]))
    const failSpent = bug === 'invalid reply is accounted' ? spent.plus(input).plus(output) : spent
    return {
      settings, key, remaining: pick('remaining', remaining, remaining), used, tokens: pick('tokens', failSpent, spent), limit,
      ok: pick('ok', 0, 0), value: pick('value', 0, 0), msg: pick('msg', 2, 3),
    }
  })

// ===================================================================================================================
// JobsCore.bend
// ===================================================================================================================
export const FOLLOW = ['Continue', 'Finished', 'Expired'] as const
export type JobsBug = 'expiry beats a receipt' | 'expiry ignored' | 'a seen event is printed again' | 'closed queue admits' | 'bound is strict' | 'bound is off by one' | 'is_ge off by one'
export const followDecision = (bug?: JobsBug) => fun('JobsCore.follow_decision').inputs({finished: bool, expired: bool}).returns(({finished, expired}: Env) => ({
  out: bug === 'expiry beats a receipt' ? when(expired, 2, when(finished, 1, 0)) : when(finished, 1, when(bug === 'expiry ignored' ? expired.and(expired.not()) : expired, 2, 0)),
}))
// fresh(line, cursor, next, unseen): unseen → Followed{next, gap(...)} (a loss record first when next skips past
// cursor + 1, U32.add wrapping); else Followed{cursor, []}. outs counts the lines printed.
export const fresh = (bug?: JobsBug) => fun('JobsCore.fresh').inputs({line: nat, cursor: u32, next: u32, unseen: bool}).returns(({cursor, next, unseen}: Env) => {
  const print = bug === 'a seen event is printed again' ? yes : unseen
  const skipped = next.gt(when(cursor.eq(U32_MAX), 0, cursor.plus(1)))
  return {cursor: when(print, next, cursor), outs: when(print, when(skipped, 2, 1), 0)}
})
export const admit = (bug?: JobsBug) => fun('JobsCore.admit').inputs({closed: bool, total: nat, max: nat}).returns(({closed, total, max: m}: Env) => ({
  out: bit((bug === 'closed queue admits' ? yes : closed.not()).and(bug === 'bound is strict' ? total.lt(m) : bug === 'bound is off by one' ? total.atMost(m.plus(1)) : total.atMost(m))),
}))
// Base's Nat.is_ge(a, b) (a ≥ b), which the Bend proof of queue_refuses_past_its_bound needs as a lemma.
export const isGe = (bug?: JobsBug) => fun('Nat.is_ge').inputs({a: nat, b: nat}).returns(({a, b}: Env) => ({out: bit(bug === 'is_ge off by one' ? a.plus(1).atLeast(b) : a.atLeast(b))}))

// `follow` over a run: each event line, with its sequence number if it carries one (found, next), goes through
// JobsCore.sequenced/fresh; Printed lists the sequence numbers printed, in order.
export const follow = (bug?: 'prints an event equal to the cursor' | 'cursor not advanced') => rule('JobsCore.follow')
  .params({start: nat})
  .inputs({found: bool, next: nat})
  // U32 values, as nat with a bound (so random runs draw small ones; upTo draws over its whole range)
  .pre(({start}) => start.atMost(U32_MAX))
  .assume(({next}) => next.atMost(U32_MAX))
  .state({cursor: ({start}) => start, outs: 0})
  .lists('Printed')
  .flags(({found, next, cursor}) => ({unseen: found.and(bug === 'prints an event equal to the cursor' ? next.atLeast(cursor) : next.gt(cursor))}))
  .step(({unseen, next, cursor, Printed}) => ({
    cursor: when(unseen, bug === 'cursor not advanced' ? cursor : next, cursor),
    outs: when(unseen, when(next.gt(when(cursor.eq(U32_MAX), 0, cursor.plus(1))), 2, 1), 0),
    ...Printed.apply(Printed.push(next, unseen)),
  }))

// An interactive job's input queue (Host applies JobsCore.admit under the queue's lock; JobsCore.push appends,
// drained/emptied hand the bytes over): each write is a chunk (interned) of `bytes` bytes.
export type QueueBug = 'push prepends' | 'drain keeps the bytes' | 'admit ignores closed' | 'admit skips the bound' | 'drain reopens'
export const inputQueue = (bug?: QueueBug) => rule('JobsCore input queue')
  .params({max: nat})
  .inputs({op: oneOf('write', 'drain', 'seal'), bytes: nat, chunk: nat})
  .state({total: 0, closed: 0})
  .lists('Q')
  .flags(({op, bytes, total, closed, max: m}) => ({
    admitted: op.is('write').and(bug === 'admit ignores closed' ? yes : closed.eq(0), bug === 'admit skips the bound' ? yes : total.plus(bytes).atMost(m)),
    draining: op.is('drain'),
  }))
  .step(({op, admitted, draining, bytes, chunk, total, closed, Q}) => ({
    total: when(admitted, total.plus(bytes), when(draining, bug === 'drain keeps the bytes' ? total : 0, total)),
    // seal ends input; emptied() keeps `closed` (the bug resets it, as Queue{"", False{}} would).
    closed: when(op.is('seal'), 1, when(draining.and(bug === 'drain reopens' ? yes : yes.not()), 0, closed)),
    ...Q.apply(
      bug === 'push prepends' ? Q.insertAt(0, chunk, admitted) : Q.push(chunk, admitted),
      {when: draining.and(bug === 'drain keeps the bytes' ? yes.not() : yes), at: () => 0, len: 0},
    ),
  }))

// ===================================================================================================================
// StoreCore.bend
// ===================================================================================================================
export const STORE = ['Accept', 'Adopt', 'Refuse'] as const
export const STORE_MSGS = ['none', 'unreadable', 'newer'] as const
export type StoreBug = 'newer store adopted' | 'current store refused' | 'writer leaves unmarked home' | 'reader adopts'
const D = (s: (typeof STORE)[number]) => STORE.indexOf(s)
// versioned(found, shown): 0 → unreadable(), 1 → Accept, 2+ → newer(shown) (a Refuse whose message embeds shown).
const versionedTerm = (bug?: StoreBug) => (found: Env, shown: Env) => ({
  out: when(found.eq(0), D('Refuse'), when(found.eq(1), bug === 'current store refused' ? D('Refuse') : D('Accept'), bug === 'newer store adopted' ? D('Adopt') : D('Refuse'))),
  msg: when(found.eq(0), 1, when(found.eq(1), bug === 'current store refused' ? 1 : 0, bug === 'newer store adopted' ? 0 : 2)),
  shown: when(found.atLeast(2).and(bug === 'newer store adopted' ? yes.not() : yes), shown, 0),
})
const missingTerm = (bug?: StoreBug) => (mutating: Env, created: Env) => ({
  out: when(bug === 'writer leaves unmarked home' ? created : bug === 'reader adopts' ? yes : mutating.or(created), D('Adopt'), D('Accept')), msg: 0, shown: 0,
})
export const versioned = (bug?: StoreBug) => fun('StoreCore.versioned').inputs({found: nat, shown: nat}).returns(({found, shown}: Env) => versionedTerm(bug)(found, shown))
export const missing = (bug?: StoreBug) => fun('StoreCore.missing').inputs({mutating: bool, created: bool}).returns(({mutating, created}: Env) => missingTerm(bug)(mutating, created))
// decide(answer, mutating) whole: Host's answer starts with '+' (just created), another character, or is empty; the
// marker text after it is empty or not; a marker's store number is Codec.read → field "store" → Nat.read, a parse (the
// runtime's answer: parsed, missing when unreadable anywhere on the way; shown its lexeme).
export const storeDecide = (bug?: StoreBug) => fun('StoreCore.decide').inputs({lead: oneOf('plus', 'other', 'empty'), markerEmpty: bool, parsed: maybe(nat), shown: nat, mutating: bool})
  .returns(({lead, markerEmpty, parsed, shown, mutating}: Env) => {
    const created = lead.is('plus'), absent = lead.is('empty').or(markerEmpty)
    const miss = missingTerm(bug)(mutating, created), ver = versionedTerm(bug)(valueOf(parsed) as Env, shown)
    const readable = parsed.isSome
    const pick = (f: 'out' | 'msg' | 'shown', unreadable: TermLike) => when(absent, miss[f], when(readable, ver[f], unreadable))
    return {out: pick('out', D('Refuse')), msg: pick('msg', 1), shown: pick('shown', 0)}
  })

// ===================================================================================================================
// SpoolCore.bend
// ===================================================================================================================
export type SpoolBug = 'minus floors at one' | 'omitted measured from the window' | 'ended stream still holds back' | 'ceiling ignored'
// minus(a, b) = less(b, a), a recursive definition of a ∸ b; from(offset, oldest), a recursive definition of max.
const minusT = (bug?: SpoolBug) => (a: Env, b: Env) => (bug === 'minus floors at one' ? max(a.minus(b), 1) : a.minus(b))
export const minus = (bug?: SpoolBug) => fun('SpoolCore.minus').inputs({a: nat, b: nat}).returns(({a, b}: Env) => ({out: minusT(bug)(a, b)}))
export const from = () => fun('SpoolCore.from').inputs({offset: nat, oldest: nat}).returns(({offset, oldest}: Env) => ({out: max(offset, oldest)}))
const spanTerm = (bug?: SpoolBug) => ({retained, count: c, offset, max: m}: Env) => {
  const start = max(offset, retained)
  return {start, length: min(m, minusT(bug)(c, start)), omitted: bug === 'omitted measured from the window' ? minusT(bug)(start, retained) : minusT(bug)(start, offset)}
}
export const span = (bug?: SpoolBug) => fun('SpoolCore.span').inputs({retained: nat, count: nat, offset: nat, max: nat}).returns(spanTerm(bug))
// kept(bytes, ended): a prefix of bytes (List.take): all of them once ended, else without the trailing partial UTF-8
// character, whose length (0..3) held(bytes) finds by walking the list (the runtime's answer).
export const kept = (bug?: SpoolBug) => fun('SpoolCore.kept').inputs({len: nat, held: upTo(3), ended: bool}).returns(({len, held, ended}: Env) => ({
  len: bug === 'ended stream still holds back' ? len.minus(held) : when(ended, len, len.minus(held)),
}))
export const answerNow = (bug?: SpoolBug) => fun('SpoolCore.answer_now').inputs({expired: bool, returned: bool, eof: bool}).returns(({expired, returned, eof}: Env) => ({
  out: bit(bug === 'ceiling ignored' ? returned.or(eof) : expired.or(returned, eof)),
}))
// A reader following a rolling spool: the writer adds bytes; each read asks span(oldest(count), count, offset, max)
// and continues at start + length (the record's `next`). Not in Bend.
export const spoolReader = (bug?: 'loss not disclosed' | 'reader skips ahead') => rule('SpoolCore reader')
  .params({ring: nat, max: nat})
  .inputs({op: oneOf('write', 'read'), n: nat})
  .state({count: 0, offset: 0, delivered: 0, lost: 0})
  .flags(({op}) => ({reading: op.is('read')}))
  .step(({reading, n, count: c, offset, delivered, lost, ring, max: m}) => {
    const sp = spanTerm()({retained: c.minus(ring), count: c, offset, max: m})
    return {
      count: when(reading, c, c.plus(n)),
      offset: when(reading, (sp.start as Env).plus(sp.length).plus(bug === 'reader skips ahead' ? 1 : 0), offset),
      delivered: when(reading, delivered.plus(sp.length), delivered),
      lost: when(reading, bug === 'loss not disclosed' ? lost : lost.plus(sp.omitted), lost),
    }
  })

// ===================================================================================================================
// ServeCore.bend
// ===================================================================================================================
export const childLifetime = (bug?: 'requested time not cut' | 'no request means no lifetime') => fun('ServeCore.child_lifetime').inputs({requested: maybe(u32), left: u32})
  .returns(({requested, left}: Env) => {
    const chosen = requested.match({none: () => (bug === 'no request means no lifetime' ? 0 : left), some: (r: Env) => r})
    return {out: bug === 'requested time not cut' ? chosen : min(chosen, left)}
  })

// ===================================================================================================================
// DecisionProfiles.bend and DecisionConfig.bend
// ===================================================================================================================
// Interned keys and names with a fixed meaning.
export const KEY = {profile: 1, provider: 2, providerOptions: 3} as const
export const NAME = {'vercel-ai-gateway': 1, vercel: 2} as const
export type ProfileBug = 'provider beats explicit' | 'provider ignored' | 'default beats ambient' | 'absent selectors give none'
  | 'explicit provider still applies the profile' | 'explicit provider keeps the ambient target' | 'providerOptions merged recursively' | 'canonical swaps the two names'
// fallback(value, other) on maybe-strings ("" is none); choose_profile(explicit, provider, ambient, default).
type MaybeName = {some: Cond, id: TermLike}
const mname = (m: Env): MaybeName => ({some: m.isSome, id: valueOf(m)})
const fallback = (v: MaybeName, o: MaybeName): MaybeName => ({some: v.some.or(o.some), id: when(v.some, v.id, o.id)})
const chooseProfileT = (bug?: ProfileBug) => (explicit: MaybeName, provider: Cond, ambient: MaybeName, dflt: MaybeName): MaybeName => {
  const amb = bug === 'default beats ambient' ? fallback(dflt, ambient) : bug === 'absent selectors give none' ? (ambient) : fallback(ambient, dflt)
  const p = bug === 'provider ignored' ? yes.not() : provider
  const rest: MaybeName = {some: p.not().and(amb.some), id: when(p, 0, amb.id)}
  if (bug === 'provider beats explicit') return {some: p.not().and(explicit.some.or(amb.some)), id: when(p, 0, when(explicit.some, explicit.id, amb.id))}
  return fallback(explicit, rest)
}
export const chooseProfile = (bug?: ProfileBug) => fun('DecisionProfiles.choose_profile').inputs({explicit: maybe(nat), provider: bool, ambient: maybe(nat), default: maybe(nat)})
  .returns(({explicit, provider, ambient, default: d}: Env) => { const r = chooseProfileT(bug)(mname(explicit), provider, mname(ambient), mname(d)); return {some: bit(r.some), id: when(r.some, r.id, 0)} })

// apply_document(request, Document{entries, default}, ambient). The request is an object (reqObject) given as a map
// Req; its "profile" member's value is a valid profile-name string (named, interned as profileName), another string or
// not a string (profileKind, the runtime's answer from Wire.profile_name); the chosen profile is a valid name or not
// (chosenValid), has an entry among the document's (entryFound, a list search: the runtime's answer) whose provider
// is a string (entryProvider) compatible with the request's (compatible); Entry is that entry as a map.
// The selected request: the request less its "profile" member, merged over the entry when a profile was chosen.
export const applyDocument = (bug?: ProfileBug) => rule('DecisionProfiles.apply_document')
  .inputs({reqObject: bool, profileKind: oneOf('absent', 'name', 'other-string', 'not-string'), profileName: nat, ambient: maybe(nat), default: maybe(nat),
    chosenValid: bool, entryFound: bool, entryProvider: bool, compatible: bool})
  .carries('Req', 'Entry')
  .maps({Out: 0})
  .state({ok: 0, chosen: 0, profile: 0})
  .assume(({profileKind, Req}) => profileKind.is('absent').iff(Req.at(KEY.profile).eq(0)))
  .flags(({profileKind, profileName, ambient, default: d, Req}) => {
    const explicit: MaybeName = {some: profileKind.is('name'), id: when(profileKind.is('name'), profileName, 0)}
    const p = chooseProfileT(bug === 'explicit provider still applies the profile' ? 'provider ignored' : undefined)(explicit, Req.at(KEY.provider).atLeast(1), mname(ambient), mname(d))
    return {chosenSome: p.some, explicitOk: profileKind.is('absent').or(profileKind.is('name'))}
  })
  .flags(({reqObject, explicitOk, chosenSome, chosenValid, entryFound, entryProvider, compatible}) => ({
    applied: reqObject.and(explicitOk, chosenSome.not().or(chosenValid.and(entryFound, entryProvider, compatible))),
  }))
  .step(({applied, chosenSome, profileKind, profileName, ambient, default: d, Req, Entry, Out}) => {
    const explicit: MaybeName = {some: profileKind.is('name'), id: when(profileKind.is('name'), profileName, 0)}
    const p = chooseProfileT(bug === 'explicit provider still applies the profile' ? 'provider ignored' : undefined)(explicit, Req.at(KEY.provider).atLeast(1), mname(ambient), mname(d))
    const less = (k: Env) => when(k.eq(KEY.profile), 0, Req.at(k))
    return {
      ok: bit(applied), chosen: bit(applied.and(chosenSome)), profile: when(applied.and(chosenSome), p.id, 0),
      Out: Out.each(k => when(applied, when(chosenSome, when(less(k).atLeast(1), less(k), Entry.at(k)), less(k)), 0)),
    }
  })

// merge(base, overrides): both objects; every base member whose key the overrides lack, then every override member.
// As maps: Out[k] = Over[k] where present, else Base[k]. A second base (BaseB, OutB) runs beside it for the
// noninterference law (Bend's shadowed_provider_options_are_irrelevant compares two merges).
export const merge = (bug?: ProfileBug) => rule('DecisionProfiles.merge')
  .inputs({baseObject: bool, overObject: bool})
  .carries('Base', 'BaseB', 'Over')
  .maps({Out: 0, OutB: 0})
  .state({ok: 0})
  .step(({baseObject, overObject, Base, BaseB, Over, Out, OutB}) => {
    const ok = baseObject.and(overObject)
    const at = (B: Env) => (k: Env) => when(ok, bug === 'providerOptions merged recursively'
      ? when(Over.at(k).atLeast(1), when(k.eq(KEY.providerOptions), max(Over.at(k), B.at(k)), Over.at(k)), B.at(k))
      : when(Over.at(k).atLeast(1), Over.at(k), B.at(k)), 0)
    return {ok: bit(ok), Out: Out.each(at(Base)), OutB: OutB.each(at(BaseB))}
  })

// configure_explicit(request, settings, model_env, endpoint_env, account, explicit): an explicit provider hands
// configure "" for both ambient values. configure itself (string validation and preset lookup) is a function of its
// arguments; the function gives the arguments it receives: the model and endpoint env, as maybe-strings.
export const configureExplicit = (bug?: ProfileBug) => fun('DecisionConfig.configure_explicit').inputs({explicit: bool, model: maybe(nat), endpoint: maybe(nat)})
  .returns(({explicit, model, endpoint}) => {
    const pass = (m: Env, keepOnExplicit: boolean) => when(explicit.and(keepOnExplicit ? yes.not() : yes), 0, when(m.isSome, valueOf(m), 0))
    return {model: pass(model, bug === 'explicit provider keeps the ambient target'), endpoint: pass(endpoint, false)}
  })
// canonical(provider): "vercel-ai-gateway" → "vercel", else itself.
export const canonicalT = (bug?: ProfileBug) => (p: Env) => (bug === 'canonical swaps the two names'
  ? when(p.eq(NAME['vercel-ai-gateway']), NAME.vercel, when(p.eq(NAME.vercel), NAME['vercel-ai-gateway'], p))
  : when(p.eq(NAME['vercel-ai-gateway']), NAME.vercel, p))
export const canonical = (bug?: ProfileBug) => fun('DecisionConfig.canonical').inputs({provider: nat, matched: bool}).returns(({provider}: Env) => {
  const c = canonicalT(bug)(provider)
  return {once: c, twice: canonicalT(bug)(c as Env)}
})
