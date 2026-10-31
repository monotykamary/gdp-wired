// RFC 3261 section 17's four transaction state machines, with RFC 6026's changes to the INVITE ones, as WRITTEN models
// (no reader takes a SIP stack's transaction layer as it ships: research/distributed/DESIGN.md, section 6, has the
// survey), every transaction at once (lift: each a process keyed by its id) beside the time (core/system.ts's time) and
// each transaction's clock (clocked, skew 0 by default: one node's clock is the time its own timers read). A timer is
// a step allowed once the clock has passed its deadline: it fires late by any amount, never early.
//
// The progress law of each, "every transaction eventually terminates", over every transaction (a keyed leads-to), under
// weak fairness of: time passing (the time's step), each timer due firing, and, where stated, the far end or the TU:
//   NICT (17.1.2.2)  Trying, Proceeding: Timer F (64*T1) terminates; Completed: Timer K (T4, or 0 reliable).
//   ICT (17.1.1.2; RFC 6026 7.2)  Calling: Timer B (64*T1); Completed: Timer D (> 32 s, or 0); Accepted: Timer M
//                    (64*T1). Proceeding has no timer: a final response must come (the far end's), refuted without it.
//   IST (17.2.1; RFC 6026 7.1)  Completed: Timer H (64*T1); Confirmed: Timer I (T4, or 0); Accepted: Timer L (64*T1).
//                    Proceeding has no timer: the TU must send a final response, refuted without it.
//   NIST (17.2.2)    Completed: Timer J (64*T1, or 0). Trying and Proceeding have no timer: the TU's final response.
// What is modelled: each state, each event of the figures (responses and requests from the network, the TU's
// responses, the timers, a transport error), the timers' deadlines and the retransmission intervals (A and G double,
// E and G capped at T2). What is not: message contents, the transport's own retransmission, the TU's other duties.
//   bun research/distributed/sip.ts [--ms 20000] [--skew E]
import {type KeyedLiveness, type Rule, all, any, min, nat, oneOf, proveLeadsTo, refuteLeadsTo, rule, when} from '../../core/dsl.ts'
import {clocked, modelsOf, system, time} from '../../core/system.ts'

const arg = (n: string) => { const i = process.argv.indexOf(`--${n}`); return i < 0 ? undefined : process.argv[i + 1] }
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Env = any
// The states (one numbering for the four; 0 is a transaction not yet started).
export const S = {idle: 0, trying: 1, proceeding: 2, completed: 3, terminated: 4, accepted: 5, confirmed: 6, calling: 7} as const
const params = {T1: nat, T2: nat, T4: nat, D: nat}
const pre = ({T1, T2}: Env) => T1.atLeast(1).and(T1.atMost(T2))
const inS = (st: Env, ...xs: number[]) => any(...xs.map(x => st.eq(x)))
// The transitions: the first case whose condition holds gives the next value, else it is kept.
const cases = (keep: Env, ...cs: [Env, Env][]) => cs.reduceRight((acc, [c, v]) => when(c, v, acc), keep)

// Non-INVITE client transaction (17.1.2.2, Figure 6).
const NICT = ['start', 'r1xx', 'rfinal', 'timerE', 'timerF', 'timerK', 'transportError'] as const
export const nict = rule('NICT').params(params).inputs({ev: oneOf(...NICT), t: nat}).state({st: 0, eAt: 0, eInt: 0, fAt: 0, kAt: 0}).pre(pre)
  .assume(({ev, t, st, eAt, fAt, kAt}) => all(
    ev.is('start').implies(st.eq(S.idle)),
    ev.is('timerE').implies(inS(st, S.trying, S.proceeding).and(eAt.atMost(t))),
    ev.is('timerF').implies(inS(st, S.trying, S.proceeding).and(fAt.atMost(t))),
    ev.is('timerK').implies(st.eq(S.completed).and(kAt.atMost(t))),
    ev.is('transportError').implies(inS(st, S.trying, S.proceeding))))
  .step(({ev, t, st, eAt, eInt, fAt, kAt, T1, T2, T4}) => {
    const live = inS(st, S.trying, S.proceeding), e2 = when(st.eq(S.trying), min(eInt.times(2), T2), T2)
    return {
      st: cases(st, [ev.is('start'), S.trying], [ev.is('r1xx').and(live), S.proceeding], [ev.is('rfinal').and(live), S.completed],
        [any(ev.is('timerF'), ev.is('timerK'), ev.is('transportError')), S.terminated]),
      // (E: T1, then MIN(2*T1, T2), MIN(4*T1, T2), ... in Trying; T2 in Proceeding)
      eInt: cases(eInt, [ev.is('start'), T1], [ev.is('timerE'), e2]),
      eAt: cases(eAt, [ev.is('start'), t.plus(T1)], [ev.is('timerE'), t.plus(e2)]),
      fAt: cases(fAt, [ev.is('start'), t.plus(T1.times(64))]),
      kAt: cases(kAt, [ev.is('rfinal').and(live), t.plus(T4)]),
    }
  })

// INVITE client transaction (17.1.1.2, Figure 5; RFC 6026 7.2 and Figure 5: a 2xx goes to Accepted, Timer M).
const ICT = ['start', 'r1xx', 'r2xx', 'r300to699', 'timerA', 'timerB', 'timerD', 'timerM', 'transportError'] as const
export const ict = rule('ICT').params(params).inputs({ev: oneOf(...ICT), t: nat}).state({st: 0, aAt: 0, aInt: 0, bAt: 0, dAt: 0, mAt: 0}).pre(pre)
  .assume(({ev, t, st, aAt, bAt, dAt, mAt}) => all(
    ev.is('start').implies(st.eq(S.idle)),
    ev.is('timerA').implies(st.eq(S.calling).and(aAt.atMost(t))),
    ev.is('timerB').implies(st.eq(S.calling).and(bAt.atMost(t))),
    ev.is('timerD').implies(st.eq(S.completed).and(dAt.atMost(t))),
    ev.is('timerM').implies(st.eq(S.accepted).and(mAt.atMost(t))),
    ev.is('transportError').implies(inS(st, S.calling, S.completed))))
  .step(({ev, t, st, aAt, aInt, bAt, dAt, mAt, T1, D}) => {
    const live = inS(st, S.calling, S.proceeding)
    return {
      st: cases(st, [ev.is('start'), S.calling], [ev.is('r1xx').and(live), S.proceeding], [ev.is('r2xx').and(live), S.accepted],
        [ev.is('r300to699').and(live), S.completed], [any(ev.is('timerB'), ev.is('timerD'), ev.is('timerM'), ev.is('transportError')), S.terminated]),
      // (A: T1, doubling at each firing, while Calling)
      aInt: cases(aInt, [ev.is('start'), T1], [ev.is('timerA'), aInt.times(2)]),
      aAt: cases(aAt, [ev.is('start'), t.plus(T1)], [ev.is('timerA'), t.plus(aInt.times(2))]),
      bAt: cases(bAt, [ev.is('start'), t.plus(T1.times(64))]),
      dAt: cases(dAt, [ev.is('r300to699').and(live), t.plus(D)]),
      mAt: cases(mAt, [ev.is('r2xx').and(live), t.plus(T1.times(64))]),
    }
  })

// INVITE server transaction (17.2.1, Figure 7; RFC 6026 7.1 and Figure 7: the TU's 2xx goes to Accepted, Timer L).
const IST = ['start', 'tu1xx', 'tu2xx', 'tu300to699', 'ack', 'timerG', 'timerH', 'timerI', 'timerL', 'transportError'] as const
export const ist = rule('IST').params(params).inputs({ev: oneOf(...IST), t: nat}).state({st: 0, gAt: 0, gInt: 0, hAt: 0, iAt: 0, lAt: 0}).pre(pre)
  .assume(({ev, t, st, gAt, hAt, iAt, lAt}) => all(
    ev.is('start').implies(st.eq(S.idle)),
    ev.is('timerG').implies(st.eq(S.completed).and(gAt.atMost(t))),
    ev.is('timerH').implies(st.eq(S.completed).and(hAt.atMost(t))),
    ev.is('timerI').implies(st.eq(S.confirmed).and(iAt.atMost(t))),
    ev.is('timerL').implies(st.eq(S.accepted).and(lAt.atMost(t))),
    ev.is('transportError').implies(inS(st, S.proceeding, S.completed))))
  .step(({ev, t, st, gAt, gInt, hAt, iAt, lAt, T1, T2, T4}) => {
    const proc = st.eq(S.proceeding), g2 = min(gInt.times(2), T2)
    return {
      st: cases(st, [ev.is('start'), S.proceeding], [ev.is('tu2xx').and(proc), S.accepted], [ev.is('tu300to699').and(proc), S.completed],
        [ev.is('ack').and(st.eq(S.completed)), S.confirmed], [any(ev.is('timerH'), ev.is('timerI'), ev.is('timerL'), ev.is('transportError')), S.terminated]),
      // (G: T1, then MIN(2*T1, T2), ... while Completed, unreliable transports)
      gInt: cases(gInt, [ev.is('tu300to699').and(proc), T1], [ev.is('timerG'), g2]),
      gAt: cases(gAt, [ev.is('tu300to699').and(proc), t.plus(T1)], [ev.is('timerG'), t.plus(g2)]),
      hAt: cases(hAt, [ev.is('tu300to699').and(proc), t.plus(T1.times(64))]),
      iAt: cases(iAt, [ev.is('ack').and(st.eq(S.completed)), t.plus(T4)]),
      lAt: cases(lAt, [ev.is('tu2xx').and(proc), t.plus(T1.times(64))]),
    }
  })

// Non-INVITE server transaction (17.2.2, Figure 8).
const NIST = ['start', 'request', 'tu1xx', 'tufinal', 'timerJ', 'transportError'] as const
export const nist = rule('NIST').params(params).inputs({ev: oneOf(...NIST), t: nat}).state({st: 0, jAt: 0}).pre(pre)
  .assume(({ev, t, st, jAt}) => all(
    ev.is('start').implies(st.eq(S.idle)),
    ev.is('timerJ').implies(st.eq(S.completed).and(jAt.atMost(t))),
    ev.is('transportError').implies(inS(st, S.proceeding, S.completed))))
  .step(({ev, t, st, jAt, T1}) => {
    const live = inS(st, S.trying, S.proceeding)
    return {
      st: cases(st, [ev.is('start'), S.trying], [ev.is('tu1xx').and(live), S.proceeding], [ev.is('tufinal').and(live), S.completed],
        [any(ev.is('timerJ'), ev.is('transportError')), S.terminated]),
      // (J: 64*T1 for unreliable transports, 0 for reliable: here 64*T1, the longer)
      jAt: cases(jAt, [ev.is('tufinal').and(live), t.plus(T1.times(64))]),
    }
  })

// A transaction kind: its rule, its events, and its progress: the states it lives in, each timer that ends a state
// (its deadline and its event), and what the law assumes of the far end or the TU in the states no timer ends.
type Spec = {rule: Rule<Env, Env, Env, Env, Env, Env, Env, Env>, events: readonly string[], live: number[], timers: {in: number[], at: string, ev: string}[], answers: {in: number[], ev: string}[]}
export const KINDS: Record<string, Spec> = {
  NICT: {rule: nict as never, events: NICT, live: [S.trying, S.proceeding, S.completed], timers: [{in: [S.trying, S.proceeding], at: 'fAt', ev: 'timerF'}, {in: [S.completed], at: 'kAt', ev: 'timerK'}], answers: []},
  ICT: {rule: ict as never, events: ICT, live: [S.calling, S.proceeding, S.completed, S.accepted], timers: [{in: [S.calling], at: 'bAt', ev: 'timerB'}, {in: [S.completed], at: 'dAt', ev: 'timerD'}, {in: [S.accepted], at: 'mAt', ev: 'timerM'}],
    answers: [{in: [S.proceeding], ev: 'r300to699'}]},
  IST: {rule: ist as never, events: IST, live: [S.proceeding, S.completed, S.confirmed, S.accepted], timers: [{in: [S.completed], at: 'hAt', ev: 'timerH'}, {in: [S.confirmed], at: 'iAt', ev: 'timerI'}, {in: [S.accepted], at: 'lAt', ev: 'timerL'}],
    answers: [{in: [S.proceeding], ev: 'tu300to699'}]},
  NIST: {rule: nist as never, events: NIST, live: [S.trying, S.proceeding, S.completed], timers: [{in: [S.completed], at: 'jAt', ev: 'timerJ'}], answers: [{in: [S.trying, S.proceeding], ev: 'tufinal'}]},
}
// Every transaction of a kind at once, beside the time: act 0 the time, 1 a transaction's event.
export const transactions = (kind: keyof typeof KINDS, skew: number | string = 0) =>
  system(kind, {time: time(), tx: {rule: clocked(KINDS[kind]!.rule.machine, 't', skew), id: 'tx'}}, {kinds: {ev: oneOf(...KINDS[kind]!.events)}})
// "Every transaction eventually terminates": from a live state to Terminated, for every transaction k, under weak
// fairness of time passing (where a timer of k's state is not due), of each timer of k due firing, and with `answered`,
// of the far end's or the TU's final response in the states no timer ends.
export function terminates(kind: keyof typeof KINDS, r: ReturnType<typeof transactions>, answered: boolean): KeyedLiveness {
  const s = KINDS[kind]!, ev = (e: string) => s.events.indexOf(e)
  // (the clock's reading left free: with no skew it is the time itself)
  const fire = (k: Env, e: string, _b: Env) => ({act: 1, tx: k, ev: ev(e)})
  return r.leadsTo(`every ${kind} eventually terminates${answered ? ' (the final response comes)' : ''}`, {
    from: ({st}: Env, k) => inS(st.at(k), ...s.live), to: ({st}: Env, k) => st.at(k).eq(S.terminated),
    helpful: [
      {when: (b: Env, k) => any(...s.timers.map(tm => inS(b.st.at(k), ...tm.in).and(b.now.lt(b[tm.at].at(k))))), request: () => ({act: 0, dt: 1})},
      ...s.timers.map(tm => ({when: (b: Env, k: Env) => inS(b.st.at(k), ...tm.in).and(b[tm.at].at(k).atMost(b.now)), request: (b: Env, k: Env) => fire(k, tm.ev, b)})),
      ...(answered ? s.answers.map(a => ({when: (b: Env, k: Env) => inS(b.st.at(k), ...a.in), request: (b: Env, k: Env) => fire(k, a.ev, b)})) : []),
    ],
  })
}

if (import.meta.main) {
  const ms = Number(arg('ms') ?? 20_000), skew = arg('skew') ?? 0
  for (const kind of Object.keys(KINDS) as (keyof typeof KINDS)[]) {
    const r = transactions(kind, typeof skew === 'string' && /^\d+$/.test(skew) ? Number(skew) : skew)
    for (const answered of KINDS[kind]!.answers.length ? [false, true] : [false]) {
      const l = terminates(kind, r, answered), t0 = performance.now(), v = proveLeadsTo(r, [], l, {ms})
      const verdict = v.proven && v.checked ? 'proven' : 'unknown'
      console.log(`${kind} | ${l.name} | assumes ${modelsOf(r).map(m => m.name).join(', ')} | ${verdict} | ${Math.round(performance.now() - t0)} ms${v.found?.rank ? ` | rank ${v.found.rank}` : ''}${v.found?.laws?.length ? ` | laws: ${v.found.laws.map(f => f.text).join('; ')}` : ''}`)
      if (verdict !== 'proven') console.log(`    ${v.goal ?? ''} | ${v.stuck ?? ''} | ${v.why ?? ''}`)
      if (verdict !== 'proven') {
        // a fair run that never terminates: found from the runs, its ring checked by the kernel
        const t1 = performance.now(), f = refuteLeadsTo(r, [], l, {ms})
        console.log(`    a fair run that never gets there: ${f ? (f.verdict.refuted ? `refuted, the run fair: ${f.verdict.fair!.join(', ')}` : `not shown (${f.verdict.why})`) : 'none found'} | ${Math.round(performance.now() - t1)} ms`)
        if (f?.verdict.refuted) console.log(`      stem ${JSON.stringify(f.ring.stem)} at ${JSON.stringify(f.ring.params)}; ring: ${f.ring.sets.map(x => `${JSON.stringify(x.request)} from ${JSON.stringify(x.holds)}`).join(' ; ')}`)
      }
    }
  }
}
