// golang.org/x/time/rate v0.16.0 (github.com/golang/time), Limiter.AllowN: reserveN with maxFutureReserve 0 and the
// advance it calls. BSD-3-Clause, (c) The Go Authors.
// https://github.com/golang/time/blob/fb013b3d305a26f5ef5350a6eaffc7c87a200383/rate/rate.go
//
// A token bucket of `burst` tokens refilled at `limit` tokens per second: AllowN(t, n) reports whether n events may
// happen at t, and takes n tokens if so (rate.go:116-118 -> :337-383).
//
// Mapping:
// - `t: nat` is AllowN's own argument (rate.go:116), in ticks; the rule's `rate` is tokens per tick, a natural (the code's
//   is a float64 per second, see the gaps). `tokens` is a natural: with maxFutureReserve 0 a granted request never
//   leaves the bucket below 0 (waitDuration <= 0 means tokens >= n, up to the float caveat in the gaps).
// - `inf`: limit == Inf (rate.go:341-348): every request is granted and nothing changes.
// - NewLimiter (rate.go:100-106): tokens = burst, last the zero time (0 here).
// - Ghosts: `admitted` (the n of every granted request: observed results), `latest` (the latest t seen), `okLast`
//   (AllowN's answer to the last request).
import {max, min, nat, bool, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'golang/time', commit: 'fb013b3d305a26f5ef5350a6eaffc7c87a200383', licence: 'BSD-3-Clause', author: 'The Go Authors', language: 'Go'}

export const allowN = () => rule('x/time/rate Limiter.AllowN')
  .params({rate: nat, burst: nat, inf: bool})
  .inputs({t: nat, n: nat})
  .state({tokens: ({burst}) => burst, last: 0, admitted: 0, latest: 0, okLast: bool.from(false)})
  .flags(({t, n, rate, burst, inf, tokens, last}) => {
    // advance (rate.go:387-401): last := min(lim.last, t); tokens + elapsed * limit, at most burst.
    const elapsed = t.minus(min(last, t)), ts = min(burst, tokens.plus(elapsed.mul(rate)))
    // rate.go:356-367: ok := n <= burst && waitDuration <= maxFutureReserve (0): waitDuration is 0 iff tokens - n >= 0
    // (a zero limit gives InfDuration when short, rate.go:406-408, the same answer).
    return {ok: inf.or(n.atMost(burst).and(n.atMost(ts))), takes: inf.not().and(n.atMost(burst), n.atMost(ts))}
  })
  .step(({t, n, rate, burst, tokens, last, admitted, latest, ok, takes}) => {
    const ts = min(burst, tokens.plus(t.minus(min(last, t)).mul(rate)))
    return {
      // rate.go:376-381: if ok { lim.last = t; lim.tokens = tokens }.
      tokens: when(takes, ts.minus(n), tokens),
      last: when(takes, t, last),
      admitted: when(ok, admitted.plus(n), admitted),
      latest: max(latest, t),
      okLast: ok,
    }
  })

const r = allowN()
const cite = (lines: string, exp: string) => ({...src, path: 'rate/rate.go', lines, export: exp})

export const items: RealItem[] = [{
  id: 'rate limit/golang-x-time/AllowN',
  domain: 'rate limit',
  source: cite('100-118,337-401', 'Limiter.AllowN'),
  also: [cite('33-41', 'Limiter (doc)'), cite('403-428', 'durationFromTokens, tokensFromDuration')],
  summary: 'A token bucket of burst tokens refilled at limit per second from the last update; AllowN(t, n) grants n events at t when the bucket, refilled to t and capped at burst, holds n, and then takes them and sets last = t.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'tokens and limit are float64, elapsed time is ns read as float seconds (rate.go:396, :422-427): the rule uses whole ticks and a whole rate per tick; with floats a shortfall below 1e-9 s of tokens truncates to a 0 wait (rate.go:410, time.Duration(duration)) and is granted'},
    {gap: 'nonlinear', blocks: 'part', detail: 'elapsed × limit (rate.go:395, tokensFromDuration) is a product of two unknowns in the step'},
    {gap: 'scope', blocks: 'part', detail: 'only AllowN (maxFutureReserve 0): ReserveN / WaitN (debt, a negative token count), Cancel and SetLimitAt / SetBurstAt are left out'},
  ],
  laws: [
    invariant(r, r.law('the bucket never holds more than burst tokens', ({tokens, burst}) => tokens.atMost(burst)),
      'safety', 'docs', 'rate.go:101-102 NewLimiter "permits bursts of at most b tokens"'),
    stepLaw(r, r.stepLaw('a refused request changes nothing',
      ({tokens, last}, after) => after.tokens.eq(tokens).and(after.last.eq(last)),
      ({ok}) => ok.not()),
    'step', 'docs', 'rate.go:111-113 AllowN "Use this method if you intend to drop / skip events that exceed the rate limit"; :376 the state is updated only if ok'),
    invariant(r, r.law('no more is granted than burst plus rate times the latest time seen', ({admitted, burst, rate, latest, inf}) => inf.or(admitted.atMost(burst.plus(rate.mul(latest))))),
      'safety', 'docs', 'rate.go:35-37 "Informally, in any large enough time interval, the Limiter limits the rate to r tokens per second, with a maximum burst size of b events"'),
    leadsTo(r, r.leadsTo('a refused caller is granted one event once it waits long enough', {
      from: ({okLast, rate, burst}) => okLast.not().and(rate.atLeast(1), burst.atLeast(1)),
      to: ({okLast}) => okLast,
      helpful: ({last, burst}) => ({t: last.plus(burst), n: 1}),
    }), 'docs', 'rate.go:33-34 "a token bucket of size b, initially full and refilled at rate r tokens per second"'),
  ],
}]
