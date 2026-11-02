// Business days over a calendar (`gdp-wired/laws`): "within 10 business days" decided in the kernel's own arithmetic,
// nothing new trusted. A calendar is its weekend days, its holidays (dates) and its offset from UTC, stated once
// (`[calendar]` in gdp.toml, or given here); the request's time is the clock's (seconds or milliseconds since 1970 UTC).
//
// The count. A time x is on day s(x) = ⌊(x + offset)/D⌋ + 10 (D a day in the clock's units; day 0 the Monday 1969-12-22,
// so a time from 1970 on, at any offset within ±14 h, is on a day at least 0). C(x), the business days up to and
// including x's day, is
//   C(x) = k·w + #{p a working weekday : p <= r} − #{h a holiday on a working weekday : h <= s(x)}
// with w = ⌊y/7D⌋ x's week, r its weekday (0 Monday), y = x + offset + 10·D and k the working days in a week. Each
// "p <= r" is y >= 7D·w + D·p, and each "h <= s(x)" is y >= D·h: comparisons linear in y and w. So C is linear but for
// the one division ⌊y/7D⌋. Where the law may read functions (a law about every state) that is divBy(7D), the kernel's
// own div$k with its facts; a law of one step can't read a function, so there the week is a key the law holds at
// every value of, under the guard 7D·w <= y < 7D·w + 7D, which only ⌊y/7D⌋ meets: ∀w. guard → L is L at ⌊y/7D⌋.
//
// Elapsed business days from a to b: C(b) − C(a), the business days after a's day up to and including b's (the day
// of receipt doesn't count; the last day counts whole). Negative where b is before a. `now - received <= 10 business
// days` in a law is C(now) − C(received) <= 10.
//
// What it doesn't model: daylight saving (one fixed offset), a holiday not listed (a year with no list has none),
// half days. The calendar is the person's statement, like a law's citation; the arithmetic over it is exact.
import {type Cond, Int, type IntLike, Term, all, when} from './dsl.ts'

export type Calendar = {weekend?: string[], holidays?: string[], utc_offset?: string}
const DAYS = ['mon', 'tue', 'wed', 'thu', 'fri', 'sat', 'sun']
export class CalendarError extends Error {}
// A time with its week pinned (a key of a step law): `between` reads the week from it instead of dividing.
export type Pinned = {t: Int, w: Int}
// Day index of a date (YYYY-MM-DD) from the Monday 1969-12-22.
const dayOf = (d: string): number => {
  const m = /^(\d{4})-(\d{2})-(\d{2})$/.exec(d.trim())
  const t = m ? Date.UTC(Number(m[1]), Number(m[2]) - 1, Number(m[3])) : NaN
  if (!m || Number.isNaN(t) || new Date(t).toISOString().slice(0, 10) !== d.trim()) throw new CalendarError(`${d}: a holiday is a date, YYYY-MM-DD`)
  return t / 86_400_000 + 10
}

export function businessDays(cal: Calendar, clock: 's' | 'ms' = 's') {
  const unit = clock === 'ms' ? 1000 : 1, D = 86_400 * unit, W = 7 * D
  const weekend = (cal.weekend ?? ['sat', 'sun']).map(d => d.trim().toLowerCase().slice(0, 3))
  for (const d of weekend) if (!DAYS.includes(d)) throw new CalendarError(`${d}: a weekend day is one of ${DAYS.join(', ')}`)
  const work = DAYS.map((_, p) => p).filter(p => !weekend.includes(DAYS[p]!))
  if (!work.length) throw new CalendarError('a calendar whose every day is a weekend day has no business day')
  const off = /^([+-])(\d{2}):(\d{2})$/.exec((cal.utc_offset ?? '+00:00').trim())
  if (!off || Number(off[2]) * 60 + Number(off[3]) > 14 * 60 || Number(off[3]) > 59) throw new CalendarError(`${cal.utc_offset}: an offset from UTC is ±HH:MM, at most 14 hours`)
  const offset = (off[1] === '-' ? -1 : 1) * (Number(off[2]) * 3600 + Number(off[3]) * 60) * unit
  // (the holidays that take a working day away, each once, in order)
  const hols = [...new Set((cal.holidays ?? []).map(dayOf))].filter(h => work.includes(h % 7)).sort((a, b) => a - b)
  const shift = (x: IntLike) => Int.of(x).plus(offset + 10 * D)
  // (the holidays on or before y's day, as a balanced choice: one path per count, never 2^n)
  const held = (y: Int, lo: number, hi: number): Int => {
    if (lo > hi) return Int.of(0)
    const mid = (lo + hi) >> 1
    return when(y.atLeast(hols[mid]! * D), held(y, mid + 1, hi).plus(mid - lo + 1), held(y, lo, mid - 1))
  }
  // C at y = x + offset + 10D in week w.
  const count = (y: Int, w: Int): Int => work.reduce((n, p) => n.plus(when(y.atLeast(w.times(W).plus(p * D)), Int.of(1), Int.of(0))), w.times(work.length)).minus(held(y, 0, hols.length - 1))
  const pinned = (x: IntLike | Pinned): x is Pinned => typeof x === 'object' && x !== null && 'w' in x && 't' in x
  const C = (x: IntLike | Pinned): Int => (pinned(x) ? count(shift(x.t), x.w) : count(shift(x), shift(x).divBy(W)))
  return {
    calendar: {weekend, holidays: hols.length, offset: cal.utc_offset ?? '+00:00', clock},
    // The business days up to and including x's day (from 1969-12-22), and from a's day to b's.
    upTo: C,
    between: (a: IntLike | Pinned, b: IntLike | Pinned): Int => C(b).minus(C(a)),
    // x's week pinned to the key w (a step law's), with the guard only ⌊y/7D⌋ meets.
    pin: (x: IntLike, w: IntLike): {at: Pinned, guard: Cond} => {
      const y = shift(x), wk = Int.of(w)
      return {at: {t: Int.of(x), w: wk}, guard: all(wk.times(W).atMost(y), y.lt(wk.times(W).plus(W)))}
    },
    // The same count computed (for runs and tests): the business days from a's day to b's.
    count: (a: number, b: number): number => {
      const c = (x: number) => { const y = x + offset + 10 * D, s = Math.floor(y / D), w = Math.floor(y / W), r = s - 7 * w
        return w * work.length + work.filter(p => p <= r).length - hols.filter(h => h <= s).length }
      return c(b) - c(a)
    },
  }
}
export type BusinessDays = ReturnType<typeof businessDays>
// A key's term as an integer (a step law's key is a natural; the week of a time before 1969-12-22 has none, so a key
// for one is the difference of two).
export const keyInt = (k: Term, k2?: Term): Int => (k2 ? new Int(k, k2) : Int.of(k))
