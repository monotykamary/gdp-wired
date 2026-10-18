// The bench's gdp-wired side: `bun compare/bench/gdpwired.ts <rule> <N>` runs the rule's compiled step (`.compiled()`,
// the JavaScript compileJs makes from the machine proveRule proved, imported unchanged from compare/gdpwired/) over N
// requests from the shared stream, and prints a checksum of the final state, the same line the Bend and Lean benches
// print. The stream: the LCG x' = (x * 1103515245 + 12345) mod 2^31 from x = 42, one step per request, each request's
// fields read off the new x.
//   budget: c = x mod 16; b = 8N, m = 10. Prints s.
//   caps: acct = x mod 1000, day = x mod 365, ok = x mod 4 != 0; d = 3. Prints the grants, their acct sum, their day sum.
//   window: t = the previous t + x mod 3 (from 0), forced = x mod 10 == 0; w = 60, c = 5. Prints the logged requests,
//   how many were forced, the sum of their t.
import {budget} from '../gdpwired/budget.ts'
import {caps} from '../gdpwired/caps.ts'
import {proved as window} from '../gdpwired/window.ts'

const lcg = (x: number) => ((Math.imul(x, 1103515245) + 12345) >>> 0) & 0x7fffffff
const [rule, arg] = process.argv.slice(2)
const n = Number(arg ?? 0)

// Inputs are built in the shape encodeInput gives (naturals, a bool as 0 or 1); the first one is checked against it.
function same(a: object, b: object) { if (JSON.stringify(a) !== JSON.stringify(b)) throw new Error(`input encoding: ${JSON.stringify(a)} vs ${JSON.stringify(b)}`) }

if (rule === 'budget') {
  const js = budget.compiled(), params = budget.encodeParams({b: 8 * n, m: 10})
  let st = js.init(params), x = 42
  for (let i = 0; i < n; i++) {
    x = lcg(x)
    const input = {c: x % 16}
    if (i === 0) same(input, budget.encodeInput({c: x % 16}))
    st = js.step(params, st, input)
  }
  console.log(`${st.scalars.s}`)
} else if (rule === 'caps') {
  const js = caps.compiled(), params = caps.encodeParams({d: 3})
  let st = js.init(params), x = 42
  for (let i = 0; i < n; i++) {
    x = lcg(x)
    const input = {acct: x % 1000, day: x % 365, ok: x % 4 !== 0 ? 1 : 0}
    if (i === 0) same(input, caps.encodeInput({acct: x % 1000, day: x % 365, ok: x % 4 !== 0}))
    st = js.step(params, st, input)
  }
  let grants = 0, accts = 0, days = 0
  for (const [k, v] of st.maps.Acct!) { grants += v; accts += k * v }
  for (const [k, v] of st.maps.Day!) days += k * v
  console.log(`${grants} ${accts} ${days}`)
} else if (rule === 'window') {
  // now is a param of the law only (ours); the step never reads it.
  const js = window.compiled(), params = window.encodeParams({w: 60, c: 5, now: 0})
  let st = js.init(params), x = 42, t = 0
  for (let i = 0; i < n; i++) {
    x = lcg(x)
    t += x % 3
    const input = {forced: x % 10 === 0 ? 1 : 0, t}
    if (i === 0) same(input, window.encodeInput({forced: x % 10 === 0, t}))
    st = js.step(params, st, input)
  }
  const log = st.history!.slice(st.head ?? 0)
  let forced = 0, ts = 0
  for (const r of log) { forced += r.forced!; ts += r.t! }
  console.log(`${log.length} ${forced} ${ts}`)
} else {
  console.error('usage: bun compare/bench/gdpwired.ts budget|caps|window <N>')
  process.exit(2)
}
