// The caps rule (core/models.ts, the grant decided once per step) through compileJs at growing request counts, beside
// the interpreter: the generated step updates its maps in place, so its time grows with the requests, not with their
// square (the interpreter copies its maps each step). Requests from a fixed LCG; the answer is the number of grants.
//   bun grant-scale.ts
import {compileJs, interpret} from '../core/machine.ts'
import {admitFlagged} from '../core/models.ts'

const lcg = (s: number) => (Math.imul(s, 1103515245) + 12345) >>> 0
function requests(count: number) {
  const reqs: {acct: number, day: number, hour: number, dom: number, ok: number}[] = []
  const mods = [count + 1, Math.floor(count / 50) + 1, Math.floor(count / 10) + 1, Math.floor(count / 20) + 1]
  let s = 7
  for (let i = 0; i < count; i++) {
    const f: number[] = []
    for (let j = 0; j < 4; j++) { s = lcg(s); f.push((s >>> 8) % mods[j]!) }
    s = lcg(s)
    reqs.push({acct: f[0]!, day: f[1]!, hour: f[2]!, dom: f[3]!, ok: (s >>> 8) % 4 !== 0 ? 1 : 0})
  }
  return reqs.reverse()
}
const P = {d: 20, hr: 5, dm: 10}
const gen = new Function(`${compileJs(admitFlagged()).replace(/^export function/gm, 'function')}\nreturn {init, step}`)()
const run = interpret(admitFlagged())
const grants = (st: any) => { let g = 0; for (const v of st.maps.Acct.values()) g += v; return g }
const median = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)]!
const time = (f: () => number, reps: number) => { let answer = f(); const ts: number[] = []; for (let i = 0; i < reps; i++) { const t = performance.now(); answer = f(); ts.push(performance.now() - t) } return {ms: Math.round(median(ts) * 10) / 10, answer} }
for (const count of [1000, 10_000, 100_000, 1_000_000]) {
  const reqs = requests(count)
  const compiled = time(() => { let st = gen.init(P); for (const r of reqs) st = gen.step(P, st, r); return grants(st) }, 5)
  const interpreted = count <= 10_000 ? time(() => { let st = run.init(P); for (const r of reqs) st = run.step(P, st, r); return grants(st) }, 3) : undefined
  console.log(JSON.stringify({requests: count, compiled, interpreted, agree: interpreted === undefined || interpreted.answer === compiled.answer}))
}
