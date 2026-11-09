// Section 17 trace: one frozen-family helper × operation × counted pass, every countsDump event as one line (`S17 {...}`,
// heavy fields reduced to sizes), the counted clock, wall and RSS at each, and the attempt's end (`S17_END`). Research
// only: no proof is produced, nothing is admitted. Runs unchanged on the frozen 15eff72f tree and on this one.
import {readFileSync} from 'node:fs'
import {all, same, x, n, type Law, type Machine} from '../../core/machine.ts'
import {countedAttempts, countsDump} from '../../core/counts.ts'
import {finiteCountChoice} from '../../core/count-cases.ts'
import {clock, counted, fullRate, fullWork, withWall} from '../../kernel/prove.ts'
const [file, tag, opText, passText, wallText = '60000', budgetText = '1e12'] = process.argv.slice(2)
const p = JSON.parse(readFileSync(file!, 'utf8')), op = Number(opText), pass = Number(passText) as 0 | 1, wallMs = Number(wallText), budget = Number(budgetText)
const choice = finiteCountChoice(p.m)
if (!choice || !choice[1].has(op)) throw Error('operation not present')
const law: Law = p.laws[p.targets[tag!]]
if (!law) throw Error('missing target')
const m: Machine = {...p.m, assume: all(...(p.m.assume ? [p.m.assume] : []), same(x(choice[0]), n(op)))}
const t0 = performance.now(), w0 = fullWork()
let seq = 0
const sizeOf = (v: unknown): unknown => Array.isArray(v) ? v.length : v && typeof v === 'object' ? Object.fromEntries(Object.entries(v as object).map(([k, u]) => [k, Array.isArray(u) ? u.length : typeof u === 'object' && u ? '{…}' : u])) : v
countsDump.on = e => {
  const r = e as Record<string, unknown>, out: Record<string, unknown> = {seq: ++seq, ms: Math.round(performance.now() - t0), units: Math.round((fullWork() - w0) / fullRate), rssMiB: Math.round(process.memoryUsage().rss / 1048576)}
  for (const [k, v] of Object.entries(r)) {
    if (k === 'machine' || k === 'laws' || k === 'rawGoal' || k === 'certificateRequest' || k === 'proof' || k === 'decls' || k === 'ls') continue
    if (k === 'hyps' || k === 'instances' || k === 'reads' || k === 'at') { out[k] = sizeOf(v); continue }
    if (k === 'completion') { const c = v as Record<string, unknown>; out.completion = {genuine: c.genuine, keys: Object.keys(c)}; continue }
    if (k === 'goal' && typeof v !== 'string') { out.goal = sizeOf(v); continue }
    out[k] = v
  }
  console.log('S17 ' + JSON.stringify(out))
}
let result: Record<string, unknown> | undefined, error: string | undefined
try {
  counted(fullRate, () => withWall(t0 + wallMs, () => {
    const until = clock() + budget, a = countedAttempts(m, p.caller.map((i: number) => p.laws[i]), new Set(p.support.map((i: number) => p.laws[i])), until) as {houdini?: boolean, traced: (law: Law, ls: Law[], pass: 0 | 1, ms: number) => Record<string, unknown>}
    a.houdini = true
    result = a.traced(law, p.laws, pass, budget)
  }))
} catch (e) { error = String(e) }
console.log('S17_END ' + JSON.stringify({tag, op, pass, law: law.name, ms: Math.round(performance.now() - t0), units: Math.round((fullWork() - w0) / fullRate), rssMiB: Math.round(process.memoryUsage().rss / 1048576), events: seq,
  result: result && ('proof' in result ? 'proof' : {stuck: result.stuck, why: result.why, refuted: result.refuted}), error}))
