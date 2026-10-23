// A CHC task's bounded run written out as a derivation, and checked again: `bun research/bmc2/derivation.ts <task.smt2>
// <out.json.gz> [--ms 15000]`. The run core/bmc.ts finds (as solve.ts's bmc stage asks it), each step's clause and request
// values (the clause's free variables, Int as integers), the predicate's arguments after each step, and the verdict of
// compare/chc/translate.ts's checkDerivation (which evaluates each clause on the values with no gdp-wired code).
import {readFileSync, writeFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {type Step, build, checkDerivation} from '../../compare/chc/translate.ts'
import {findBoundedRun} from '../../core/bmc.ts'

const [file, out] = process.argv.slice(2), i = process.argv.indexOf('--ms'), ms = i < 0 ? 15000 : Number(process.argv[i + 1])
const chc = parseChc(readFileSync(file!, 'utf8')), b = build(chc), r = b.rule, g = r.compiled()
const found = findBoundedRun(r.machine, [b.law], {ms, wall: performance.now() + ms})
if (!found) { console.log(JSON.stringify({task: file, found: false})); process.exit(1) }
const raws = found.trace.map(t => {
  const o: Record<string, number | boolean | string> = {c: b.clauseNames[t.c as number]!}
  for (let k = 0; k < b.inInt; k++) o[`x${k}`] = (t[`x${k}`] as number) - (t[`x${k}$neg`] as number)
  for (let k = 0; k < b.inBool; k++) o[`y${k}`] = t[`y${k}`] === 1
  return o
})
let st = g.init({})
const steps: Step[] = []
for (const raw of raws) {
  const before = r.decode(st), next = g.step({}, st, r.encodeInput(raw as never))
  steps.push({clause: Number(String(raw.c).slice(1)), input: raw, before, after: r.decode(next)})
  st = next
}
const bad = checkDerivation(b, chc, steps)
const args = (s: Record<string, unknown>) => ({loc: s.loc, ...Object.fromEntries(Array.from({length: b.nInt}, (_, k) => [`i${k}`, s[`i${k}`]])), ...Object.fromEntries(Array.from({length: b.nBool}, (_, k) => [`b${k}`, s[`b${k}`]]))})
const doc = {task: file!.split('/').slice(-2).join('/'), predicates: b.predNames, clauses: b.clauseNames.length, steps: steps.length,
  checkDerivation: bad ?? 'confirmed', derivation: steps.map(s => ({clause: s.clause, input: s.input, after: args(s.after)}))}
writeFileSync(out!, Bun.gzipSync(new TextEncoder().encode(JSON.stringify(doc))))
console.log(JSON.stringify({task: doc.task, steps: doc.steps, checkDerivation: doc.checkDerivation, last: doc.derivation.slice(-2)}))
