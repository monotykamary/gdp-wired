// One task's proveRule, timed by phase: `bun compare/chc/prof/prove.ts <task.smt2>` (PROVE_TRACE=1 for each goal).
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build} from '../translate.ts'
import {proveRule} from '../../../core/dsl.ts'
import {profile} from '../../../kernel/prove.ts'
profile.on = true
const t0 = performance.now()
const b = build(parseChc(readFileSync(process.argv[2]!, 'utf8')))
void b.rule.machine
const t1 = performance.now()
const v = proveRule(b.rule, [b.law])
const t2 = performance.now()
console.log(JSON.stringify({goals: profile.goals.map(g => ({...g, ms: Math.round(g.ms), solveMs: Math.round(g.solveMs), rowsMs: Math.round(g.rowsMs)}))}))
console.log(JSON.stringify({task: process.argv[2], buildMs: Math.round(t1 - t0), proveMs: Math.round(t2 - t1), proven: v.proven, goal: v.goal, stuck: v.stuck, why: v.why}))
