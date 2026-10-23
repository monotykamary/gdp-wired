// A forced run's speed and checkDerivation's on it: `bun research/bmc2/forced.ts <task.smt2> <steps> <ms>`
import {readFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import {forcedRun} from '../../core/bmc.ts'
const b = build(parseChc(readFileSync(process.argv[2]!, 'utf8')))
const t0 = performance.now()
const r = forcedRun(b.rule.machine, [b.law], {steps: Number(process.argv[3]), wall: performance.now() + Number(process.argv[4])})
console.log('forced', Math.round(performance.now() - t0), r?.depth)
