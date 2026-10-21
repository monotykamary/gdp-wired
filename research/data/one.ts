// One law of examples/data.ts through proveData, lemmas and all: bun research/data/one.ts <law> [ms]
import {laws, broken} from '../../examples/data.ts'
import {proveData, type DataLaw} from '../../core/data.ts'
const name = process.argv[2]!, isBroken = name.endsWith('!')
const l = ((isBroken ? broken : laws) as Record<string, () => DataLaw>)[name.replace(/!$/, '')]!()
const v = proveData(l, {ms: Number(process.argv[3] ?? 60000)})
console.log(JSON.stringify({law: v.law, proven: v.proven, checked: v.checked, ms: v.ms, scheme: v.scheme, lemmas: v.lemmas, tried: v.tried, counterexample: v.counterexample, goal: v.goal, stuck: v.stuck}))
