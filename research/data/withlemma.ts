// Debugging: a law of examples/data.ts with lemmas given (never what the corpus does): bun research/data/withlemma.ts <law>
import {laws} from '../../examples/data.ts'
import {proveData, type DataLaw} from '../../core/data.ts'
import {given} from './given.ts'
const name = process.argv[2]!
const v = proveData((laws as Record<string, () => DataLaw>)[name]!(), {lemmas: given[name], ms: Number(process.argv[3] ?? 60000)})
console.log(JSON.stringify({proven: v.proven, ms: v.ms, scheme: v.scheme, lemmas: v.lemmas, goal: v.goal, stuck: v.stuck}))
