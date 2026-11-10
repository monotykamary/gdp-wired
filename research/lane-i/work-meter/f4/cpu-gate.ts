import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {cpus} from 'node:os'
const id = process.argv[2]!
const first: Record<string, string> = JSON.parse(readFileSync('cross-input/first-cpu.json', 'utf8'))
assert(Object.hasOwn(first, id), 'audited first CPU required')
const cpu = cpus()[0]?.model
assert(cpu, 'CPU model required')
const selected = cpu !== first[id]
console.log('RAW_CENSUS_CPU_GATE ' + JSON.stringify({id, cpu, firstCpu: first[id], selected, scope: 'placement check only; no solver ran yet'}))
// A placement miss, not a proof failure or unknown result. Do not run a duplicate.
if (!selected) process.exit(75)
