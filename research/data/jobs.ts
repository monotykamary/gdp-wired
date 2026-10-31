// A Modal job list (supercomputer/run.py) for the datatype laws: one job per law of examples/data.ts through research/data/prof.ts,
// each broken variant too, and the extra cells given: bun research/data/jobs.ts [extra.json] > jobs.json
import {readFileSync} from 'node:fs'
import {broken, laws} from '../../examples/data.ts'
const extra = process.argv[2] ? JSON.parse(readFileSync(process.argv[2], 'utf8')) as object[] : []
const env = process.env.JOB_ENV ? `${process.env.JOB_ENV} ` : ''
console.log(JSON.stringify([
  ...Object.keys(laws).map(n => ({name: `law-${n}`, cmd: `${env}bun research/data/prof.ts ${n} 2>&1 | tail -60`, cpu: 2.0, timeout: 600})),
  ...Object.keys(broken).map(n => ({name: `broken-${n}`, cmd: `${env}bun research/data/prof.ts '${n}!' 2>&1 | tail -20`, cpu: 2.0, timeout: 600})),
  ...extra,
], null, 1))
