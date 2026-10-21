// A job list for modal/run.py from the suite's, each job's command under environment settings and its name prefixed:
// `bun research/cyclic/jobs.ts <out.json> [--env 'GDP_CYCLIC_ROUTE=both GDP_CYCLIC_LAX=1'] [--prefix x-] [--only a,b]`.
import {readFileSync, writeFileSync} from 'node:fs'
const arg = (flag: string) => (process.argv.includes(flag) ? process.argv[process.argv.indexOf(flag) + 1]! : undefined)
const out = process.argv[2]!, env = arg('--env'), prefix = arg('--prefix') ?? '', only = arg('--only')?.split(',')
const jobs = (JSON.parse(readFileSync(new URL('../../modal/suite.json', import.meta.url), 'utf8')) as {name: string, cmd: string}[])
  .filter(j => !only || only.includes(j.name)).map(j => ({...j, name: `${prefix}${j.name}`, cmd: env ? `export ${env}; ${j.cmd}` : j.cmd}))
writeFileSync(out, JSON.stringify(jobs, null, 1))
console.log(`${jobs.length} jobs to ${out}`)
