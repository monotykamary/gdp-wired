// The real-world corpus as a job list, one job per law, each a `score.ts --one` run in a container of its own (2
// vCPU): `bun research/realworld/jobs.ts [--domain d] [--item id] > jobs.json`, then `python3 supercomputer/run.py --backend
// modal --jobs jobs.json --out runs/realworld/<name>` and `bun research/realworld/score.ts --from runs/realworld/<name>`.
// Each law's search has 60 s; the run is killed at 150 s (a killed run reads as a timeout).
import {corpus} from './corpus.ts'

const arg = (k: string) => { const i = process.argv.indexOf(k); return i < 0 ? undefined : process.argv[i + 1] }
const domain = arg('--domain'), item = arg('--item')
const q = (s: string) => `'${s.replace(/'/g, `'\\''`)}'`
const slug = (s: string) => s.replace(/[^A-Za-z0-9]+/g, '-').replace(/^-|-$/g, '').toLowerCase()
const jobs = corpus.filter(it => (!domain || it.domain === domain) && (!item || it.id === item)).flatMap(it => it.laws.map((_, k) => ({
  name: `${slug(it.id)}-${k}`,
  cmd: `bun install --frozen-lockfile >/dev/null 2>&1; echo ${q(`${it.id}#${k}`)}; timeout -s KILL 150 bun research/realworld/score.ts --one ${q(it.id)} ${k} --ms 60000 2>&1 | tail -1`,
  cpu: 2.0, timeout: 300,
})))
console.log(JSON.stringify(jobs, null, 1))
