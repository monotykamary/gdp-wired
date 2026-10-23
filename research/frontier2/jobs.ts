// The second corpus as a job list, one job per item and prover, each a `score.ts --one` run in a container of its own
// (2 vCPU, as the benchmark runs): `bun research/frontier2/jobs.ts [--track t] > jobs.json`, then
// `python3 modal/run.py --jobs jobs.json --out runs/corpus2/<name>` and `bun research/frontier2/score.ts --from
// runs/corpus2/<name>` for the table. Each run is killed at 200 s (the searches stop by themselves within about 60 s of
// counted work, the benchmark's limit); a killed run reads as a timeout.
import {corpus} from './corpus.ts'

const i = process.argv.indexOf('--track'), track = i < 0 ? undefined : process.argv[i + 1]
const q = (s: string) => `'${s.replace(/'/g, `'\\''`)}'`
const jobs = corpus.filter(it => !track || it.track === track).flatMap((it, k) => (['today', ...(it.frontier ? ['frontier'] : [])] as const).map(how => ({
  name: `${k}-${how}`, cmd: `bun install --frozen-lockfile >/dev/null 2>&1; echo ${q(it.id)}; timeout -s KILL 200 bun research/frontier2/score.ts --one ${q(it.id)} ${how} 2>&1`, cpu: 2.0, timeout: 300,
})))
console.log(JSON.stringify(jobs, null, 1))
