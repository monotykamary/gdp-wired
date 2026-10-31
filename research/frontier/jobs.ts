// Modal jobs for the corpus, one per item and prover (`bun research/frontier/jobs.ts [--track t] > jobs.json`), each a
// `score.ts --one` run: `modal run supercomputer/run.py --jobs jobs.json --out runs/modal/frontier/<name>`, then
// `bun research/frontier/score.ts --from runs/modal/frontier/<name>` for the table.
import {corpus} from './corpus.ts'

const i = process.argv.indexOf('--track'), track = i < 0 ? undefined : process.argv[i + 1]
const q = (s: string) => `'${s.replace(/'/g, `'\\''`)}'`
const jobs = corpus.filter(it => !track || it.track === track).flatMap((it, k) => (['today', ...(it.frontier ? ['frontier'] : [])] as const).map(how => ({
  // A datatype law's search runs within its own two minutes (core/data.ts's proveData), on two CPUs.
  name: `${k}-${how}`, cmd: `bun install --frozen-lockfile >/dev/null 2>&1; echo ${q(it.id)}; timeout ${it.track === 'datatype' ? 180 : 120} bun research/frontier/score.ts --one ${q(it.id)} ${how} 2>&1`, cpu: it.track === 'datatype' ? 2.0 : 1.0, timeout: 300,
})))
console.log(JSON.stringify(jobs, null, 1))
