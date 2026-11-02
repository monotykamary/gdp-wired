// The jobs (supercomputer's format) for run.ts: one protocol and run per isolated large VM.
//   bun research/protocols/ic3syn/jobs.ts --ms 60000 --runs 3 [--only id,id] [--skip broken]
//   bun research/protocols/ic3syn/jobs.ts --paired base --runs 3 [--suite duoai]
// --paired is a baseline directory shipped with --data DIR:base. Each side gets its own strict wall limit;
// alternate the order by run, never compare different VMs. Installation is outside the measured interval.
import {protocols} from './models.ts'
import {protocols as duoai} from '../models.ts'

const arg = (name: string) => { const i = process.argv.indexOf(`--${name}`); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('ms') ?? 60_000), runs = Number(arg('runs') ?? 1), only = arg('only')?.split(','), skip = arg('skip') ?? 'broken'
const paired = arg('paired'), suite = arg('suite') ?? 'ic3syn', vm = arg('vm') ?? 'large'
if (!(Number.isSafeInteger(ms) && ms > 0 && Number.isSafeInteger(runs) && runs > 0)) throw new Error('positive integer --ms and --runs required')
if (!['ic3syn', 'duoai'].includes(suite)) throw new Error('--suite ic3syn|duoai')
const script = suite === 'duoai' ? 'research/protocols/run.ts' : 'research/protocols/ic3syn/run.ts'
const skipped = suite === 'duoai' ? [...new Set([...skip.split(','), 'given'])].join(',') : skip
const wall = Math.round(ms / 1000 * 2.5 + 60)
const phases = "'small instance|join (enumerated|end|failed|exists|set|cone|td|houdini|engine|ic3|undecided|pool|filter)'"
const quote = (s: string) => `'${s.replaceAll("'", "'\\''")}'`
const chosen = (suite === 'duoai' ? duoai : protocols).filter(p => !only || only.includes(p.id))
const jobs = chosen.flatMap(p => Array.from({length: runs}, (_, i) => {
  const run = `bun ${script} --ms ${ms} --only ${quote(p.id)} --skip ${quote(skipped)}`
  const name = `${p.id.replace('@', '_at_')}-s${ms / 1000}-r${i + 1}`
  if (!paired) return {name, cmd: `GDP_INFER_TRACE=2 timeout -s KILL ${wall} ${run} 2>/tmp/err.log; s=$?; grep -E ${phases} /tmp/err.log | cut -c1-300 | tail -c 60000; tail -c 2000 /tmp/err.log | grep -iE 'error|throw' | tail -5; exit $s`, timeout: wall + 60, vm_type: vm, cpu: 4, memory: 14336}
  const cmd = `set -e; root=$PWD; base=$(cd ${quote(paired)} && pwd); bun install --frozen-lockfile >/dev/null 2>&1; (cd "$base" && bun install --frozen-lockfile >/dev/null 2>&1); set +e; failed=0; for side in ${i % 2 ? 'base cand' : 'cand base'}; do dir=$root; [ "$side" = base ] && dir=$base; echo "PAIR begin side=$side id=${p.id} run=${i + 1}"; (cd "$dir" && GDP_INFER_TRACE=2 timeout -s KILL ${ms / 1000} ${run}) > /tmp/pair-$side.out 2>/tmp/pair-$side.err; s=$?; cat /tmp/pair-$side.out; grep -E ${phases} /tmp/pair-$side.err | cut -c1-300 | tail -c 60000; tail -c 2000 /tmp/pair-$side.err | grep -iE 'error|throw' | tail -5; echo "PAIR end side=$side exit=$s"; if [ $s -ne 0 ] && [ $s -ne 124 ] && [ $s -ne 137 ]; then failed=1; fi; done; exit $failed`
  return {name, cmd, timeout: Math.ceil(ms / 1000) * 2 + 180, vm_type: vm, cpu: 4, memory: 14336}
}))
console.log(JSON.stringify(jobs, null, 1))
