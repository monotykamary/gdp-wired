// The jobs (supercomputer's format) for run.ts: one a protocol, a run and a budget, the search's phases kept. Each on a
// boat VM of one type, `default` (4 vCPUs, 2 pinned to the job; never xlarge), as a competition fixes its hardware: the
// same counted work ran 2-3x slower on large and xlarge VMs (../engine/DESIGN.md, gen/laneY5). Run them with --timing
// (each job alone on its VM).
//   bun research/protocols/ic3syn/jobs.ts --ms 60000 --runs 2 [--only id,id] [--skip broken] [--vm default] > jobs.json
import {protocols} from './models.ts'

const arg = (name: string) => { const i = process.argv.indexOf(`--${name}`); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('ms') ?? 60_000), runs = Number(arg('runs') ?? 1), only = arg('only')?.split(','), skip = arg('skip') ?? 'broken'
const wall = Math.round(ms / 1000 * 2.5 + 60), vm = arg('vm') ?? 'default'
const phases = "'small instance|join (enumerated|end|failed|exists|set|cone|td|houdini|engine|ic3|undecided|pool|filter)'"
console.log(JSON.stringify(protocols.filter(p => !only || only.includes(p.id)).flatMap(p => Array.from({length: runs}, (_, i) => ({
  name: `${p.id.replace('@', '_at_')}-s${ms / 1000}-r${i + 1}`,
  cmd: `GDP_INFER_TRACE=2 timeout -s KILL ${wall} bun research/protocols/ic3syn/run.ts --ms ${ms} --only '${p.id}' --skip ${skip} 2>/tmp/err.log; s=$?; grep -E ${phases} /tmp/err.log | cut -c1-300 | tail -c 60000; tail -c 2000 /tmp/err.log | grep -iE 'error|throw' | tail -5; exit $s`,
  timeout: wall + 60,
  vm_type: vm,
}))), null, 1))
