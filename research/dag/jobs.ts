// The experiment's jobs files: `bun research/dag/jobs.ts <kind> [--sample names.json] [--goals dir] > jobs.json`, then
// `supercomputer run --jobs jobs.json --out runs/dag/<kind>`. (The dump g332 reads was made by the retired Modal runner,
// modal_dag.py, in git history; its inputs, /bench and /goals, were Modal volumes: nothing provides them on a box yet.)
//   dump      given-dump.ts on each of the 332 step-goal tasks (step332-tasks.json), the same 55 s as given.ts had
//   solvers   z3 and cvc5 on each dumped goal.smt2 (<goals>/<task>/), 60 s, one (solver, task) a job
//   profile   profile.ts (the tree search, instrumented) on each dumped goal.json [--ms 55000]
//   dag       dag.ts (the DAG search) on each dumped goal.json, its certificate checked by check-dag.ts [--no-learn]
//   cdcl      cdcl.ts (CDCL over the atoms, the same certificate) likewise [--no-bounds]
//   vars      vars.ts (the goal's variables by class, and the reading with every yes/no and finite value fixed)
//   items     items.ts on each example the test script runs (the tree against the DAG on the library's own goals)
//   bmc       bmc.ts on each unsat Lustre task with a Golem derivation (bmc-tasks.json), k = 1..10
// A job's files (dump's goal.json and goal.smt2, profile's and dag's reports) go to $SUPERCOMPUTER_OUTPUT_DIR.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'

const here = import.meta.dir
const args = process.argv.slice(2), kind = args[0]
const opt = (k: string, d: string) => { const i = args.indexOf(k); return i < 0 ? d : args[i + 1]! }
const json = <T>(f: string): T => JSON.parse(readFileSync(f, 'utf8'))
const safe = (task: string) => task.replace(/\.yml$/, '').replaceAll('/', '__')
const out = '"$SUPERCOMPUTER_OUTPUT_DIR"'
const goals = opt('--goals', '/goals')
const names: string[] = args.includes('--sample') ? json(opt('--sample', '')) : json(join(here, 'step332-tasks.json'))

type Job = {name: string; cmd: string; timeout: number; image?: string}
const jobs: Job[] = []
if (kind === 'dump') {
  const byTask = new Map(json<{task: string; smt2: string}[]>(join(here, '../../runs/modal/chc2/given-spacer3/tasks.json')).map(t => [t.task, t]))
  for (const t of names)
    jobs.push({name: safe(t), timeout: 90, cmd: `bun research/dag/given-dump.ts /bench/${byTask.get(t)!.smt2} compare/chc/prof/given-models.json --ms 55000 --out ${out}`})
} else if (kind === 'solvers') {
  for (const t of names) {
    const g = `${goals}/${safe(t)}/goal.smt2`
    // (the job's seconds are the solver's wall time: nothing else runs in the command)
    jobs.push({name: `z3__${safe(t)}`, timeout: 75, cmd: `timeout 60 z3 -smt2 ${g}; echo exit=$?`})
    jobs.push({name: `cvc5__${safe(t)}`, timeout: 75, cmd: `timeout 60 cvc5 ${g}; echo exit=$?`})
  }
} else if (kind === 'profile' || kind === 'dag' || kind === 'cdcl') {
  const ms = opt('--ms', '55000')
  const flags = args.filter(x => x.startsWith('--no-')).join(' ')
  for (const t of names)
    jobs.push({name: safe(t), timeout: Math.floor(Number(ms) / 1000) + 60, cmd: `bun research/dag/${kind}.ts ${goals}/${safe(t)}/goal.json --ms ${ms} --out ${out} ${flags}`.trim()})
} else if (kind === 'vars') {
  for (const t of names) jobs.push({name: safe(t), timeout: 120, cmd: `bun research/dag/vars.ts ${goals}/${safe(t)}/goal.json`})
} else if (kind === 'items') {
  const examples = 'readme guide composition sets quantifiers functions datatypes lemmas discover invoices folds trees pairs groups charts xstate infer cyclic cycles data scopes lists sizes liveness budget gdp steps'
  for (const x of examples.split(' ')) jobs.push({name: x, timeout: 1800, cmd: `bun research/dag/items.ts examples/${x}.ts --max 200 --ms 3000`})
} else if (kind === 'bmc') {
  for (const t of json<{task: string; smt2: string}[]>(join(here, 'bmc-tasks.json')))
    jobs.push({name: safe(t.task), timeout: 300, cmd: `bun research/dag/bmc.ts /bench/${t.smt2} --k 10 --ms 240000`})
} else {
  console.error('usage: bun research/dag/jobs.ts dump|solvers|profile|dag|cdcl|vars|items|bmc [--sample names.json] [--goals dir] [--ms n] [--no-...]')
  process.exit(2)
}
// (every job but items' reads the chc image's benchmarks or goals)
for (const j of jobs) if (kind !== 'items') j.image = 'chc'
console.log(JSON.stringify(jobs, null, 0).replaceAll('},{', '},\n{'))
