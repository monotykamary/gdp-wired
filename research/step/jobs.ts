// The experiment's jobs files: `bun research/step/jobs.ts <kind> [--ms 55000] [--env K=V ...] > jobs.json`, then
// `supercomputer run --jobs jobs.json --out runs/step/<kind>`. (Its runs were made by the retired Modal runner,
// modal_step.py, in git history; /goals, /goals223, /chc and /data were Modal volumes: nothing provides them on a box yet.)
//   goals332   goal.ts on each of research/dag's 332 dumped step goals (/goals/<task>/goal.json)
//   goals223   goal.ts on each table step goal dumped by `table` (/goals223/<task>/goal.json)
//   table      research/table/chc.ts --kernel on the 223 tasks chc-kernel handed to the kernel, its model kept and its
//              step goal dumped (research/dag/given-dump.ts with that model)
//   given223   compare/chc/prof/given.ts on each of the 223 with the model `table` kept (/goals223/<task>/model.json)
//   given332   compare/chc/prof/given.ts on each of the 332 with Spacer's model (compare/chc/prof/given-models.json)
// A job's files (table's model.json and dumped goal) go to $SUPERCOMPUTER_OUTPUT_DIR.
import {existsSync, readFileSync, readdirSync} from 'node:fs'
import {join} from 'node:path'

const gdp = join(import.meta.dir, '../..')
const args = process.argv.slice(2), kind = args[0]
const opt = (k: string, d: string) => { const i = args.indexOf(k); return i < 0 ? d : args[i + 1]! }
const json = <T>(f: string): T => JSON.parse(readFileSync(f, 'utf8'))
const safe = (task: string) => task.replace(/\.yml$/, '').replaceAll('/', '__')
const ms = opt('--ms', '55000')
const env = args.flatMap((x, i) => (x === '--env' ? [args[i + 1]!] : [])).join(' ')
const pre = env ? `export ${env}; ` : ''
const tasks332 = () => json<string[]>(join(gdp, 'research/dag/step332-tasks.json'))
const goals223 = () => { const d = join(gdp, 'runs/step/goals223'); return readdirSync(d).sort().map(n => ({name: n, dir: join(d, n)})) }

type Job = {name: string; cmd: string; timeout: number; image?: string}
const jobs: Job[] = []
if (kind === 'goals332') {
  for (const t of tasks332())
    jobs.push({name: safe(t), timeout: Math.floor(Number(ms) / 1000) + 120, cmd: `${pre}bun research/step/goal.ts /goals/${safe(t)}/goal.json --ms ${ms}`})
} else if (kind === 'goals223') {
  for (const d of goals223())
    if (existsSync(join(d.dir, 'goal.json')))
      jobs.push({name: d.name, timeout: Math.floor(Number(ms) / 1000) + 120, cmd: `${pre}bun research/step/goal.ts /goals223/${d.name}/goal.json --ms ${ms}`})
} else if (kind === 'given223') {
  for (const d of goals223()) {
    if (!existsSync(join(d.dir, 'model.json'))) continue
    const smt2 = Object.keys(json<Record<string, unknown>>(join(d.dir, 'model.json')))[0]
    jobs.push({name: d.name, timeout: 180, cmd: `${pre}bun compare/chc/prof/given.ts ${smt2} /goals223/${d.name}/model.json --ms 55000`})
  }
} else if (kind === 'table') {
  const rows = readFileSync(join(gdp, '../gdp-wired/runs/modal/table/chc-kernel/results.jsonl'), 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l) as {name: string; out: string})
  for (const r of rows) {
    const outs = r.out.trim().split('\n').filter(x => x.startsWith('{')).map(x => JSON.parse(x) as {stage?: string; kernel?: string})
    const k = outs.find(x => x.stage === 'result')?.kernel
    if (!k || k.includes('skipped')) continue
    const t = r.name, y = `/chc/${t}`, o = '"$SUPERCOMPUTER_OUTPUT_DIR"'
    // chc.ts --kernel writes the table's kept relations as a model at /tmp/table-model.json, keyed by the .smt2 path;
    // given-dump.ts then dumps the step goal the prover stops on with that model.
    const cmd = `${pre}f=$(dirname ${y})/$(sed -n 's/^input_files:[[:space:]]*//p' ${y} | head -1); ` +
      `bun research/table/chc.ts "$f" --task '${t}' --model /data/spacer-models.jsonl --kernel; ` +
      `[ -f /tmp/table-model.json ] && cp /tmp/table-model.json ${o}/model.json && ` +
      `bun research/dag/given-dump.ts "$f" /tmp/table-model.json --key "$f" --ms 55000 --out ${o}`
    jobs.push({name: safe(t), timeout: 900, cmd})
  }
} else if (kind === 'given332') {
  for (const t of tasks332()) jobs.push({name: safe(t), timeout: 180, cmd: `${pre}bun research/step/given332.ts '${t}'`})
} else {
  console.error('usage: bun research/step/jobs.ts goals332|goals223|table|given223|given332 [--ms 55000] [--env K=V ...]')
  process.exit(2)
}
for (const j of jobs) j.image = 'chc' // (the goals, the benchmarks and Spacer's models are the chc image's)
console.log(JSON.stringify(jobs, null, 0).replaceAll('},{', '},\n{'))
