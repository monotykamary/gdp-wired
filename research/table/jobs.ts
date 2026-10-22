// The experiment's Modal jobs: `bun research/table/jobs.ts chc [--only a|b] [--name chc]` writes research/table/jobs/<name>.json.
//   chc    the 536 tasks Spacer answers sat and gdp-wired 0.20.0 doesn't (runs/modal/chc2/gap-v020.json), one job each
//   term   the ITS tasks another tool proves terminating and gdp-wired doesn't (compare/term/failures.ts's list, given as
//          --tasks <file>, one name a line), one job each, with KoAT2's proof run in the same container
//   sv     the same for SV-COMP's termination tasks (c2ari.py's translation first)
//   tip    the 27 TIP problems of compare/tip/lemmas-sample30.json that have lemmas
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs'

const args = process.argv.slice(2), kind = args[0]!
const opt = (k: string, d: string) => { const i = args.indexOf(k); return i < 0 ? d : args[i + 1]! }
const only = opt('--only', ''), name = opt('--name', kind), extra = opt('--args', '')
const pick = (xs: string[]) => (only ? xs.filter(x => only.split('|').some(o => x.includes(o))) : xs)
const sh = (s: string) => `'${s.replace(/'/g, `'\\''`)}'`
let jobs: {name: string, cmd: string, timeout?: number}[] = []
if (kind === 'chc') {
  const gap = JSON.parse(readFileSync('runs/modal/chc2/gap-v020.json', 'utf8')) as Record<string, {kind: string}>
  const tasks = pick(Object.keys(gap).filter(t => gap[t]!.kind === 'sat'))
  jobs = tasks.map(t => ({name: t, timeout: 560, cmd: `y=/chc/${sh(t)}; f=$(dirname "$y")/$(sed -n 's/^input_files:[[:space:]]*//p' "$y" | head -1); bun research/table/chc.ts "$f" --task ${sh(t)} --model /data/spacer-models.jsonl ${extra}`}))
} else if (kind === 'term' || kind === 'sv') {
  const tasks = pick(readFileSync(opt('--tasks', ''), 'utf8').split('\n').map(s => s.trim()).filter(Boolean))
  jobs = tasks.map(t => ({name: t, timeout: 300, cmd: `bun research/table/term.ts ${sh(t)} --${kind} ${extra}`}))
} else if (kind === 'tip') {
  const lem = JSON.parse(readFileSync('compare/tip/lemmas-sample30.json', 'utf8')) as Record<string, string[]>
  jobs = pick(Object.keys(lem)).map(t => ({name: t, timeout: 900, cmd: `bun research/table/tip.ts /tip/benchmarks/${sh(t)} --lemmas compare/tip/lemmas-sample30.json --task ${sh(t)} ${extra}`}))
} else throw new Error(`kind ${kind}`)
mkdirSync('research/table/jobs', {recursive: true})
writeFileSync(`research/table/jobs/${name}.json`, JSON.stringify(jobs, null, 1) + '\n')
console.log(`${jobs.length} jobs → research/table/jobs/${name}.json`)
