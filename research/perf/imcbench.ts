// IMC's search on one CHC task, on the counted clock alone (no wall stop), so the search is the same on any machine
// and from one build to another that keeps its decisions: `bun research/perf/imcbench.ts <task.smt2> [--ms 40000]`.
// Prints one line: the outcome, the wall ms, the cost model's work and every counter (core/solver.ts's costs, work.n),
// the line two builds must agree on but for `ms` where a change to the search's code keeps its path.
import {readFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import {prepare} from '../../compare/chc/compose.ts'
import {imcSearch} from '../../core/interp.ts'
import {clock, counted, fullRate, fullWork} from '../../kernel/prove.ts'
import {costs, work} from '../../core/solver.ts'

const file = process.argv[2]!, i = process.argv.indexOf('--ms'), ms = i < 0 ? 40_000 : Number(process.argv[i + 1])
const chc = parseChc(readFileSync(file, 'utf8')), cc = prepare(chc, {slice: false, chains: true})
const b = cc ? build(cc.chc) : build(chc), m = b.rule.machine
const depths: [number, string][] = []
const is = imcSearch(m, b.law, {kinds: b.rule.kindLaws().map(l => l.holds), induction: false, progress: (k, what) => { depths.push([k, what[0]!]) }})
const t0 = performance.now()
const out = counted(fullRate, () => is.run(clock() + ms, undefined), true)
const wall = Math.round(performance.now() - t0)
const res = out === 'paused' ? 'paused' : 'inv' in out ? `inv k=${out.k}` : 'run' in out ? `run k=${out.k}` : 'kinductive' in out ? `kinductive ${out.kinductive}` : `over k=${out.k} ${'why' in out ? out.why.slice(0, 60) : ''}`
console.log(JSON.stringify({task: file.split('/').slice(-2).join('/'), res, ms: wall, fullWork: Math.round(fullWork()), workN: work.n, depths: depths.length, lastDepth: depths.at(-1), costs}))
