// One dumped step goal (research/dag/goalio.ts's JSON) given to the library's prover as it ships: `bun
// research/step/goal.ts <goal.json> [--ms 55000] [--search grow|cdcl]` (cdcl: kernel/cdcl.ts's search alone). kernel/prove.ts's grow with its own budget (a second a hypothesis, at
// least 20 s) within --ms, as research/dag/profile.ts gives the tree search; a tree found is checked by kernel.ts's
// check. Prints one JSON line: the outcome, the search's time, the tree's leaves and splits, the check's verdict and time.
import {readFileSync} from 'node:fs'
import {type Tree, check} from '../../kernel/kernel.ts'
import {clock, grow, withDeadline} from '../../kernel/prove.ts'
import {cdclStats, growCdcl} from '../../kernel/cdcl.ts'
import {loadGoal} from '../dag/goalio.ts'

const file = process.argv[2]!
const arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const ms = Number(arg('--ms') ?? 55000)
const goal = loadGoal(readFileSync(file, 'utf8'))
const count = (t: Tree): [number, number] => ('leaf' in t ? [1, 0] : ((a, b) => [a[0] + b[0], a[1] + b[1] + 1])(count(t.yes), count(t.no)))
const t0 = performance.now()
const search = arg('--search') ?? 'grow'
cdclStats.on = true
const out = withDeadline(performance.now() + ms, () => search === 'cdcl'
  ? growCdcl(goal, new Map(), {nodes: 0, until: clock() + Math.min(ms, Math.max(20_000, 1_000 * goal.hyps.length))})
  : grow(goal))
const searchMs = Math.round(performance.now() - t0)
const res: Record<string, unknown> = {goal: goal.name, hyps: goal.hyps.length, search, searchMs}
if ('tree' in out) {
  const [leaves, splits] = count(out.tree), t1 = performance.now(), ok = check(goal, out.tree)
  Object.assign(res, {outcome: ok ? 'proven' : 'rejected', leaves, splits, checkMs: Math.round(performance.now() - t1)})
} else Object.assign(res, {outcome: out.stuck, why: out.why?.slice(0, 80)})
if (cdclStats.runs) res.cdcl = Object.fromEntries(Object.entries(cdclStats).map(([key, x]) => [key, typeof x === 'number' ? Math.round(x) : x]))
console.log(JSON.stringify(res))
process.exit(0)
