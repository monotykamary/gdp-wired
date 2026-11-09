// Replay exactly one captured root goal. Units are the production allowance,
// passed explicitly from that attempt's trace, never an increased proof budget.
import {readFileSync} from 'node:fs'
import {check} from '../../kernel/kernel.ts'
import {clock, counted, fullRate, fullWork, grow, withDeadline, withWall} from '../../kernel/prove.ts'
const capture = JSON.parse(readFileSync(process.argv[2]!, 'utf8'))
const index = Number(process.argv[3]), units = Number(process.argv[4])
if (!Number.isSafeInteger(index) || !Number.isFinite(units) || units <= 0) throw Error('capture, index, positive production allowance required')
const item = capture.roots[index]
if (!item?.goal) throw Error('missing captured goal')
const start = performance.now(), before = fullWork()
const out = withWall(start + 60_000, () => counted(fullRate, () => withDeadline(clock() + units, () => grow(item.goal, new Map(), {nodes: 0, until: clock() + units})), true))
console.log(JSON.stringify({index, law: item.law, pass: item.pass, name: item.goal.name, checked: 'tree' in out ? check(item.goal, out.tree) : false, units, work: fullWork() - before, wallMs: performance.now() - start, outcome: 'tree' in out ? 'tree (diagnostic replay; not an end-to-end proof)' : out.stuck, why: 'why' in out ? out.why : undefined}))
