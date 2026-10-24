// A false step law the random runs miss, given to the kernel as it is (core/pairs.test.ts's "two groups of effects"
// with a bug, examples/groups.ts): `bun research/query/pairs-false.ts <bug> [--ms 120000]`. The goal it stops on is the
// 944-hypothesis one (CHANGELOG 0.26.0), its default budget a second a hypothesis, here within --ms. Research tooling.
import {groupLaws, groups} from '../../examples/groups.ts'
import {proveStepLaws, withDeadline} from '../../kernel/prove.ts'

const bug = process.argv[2] as Parameters<typeof groups>[0]
const i = process.argv.indexOf('--ms'), ms = i < 0 ? 120_000 : Number(process.argv[i + 1])
const g = groups(bug), t0 = performance.now()
const out = withDeadline(performance.now() + ms, () => proveStepLaws(g.machine, g.kindLaws(), groupLaws(g)))
console.log(JSON.stringify({bug, proven: out.proven, failed: out.failed && {goal: out.failed.goal, stuck: out.failed.stuck, why: out.failed.why?.slice(0, 80)}, ms: Math.round(performance.now() - t0)}))
process.exit(0)
