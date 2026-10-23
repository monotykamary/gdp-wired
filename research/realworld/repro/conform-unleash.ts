// Conformance: the rule of `feature flag/unleash-client-node/flexibleRollout` against the original Unleash Node SDK
// (unleash-client@6.12.2 from npm, the v6.12.2 tag's commit dc113ce7), on random evaluations. Installs the package into
// a fresh temp dir; nothing is vendored. Run: bun research/realworld/repro/conform-unleash.ts
// The inputs the rule takes as outcomes (the constraint check, the normalized hash) are computed here with the SDK's own
// functions; the rest of the decision (unknown feature, disabled, parent, no strategies, stickiness id, the threshold)
// is the SDK's UnleashClient.isFeatureEnabled against the rule's `run`.
import {execSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createRequire} from 'node:module'
import {flexibleRollout} from '../items/quotaflag-flags.ts'

const dir = mkdtempSync(join(tmpdir(), 'conform-unleash-'))
execSync('npm init -y && npm install --ignore-scripts --no-audit --no-fund unleash-client@6.12.2', {cwd: dir, stdio: 'ignore'})
const req = createRequire(join(dir, 'index.js'))
const {default: UnleashClient} = req('unleash-client/lib/client.js')
const {default: Flexible} = req('unleash-client/lib/strategy/flexible-rollout-strategy.js')
const {normalizedStrategyValue} = req('unleash-client/lib/strategy/util.js')
const {Strategy} = req('unleash-client/lib/strategy/strategy.js')

let seed = 7
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n }
const f = flexibleRollout()
const checker = new Strategy('x')
let checked = 0
for (let t = 0; t < 5000; t++) {
  const userId = rand(4) === 0 ? undefined : `user-${rand(100000)}`
  const customerId = rand(3) === 0 ? undefined : `c-${rand(1000)}`
  const stickiness = ['default', 'userId', 'customerId'][rand(3)]!
  const groupId = `g${rand(5)}`
  const rollout = [0, 1, 50, 99, 100, rand(101)][rand(6)]!
  const constraints = rand(2) ? [] : [{contextName: 'region', operator: 'IN', inverted: false, values: ['eu', 'us']}]
  const region = ['eu', 'us', 'ap'][rand(3)]!
  const parentEnabled = rand(4) !== 0, hasParent = rand(2) === 0
  const known = rand(8) !== 0, fallback = rand(2) === 0, enabled = rand(5) !== 0, noStrategies = rand(6) === 0
  const context = {userId, sessionId: undefined, properties: {customerId, region}}
  const feature = {name: 'f', enabled, strategies: noStrategies ? [] : [{name: 'flexibleRollout', parameters: {rollout: String(rollout), stickiness, groupId}, constraints}],
    ...(hasParent ? {dependencies: [{feature: 'parent'}]} : {})}
  const repo = {getToggle: (n: string) => (n === 'parent' ? {name: 'parent', enabled: parentEnabled, strategies: []} : n === 'f' && known ? feature : undefined), getSegment: () => undefined}
  // A random stickiness id only for 'default' with no userId: pin the generator so both sides read one value.
  const strategy = new Flexible(() => '4242')
  const client = new UnleashClient(repo, [strategy])
  const theirs = client.isEnabled('f', context, () => fallback)
  const id = stickiness === 'default' ? (userId || '4242') : stickiness === 'userId' ? userId : customerId
  const ours = f.run({
    known, fallback, parentOk: !hasParent || parentEnabled, enabled, noStrategies,
    constraintsOk: checker.checkConstraints(context, constraints[Symbol.iterator]()),
    hasId: !!id, rollout, normalized: id ? normalizedStrategyValue(id, groupId) : 1,
  }).on
  checked++
  if (ours !== theirs) { console.log(`divergence at ${t}: ${JSON.stringify({known, fallback, enabled, noStrategies, hasParent, parentEnabled, stickiness, userId, customerId, groupId, rollout, region, constraints: constraints.length})}: rule ${ours}, SDK ${theirs}`); process.exit(1) }
}
console.log(`conform-unleash: ${checked} evaluations agree`)
