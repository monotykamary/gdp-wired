// Conformance: the rule of `feature flag/growthbook/forceRuleRollout` against the original GrowthBook JS SDK
// (@growthbook/growthbook@1.7.0 from npm, the sdk-js version at the repo's v5.1.0 tag, commit 7cbc85d1), on random
// evaluations of a feature with one force rule. Installs the package into a fresh temp dir; nothing is vendored.
// Run: bun research/realworld/repro/conform-growthbook.ts
// The inputs the rule takes as outcomes (the hash value, the namespace filter, the condition) are computed with the
// SDK's own exported functions (dist/esm/util.mjs hash and inRange, evalCondition); whether the user is served the
// forced value is the SDK's GrowthBook.evalFeature against the rule's `run`.
import {execSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {forceRule} from '../items/quotaflag-flags.ts'

const dir = mkdtempSync(join(tmpdir(), 'conform-growthbook-'))
execSync('npm init -y && npm install --ignore-scripts --no-audit --no-fund @growthbook/growthbook@1.7.0', {cwd: dir, stdio: 'ignore'})
const pkg = join(dir, 'node_modules/@growthbook/growthbook/dist/esm')
const {GrowthBook, evalCondition} = await import(join(pkg, 'index.mjs'))
const {hash, inRange} = await import(join(pkg, 'util.mjs'))

let seed = 11
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % n }
const pick = <T>(xs: T[]) => xs[rand(xs.length)]!
const f = forceRule()
let checked = 0, served = 0
for (let t = 0; t < 5000; t++) {
  const id = rand(5) === 0 ? undefined : rand(10) === 0 ? '' : `u${rand(100000)}`
  const country = pick(['US', 'FR'])
  const hashVersion = pick([undefined, 1, 2, 3])
  const coverage = pick([undefined, 0, 0.0001, 0.25, 0.5, 0.9999, 1, 1.5, -0.25, rand(10001) / 10000])
  const lo = rand(10001) / 10000, hi = Math.min(1, lo + rand(10001) / 10000)
  const range: [number, number] | undefined = rand(3) === 0 ? [lo, hi] : undefined
  const condition = rand(2) ? {country: 'US'} : undefined
  const filters = rand(3) === 0 ? [{seed: 'ns', ranges: [[0, 0.5]], attribute: 'id'}] : undefined
  const rule: Record<string, unknown> = {force: 'on', seed: 'f-seed', ...(coverage === undefined ? {} : {coverage}), ...(range ? {range} : {}), ...(hashVersion ? {hashVersion} : {}), ...(condition ? {condition} : {}), ...(filters ? {filters} : {})}
  const attributes = {...(id === undefined ? {} : {id}), country}
  const gb = new GrowthBook({attributes, features: {f: {defaultValue: 'off', rules: [rule]}}})
  const theirs = gb.evalFeature('f').value === 'on'
  gb.destroy()
  // core.ts:943-951 isFilteredOut over the SDK's own hash and inRange.
  const filteredOut = !!filters && filters.some(fl => { if (!id) return true; const n = hash(fl.seed, id, 2); return n === null || !fl.ranges.some(r => inRange(n, r)) })
  const n = id ? hash('f-seed', id, hashVersion || 1) : null
  const ours = f.run({
    filteredOut, conditionOk: !condition || evalCondition(attributes, condition),
    hasRange: !!range, lo: range?.[0] ?? 0, hi: range?.[1] ?? 0, hasCoverage: coverage !== undefined, coverage: coverage ?? 0,
    hashed: !!id, knownVersion: n !== null, n: n ?? 0,
  }).served
  checked++; if (theirs) served++
  if (ours !== theirs) { console.log(`divergence at ${t}: ${JSON.stringify({id, country, hashVersion, coverage, range, condition: !!condition, filters: !!filters, n})}: rule ${ours}, SDK ${theirs}`); process.exit(1) }
}
console.log(`conform-growthbook: ${checked} evaluations agree (${served} served)`)
