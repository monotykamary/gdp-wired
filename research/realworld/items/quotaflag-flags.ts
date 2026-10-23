// Feature flags with percentage rollouts, from three SDKs:
//
// - Unleash Node SDK v6.12.2 (unleash-client on npm), FlexibleRolloutStrategy with the feature-level checks of
//   UnleashClient.isFeatureEnabled. Apache-2.0, (c) Unleash.
//   https://github.com/Unleash/unleash-client-node/tree/dc113ce745f6c0efe65ae3f6b49a439144ac4aa3/src
// - GrowthBook JS SDK at v5.1.0 (packages/sdk-js, MIT outside the enterprise dirs), isIncludedInRollout and the force
//   rules of evalFeature. MIT, (c) GrowthBook, Inc.
//   https://github.com/growthbook/growthbook/tree/7cbc85d1d113595757f6808b5c440657e4325b47/packages/sdk-js/src
// - flagd core/v0.19.0, the fractional operator's distributeValue. Apache-2.0, (c) the OpenFeature flagd authors.
//   https://github.com/open-feature/flagd/blob/ac826d8e9cf3f5b14ad56f6e9eeeb981f45321eb/core/pkg/evaluator/fractional.go
//
// The hash: each SDK hashes the user's id (with a group id or seed) and normalizes it (Unleash: murmurhash3 x86_32 % 100
// + 1; GrowthBook: fnv1a32 % 10000 / 10000; flagd: (murmur3 * totalWeight) >> 32). A rule cannot compute the hash, so
// the normalized value is an input in the range the normalization gives (the GAPS 'hash' entry). That decomposition is
// faithful for every law here that holds for all users: the normalized value of a user is a function of the user's id and
// the group id or seed only, never of the percentage, coverage or range, so two evaluations of one user at two
// percentages share it (a relate with the value equal on both sides), and every value in the range is some user's (the
// normalizations are onto their ranges). It is an approximation only for claims about how many users fall in a bucket
// (the hash's distribution), which none of these laws makes.
import {bool, decimal, fun, nat, rule, when} from '../../../core/dsl.ts'
import {type RealItem, decision, invariant, stepLaw} from '../lib.ts'

// --- Unleash flexibleRollout ------------------------------------------------------------------------------------------

const unleashSrc = {repo: 'Unleash/unleash-client-node', commit: 'dc113ce745f6c0efe65ae3f6b49a439144ac4aa3', licence: 'Apache-2.0', author: 'Unleash', language: 'TypeScript'}

export const flexibleRollout = () => fun('Unleash flexibleRollout')
  .inputs({
    // client.ts:144-145 `if (!feature) return { enabled: fallback() }`: an unknown feature serves the caller's fallback.
    known: bool, fallback: bool,
    // client.ts:148 `!this.isParentDependencySatisfied(feature, context) || !feature.enabled`: the parents' own evaluation
    // (recursive, client.ts:89-117) comes in as its outcome.
    parentOk: bool, enabled: bool,
    // client.ts:158-159 a feature with no strategies is on when enabled.
    noStrategies: bool,
    // strategy.ts:304-314 checkConstraints over the strategy's and its segments' constraints (string, semver, regex,
    // CIDR and date operators), as its outcome.
    constraintsOk: bool,
    // flexible-rollout-strategy.ts:39-43 the stickiness id resolved (userId || sessionId || random for 'default', a
    // context field otherwise); a missing one disables the strategy.
    hasId: bool,
    // :37 `Number(parameters.rollout)`, a whole percentage.
    rollout: nat,
    // util.ts:3-12 normalizedStrategyValue: murmurhash3 x86_32 of `${groupId}:${id}` (seed 0) % 100 + 1.
    normalized: nat,
  })
  .assume(({normalized}) => normalized.atLeast(1).and(normalized.atMost(100)))
  .returns(({known, fallback, parentOk, enabled, noStrategies, constraintsOk, hasId, rollout, normalized}) => ({
    // strategy.ts:325 constraints && isEnabled; flexible-rollout-strategy.ts:45 `percentage > 0 && normalizedUserId <= percentage`.
    on: when(known, parentOk.and(enabled, noStrategies.or(constraintsOk.and(hasId, rollout.gt(0), normalized.atMost(rollout)))), fallback),
  }))

const fr = flexibleRollout()
type FrEnv = Parameters<Parameters<typeof fr.law>[1]>[0]
// Everything about one evaluation but the rollout is the same on both sides (the same user, the same feature).
const sameButRollout = (a: FrEnv, b: FrEnv) => [a.known.iff(b.known), a.fallback.iff(b.fallback), a.parentOk.iff(b.parentOk), a.enabled.iff(b.enabled),
  a.noStrategies.iff(b.noStrategies), a.constraintsOk.iff(b.constraintsOk), a.hasId.iff(b.hasId), a.normalized.eq(b.normalized)]

const unleashItem: RealItem = {
  id: 'feature flag/unleash-client-node/flexibleRollout',
  domain: 'feature flag',
  source: {...unleashSrc, path: 'src/strategy/flexible-rollout-strategy.ts', lines: '21-46', export: 'FlexibleRolloutStrategy'},
  also: [
    {...unleashSrc, path: 'src/strategy/util.ts', lines: '3-12', export: 'normalizedStrategyValue'},
    {...unleashSrc, path: 'src/strategy/strategy.ts', lines: '290-326', export: 'Strategy.isEnabledWithConstraints'},
    {...unleashSrc, path: 'src/client.ts', lines: '138-185', export: 'UnleashClient.isFeatureEnabled'},
    {...unleashSrc, path: 'src/test/strategy/gradual-rollout-user-id.test.ts', lines: '11-46', export: 'tests'},
  ],
  summary: 'A feature with one flexibleRollout strategy: on when known, enabled, its parents satisfied, its constraints pass, a stickiness id resolves and the id\'s normalized hash (1..100) is at most the rollout percentage.',
  expressible: 'partial',
  gaps: [
    {gap: 'hash', blocks: 'part', detail: 'murmurhash3 x86_32 of `${groupId}:${id}` % 100 + 1 is an input in 1..100; faithful for the laws here (the value does not depend on the rollout and every value is reached)'},
    {gap: 'string', blocks: 'part', detail: 'constraint operators (IN, STR_*, SEMVER_*, REGEX, IN_CIDR, DATE_*) are an input: their outcome'},
    {gap: 'recursion', blocks: 'part', detail: 'isParentDependencySatisfied evaluates parent features recursively; its outcome is an input'},
    {gap: 'unbounded-collection', blocks: 'part', detail: 'a feature\'s list of strategies (on when any is, client.ts:164-183) is one strategy here'},
    {gap: 'float', blocks: 'part', detail: '`Number(parameters.rollout)` may be fractional or NaN; the rule takes a whole percentage, as the admin UI stores it'},
  ],
  laws: [
    decision(fr.law('a disabled feature serves nobody', ({known, enabled}) => [known, enabled.not()], out => out.on.not()),
      'safety', 'inferred', 'client.ts:148 `!feature.enabled` returns { enabled: false } before any strategy runs'),
    decision(fr.relate('raising the rollout never removes a user who was in', (a, b) => [...sameButRollout(a, b), a.rollout.atMost(b.rollout)], (outA, outB) => outA.on.implies(outB.on)),
      'safety', 'tests', 'gradual-rollout-user-id.test.ts:25-46 "enabled when percentage is exactly same", "disabled when percentage is just below": a threshold on a fixed value'),
    decision(fr.law('a 0% rollout serves nobody through the strategy', ({known, noStrategies, rollout}) => [known, noStrategies.not(), rollout.eq(0)], out => out.on.not()),
      'safety', 'tests', 'gradual-rollout-user-id.test.ts:18 "should be disabled when percentage is 0"'),
    decision(fr.law('a 100% rollout serves every user with an id who passes the constraints', ({known, parentOk, enabled, constraintsOk, hasId, rollout}) => [known, parentOk, enabled, constraintsOk, hasId, rollout.eq(100)], out => out.on),
      'safety', 'tests', 'gradual-rollout-user-id.test.ts:11 "should be enabled when percentage is 100"'),
    decision(fr.law('a user failing the constraints is never served by the strategy', ({known, noStrategies, constraintsOk}) => [known, noStrategies.not(), constraintsOk.not()], out => out.on.not()),
      'access', 'docs', 'strategy.ts:325 `this.checkConstraints(context, constraints) && this.isEnabled(parameters, context)`'),
    decision(fr.law('a strategy without a stickiness id serves nobody', ({known, noStrategies, hasId}) => [known, noStrategies.not(), hasId.not()], out => out.on.not()),
      'safety', 'tests', 'flexible-rollout.test.ts:23 "should be disabled when stickiness=userId and userId not on context"'),
  ],
}

// --- GrowthBook force rules -------------------------------------------------------------------------------------------

const gbSrc = {repo: 'growthbook/growthbook', commit: '7cbc85d1d113595757f6808b5c440657e4325b47', licence: 'MIT', author: 'GrowthBook, Inc.', language: 'TypeScript'}
// Hash values are k/10000 (v2, util.ts:38) or k/1000 (v1, :42): four decimal places are exact. Coverage and ranges are
// JSON numbers the GrowthBook UI writes as percentages, at most four places; JS compares the doubles nearest to each
// decimal, and rounding to nearest is monotone and keeps distinct 4-place values in [0, 1] apart, so the comparisons
// agree with the decimals'.
const d4 = decimal(4)

export const forceRule = () => fun('GrowthBook force rule rollout')
  .inputs({
    // core.ts:271 `rule.filters && isFilteredOut(rule.filters, ctx)` (namespace hash ranges), as its outcome.
    filteredOut: bool,
    // core.ts:283 `rule.condition && !conditionPasses(...)` (a Mongo-style condition over the attributes): no
    // condition or one that passes.
    conditionOk: bool,
    // core.ts:958-960 `range`, `coverage` (each may be undefined).
    hasRange: bool, lo: d4, hi: d4, hasCoverage: bool, coverage: d4,
    // core.ts:966-969 getHashAttribute's hashValue is non-empty.
    hashed: bool,
    // core.ts:971-972 `hash(seed, hashValue, hashVersion || 1)` is null only for an unknown hash version.
    knownVersion: bool,
    // util.ts:31-47 the hash's value, in [0, 1).
    n: d4,
  })
  .assume(({n}) => n.atLeast(0).and(n.lt(1)))
  .returns(({filteredOut, conditionOk, hasRange, lo, hi, hasCoverage, coverage, hashed, knownVersion, n}) => {
    // core.ts:953-979 isIncludedInRollout.
    const included = when(hasRange.not().and(hasCoverage.not()), hasRange.not(), // :962 no range, no coverage: true
      when(hasRange.not().and(coverage.eq(0)), hasRange, // :964 no range, coverage 0: false
        hashed.and(knownVersion, when(hasRange, lo.atMost(n).and(n.lt(hi)), n.atMost(coverage))))) // :966-978, util.ts:54-56 inRange
    // core.ts:271-335: a force rule returns its value when not filtered out, its condition passes and it includes the user.
    return {included, served: filteredOut.not().and(conditionOk, included)}
  })

const gb = forceRule()
type GbEnv = Parameters<Parameters<typeof gb.law>[1]>[0]
const sameUser = (a: GbEnv, b: GbEnv) => [a.filteredOut.iff(b.filteredOut), a.conditionOk.iff(b.conditionOk), a.hashed.iff(b.hashed), a.knownVersion.iff(b.knownVersion), a.n.eq(b.n)]

const growthbookItem: RealItem = {
  id: 'feature flag/growthbook/forceRuleRollout',
  domain: 'feature flag',
  source: {...gbSrc, path: 'packages/sdk-js/src/core.ts', lines: '953-979', export: 'isIncludedInRollout'},
  also: [
    {...gbSrc, path: 'packages/sdk-js/src/core.ts', lines: '231-336', export: 'evalFeature (force rules)'},
    {...gbSrc, path: 'packages/sdk-js/src/util.ts', lines: '19-56', export: 'hash, inRange'},
  ],
  summary: 'A GrowthBook force rule serves its value to a user who passes its filters and condition and falls in its rollout: the user\'s hash in [0, 1) within the rule\'s range, or at most its coverage.',
  expressible: 'partial',
  gaps: [
    {gap: 'hash', blocks: 'part', detail: 'fnv1a32-based hash(seed, hashValue, version) is an input in [0, 1) at four places; faithful for these laws (it does not depend on coverage or range)'},
    {gap: 'dynamic-policy', blocks: 'part', detail: 'rule.condition is a Mongo-style query evaluated over the attributes (mongrule.ts); its outcome is an input'},
    {gap: 'hash', blocks: 'part', detail: 'isFilteredOut (namespace filters: hash ranges over other seeds) is an input'},
    {gap: 'float', blocks: 'part', detail: 'coverage and range bounds are JS numbers; decimal(4) is exact only for bounds with at most four places, as the UI writes them'},
  ],
  laws: [
    decision(gb.law('a rule with coverage 0 serves nobody', ({hasRange, hasCoverage, coverage}) => [hasRange.not(), hasCoverage, coverage.eq(0)], out => out.served.not()),
      'safety', 'inferred', 'core.ts:964 `if (!range && coverage === 0) return false`'),
    decision(gb.relate('raising the coverage never removes a user who was in', (a, b) => [...sameUser(a, b), a.hasRange.not(), b.hasRange.not(), a.hasCoverage, b.hasCoverage, a.coverage.atMost(b.coverage)], (outA, outB) => outA.served.implies(outB.served)),
      'safety', 'inferred', 'a percentage rollout: the user\'s hash is fixed by seed and attribute (util.ts:31-47), the coverage only moves the threshold'),
    decision(gb.relate('widening the range never removes a user who was in', (a, b) => [...sameUser(a, b), a.hasRange, b.hasRange, b.lo.atMost(a.lo), a.hi.atMost(b.hi)], (outA, outB) => outA.served.implies(outB.served)),
      'safety', 'inferred', 'core.ts:975 `inRange(n, range)`: a wider range holds every hash the narrower one does'),
    decision(gb.law('a user without the hash attribute is never in a percentage rollout', ({hasRange, hasCoverage, hashed}) => [hasRange.or(hasCoverage), hashed.not()], out => out.included.not()),
      'access', 'docs', 'core.ts:966-969 `if (!hashValue) { return false; }`'),
    decision(gb.law('a rule with no range and no coverage includes everyone', ({hasRange, hasCoverage}) => [hasRange.not(), hasCoverage.not()], out => out.included),
      'safety', 'docs', 'core.ts:962 `if (!range && coverage === undefined) return true`'),
    decision(gb.law('full coverage includes every hashed user', ({hasRange, hasCoverage, coverage, hashed, knownVersion}) => [hasRange.not(), hasCoverage, coverage.atLeast(1), hashed, knownVersion], out => out.included),
      'safety', 'inferred', 'coverage 1 is a 100% rollout; the hash is below 1 (util.ts:38, :42)'),
    decision(gb.law('a filtered-out user is never served the forced value', ({filteredOut}) => filteredOut, out => out.served.not()),
      'access', 'docs', 'core.ts:270-278 "If there are filters for who is included (e.g. namespaces)" ... continue'),
  ],
}

// --- flagd fractional ---------------------------------------------------------------------------------------------------

const flagdSrc = {repo: 'open-feature/flagd', commit: 'ac826d8e9cf3f5b14ad56f6e9eeeb981f45321eb', licence: 'Apache-2.0', author: 'OpenFeature (flagd authors)', language: 'Go'}

// distributeValue's loop over the weighted variants, one variant per request in their order (fractional.go:287-293):
// a run of the rule is the loop over a list, and every list is some run. `bucket` is fractional.go:284
// `(uint64(hashValue) * uint64(totalWeight)) >> 32`, a param (fixed for the loop): it lies below totalWeight, and every
// value below it is some hash's bucket, since totalWeight <= MaxInt32 < 2^32. The loop's `return variant.variant` is
// `done` with the variant's index `chosen`; requests after it are variants the loop no longer reads (nothing changes).
// `start`: the chosen variant's range start, ghost state (the rangeEnd before its weight), for the law about its range.
// Weights are naturals: parseFractionalEvaluationDistributions clamps negative weights to 0 (:254-259) and refuses
// non-integers and sums past MaxInt32 (:241-271). A total of 0 returns nil (:280-282); so does this loop, which then
// never passes the bucket.
export const fractional = () => rule('flagd fractional distributeValue')
  .params({bucket: nat})
  .inputs({weight: nat})
  .state({rangeEnd: 0, i: 0, done: bool.from(false), chosen: 0, start: 0})
  .flags(({bucket, weight, rangeEnd, done}) => ({
    // :288-289 `rangeEnd += uint64(variant.weight); if bucket < rangeEnd`.
    picks: done.not().and(bucket.lt(rangeEnd.plus(weight))),
  }))
  .step(({weight, rangeEnd, i, done, chosen, start, picks}) => ({
    rangeEnd: when(done, rangeEnd, rangeEnd.plus(weight)),
    i: when(done, i, i.plus(1)),
    done: done.or(picks),
    chosen: when(picks, i, chosen),
    start: when(picks, rangeEnd, start),
  }))

const fd = fractional()
const flagdItem: RealItem = {
  id: 'feature flag/flagd/fractional',
  domain: 'feature flag',
  source: {...flagdSrc, path: 'core/pkg/evaluator/fractional.go', lines: '279-296', export: 'distributeValue'},
  also: [
    {...flagdSrc, path: 'core/pkg/evaluator/fractional.go', lines: '191-275', export: 'parseFractionalEvaluationDistributions'},
    {...flagdSrc, path: 'docs/architecture-decisions/high-precision-fractional-bucketing.md', lines: '33-42', export: 'goals'},
  ],
  summary: 'flagd\'s fractional operator maps a user\'s murmur3 hash to a bucket below the total weight and walks the weighted variants, returning the first whose cumulative weight passes the bucket.',
  expressible: 'partial',
  gaps: [
    {gap: 'hash', blocks: 'part', detail: 'murmur3.Sum32 of the CBOR-encoded [flagKey, targetingKey] (or the explicit bucketing value) is not computed: the bucket it gives is the param'},
    {gap: 'nonlinear', blocks: 'part', detail: 'bucket = (hash * totalWeight) >> 32 multiplies two unknowns; the bucket is given (below the total, every value reached)'},
    {gap: 'other', blocks: 'law', detail: 'a law about two evaluations of one user under two weightings (stickiness as the weights change: the bucket moves with the total) compares two runs of the loop; relate takes one request, not two runs', laws: ['raising a variant\'s weight at the same total keeps its users']},
    {gap: 'other', blocks: 'law', detail: '"any variant with weight > 0 receives some traffic" says some bucket picks it: an exists over the param, across runs', laws: ['every variant of positive weight is chosen for some bucket']},
  ],
  laws: [
    stepLaw(fd, fd.stepLaw('a variant of weight 0 is never chosen', ({weight}, after) => after.done.implies(weight.gt(0)), ({done}) => done.not()),
      'step', 'docs', 'high-precision-fractional-bucketing.md:41 "any variant with weight > 0 receives some traffic"; the loop picks by `bucket < rangeEnd` after adding the weight'),
    invariant(fd, fd.law('once the weights read pass the bucket, a variant is chosen', ({bucket, rangeEnd, done}) => bucket.lt(rangeEnd).implies(done)),
      'safety', 'docs', 'fractional.go:294 "unreachable given validation": the bucket is below the total, so the loop returns a variant'),
    invariant(fd, fd.law("the chosen variant's range holds the bucket", ({bucket, done, start, rangeEnd}) => done.implies(start.atMost(bucket).and(bucket.lt(rangeEnd)))),
      'safety', 'docs', 'fractional.go:277-278 "maps a 32-bit hash to the range [0, totalWeight) and finds the variant bucket that contains that value"'),
    stepLaw(fd, fd.stepLaw('a chosen variant never changes', ({chosen}, after) => after.done.and(after.chosen.eq(chosen)), ({done}) => done),
      'step', 'docs', 'fractional.go:290 `return variant.variant`: the first variant whose range holds the bucket'),
    invariant(fd, fd.law('the chosen variant is one the loop read', ({done, chosen, i}) => done.implies(chosen.lt(i))),
      'safety', 'inferred', 'distributeValue returns a variant of the list it walks'),
  ],
  unstated: [
    {name: 'raising a variant\'s weight at the same total keeps its users', kind: 'safety', intent: 'docs', why: 'fractional-operation-spec.md:9 "evaluations MUST be sticky"'},
    {name: 'every variant of positive weight is chosen for some bucket', kind: 'safety', intent: 'docs', why: 'high-precision-fractional-bucketing.md:41 "Guarantee that any variant with weight > 0 receives some traffic allocation"'},
  ],
}

export const items: RealItem[] = [unleashItem, growthbookItem, flagdItem]
