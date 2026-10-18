// Cloud infrastructure: tenant quotas, autoscaling within bounds, a lease held by one node, rolling deploys that keep
// enough instances healthy, storage quotas with deletes, a regional rate limit read from the log, a drain loop, and
// backup retention. Each rule takes the bug its broken variant carries.
import {type Bool, type Maybe, type Term, bool, count, forall, loop, max, maybe, min, nat, no, oneOf, relation, rule, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Tenant quotas: a tenant allocates resources within its quota and releases what it holds; an operator only raises
// quotas.
const quotas = (bug?: 'checks the old usage') => rule('tenant quotas')
  .inputs({op: oneOf('raise', 'allocate', 'release'), tenant: nat, amount: nat})
  .maps({Quota: 0, Used: 0})
  .flags(({op, tenant, amount, Quota, Used}) => ({
    allocates: op.is('allocate').and(bug ? Used.at(tenant).atMost(Quota.at(tenant)) : Used.at(tenant).plus(amount).atMost(Quota.at(tenant))),
    releases: op.is('release').and(amount.atMost(Used.at(tenant))),
  }))
  .step(({op, tenant, amount, allocates, releases, Quota, Used}) => ({
    Quota: Quota.bump(tenant, op.is('raise'), amount),
    Used: Used.set(tenant, when(allocates, Used.at(tenant).plus(amount), when(releases, Used.at(tenant).minus(amount), Used.at(tenant)))),
  }))
const quotaLaws = (r: ReturnType<typeof quotas>) => [r.law('every tenant: used <= quota', ({Used, Quota}) => forall(t => Used.at(t).atMost(Quota.at(t))))]

// Autoscaling: the replica count moves toward the desired count by at most `stepSize` per decision, and stays within
// [minReplicas, maxReplicas].
const scaler = (bug?: 'scale-down ignores the floor') => rule('autoscaling within bounds')
  .params({minReplicas: nat, maxReplicas: nat, stepSize: nat})
  .inputs({desired: nat})
  .state({replicas: ({minReplicas}) => minReplicas})
  .pre(({minReplicas, maxReplicas}) => minReplicas.atMost(maxReplicas))
  .step(({replicas, desired, minReplicas, maxReplicas, stepSize}) => {
    const toward = max(replicas.minus(stepSize), min(replicas.plus(stepSize), desired))
    return {replicas: bug ? min(maxReplicas, toward) : max(minReplicas, min(maxReplicas, toward))}
  })
const scalerLaws = (r: ReturnType<typeof scaler>) => [
  r.law('replicas >= minReplicas', ({replicas, minReplicas}) => minReplicas.atMost(replicas)),
  r.law('replicas <= maxReplicas', ({replicas, maxReplicas}) => replicas.atMost(maxReplicas)),
]
const scalerSteps = (r: ReturnType<typeof scaler>) => [
  r.stepLaw('a decision adds at most stepSize replicas', ({replicas, stepSize}, after) => after.replicas.atMost(replicas.plus(stepSize))),
]

// A lease: `owner` is the holder's id plus one (0 when free); a node acquires it only while it is free, and only its
// owner releases it. Holds records each node's own view.
const lease = (bug?: 'checks only its own flag') => rule('lease held by one node')
  .inputs({op: oneOf('acquire', 'release'), node: nat})
  .state({owner: 0})
  .maps({Holds: 0})
  .flags(({op, node, owner, Holds}) => ({
    acquires: op.is('acquire').and(bug ? Holds.at(node).eq(0) : owner.eq(0)),
    releases: op.is('release').and(owner.eq(node.plus(1))),
  }))
  .step(({node, acquires, releases, owner, Holds}) => ({
    owner: when(acquires, node.plus(1), when(releases, 0, owner)),
    Holds: Holds.set(node, when(acquires, 1, when(releases, 0, Holds.at(node)))),
  }))
const leaseLaws = (r: ReturnType<typeof lease>) => [
  r.law('a node that thinks it holds the lease is its owner', ({Holds, owner}) => forall(n => Holds.at(n).eq(0).or(owner.eq(n.plus(1))))),
  r.law('a node\'s view is 0 or 1', ({Holds}) => forall(n => Holds.at(n).atMost(1))),
]

// A rolling deploy: an instance is taken down only while more than `minHealthy` are up, and comes back after.
const rolling = (bug?: 'takes down at the minimum') => rule('rolling deploy')
  .params({total: nat, minHealthy: nat})
  .inputs({op: oneOf('drain', 'restore')})
  .state({healthy: ({total}) => total, draining: 0})
  .pre(({minHealthy, total}) => minHealthy.atMost(total))
  .flags(({op, healthy, draining, minHealthy}) => ({
    drains: op.is('drain').and(bug ? healthy.atLeast(minHealthy) : healthy.gt(minHealthy)),
    restores: op.is('restore').and(draining.atLeast(1)),
  }))
  .step(({drains, restores, healthy, draining}) => ({
    healthy: when(drains, healthy.minus(1), when(restores, healthy.plus(1), healthy)),
    draining: when(drains, draining.plus(1), when(restores, draining.minus(1), draining)),
  }))
const rollingLaws = (r: ReturnType<typeof rolling>) => [
  r.law('healthy >= minHealthy', ({healthy, minHealthy}) => minHealthy.atMost(healthy)),
  r.law('healthy + draining = total', ({healthy, draining, total}) => healthy.plus(draining).eq(total)),
]

// A storage quota: a put of `size` fits under the quota; a delete removes at most what the bucket holds.
const storage = (bug?: 'put checks the old total') => rule('storage quota with deletes')
  .params({quota: nat})
  .inputs({op: oneOf('put', 'delete'), bucket: nat, size: nat})
  .state({total: 0})
  .maps({Stored: 0})
  .flags(({op, bucket, size, total, quota, Stored}) => ({
    puts: op.is('put').and(bug ? total.atMost(quota) : total.plus(size).atMost(quota)),
    deletes: op.is('delete').and(size.atMost(Stored.at(bucket))),
  }))
  .step(({bucket, size, puts, deletes, total, Stored}) => ({
    total: when(puts, total.plus(size), when(deletes, total.minus(size), total)),
    Stored: Stored.set(bucket, when(puts, Stored.at(bucket).plus(size), when(deletes, Stored.at(bucket).minus(size), Stored.at(bucket)))),
  }))
const storageLaws = (r: ReturnType<typeof storage>) => [r.law('total stored <= quota', ({total, quota}) => total.atMost(quota))]
const storageSteps = (r: ReturnType<typeof storage>) => [
  r.stepLaw('a delete never raises the total', ({total}, after) => after.total.atMost(total), ({deletes}) => deletes),
]

// A regional rate limit read from the log: a request from a region goes through while that region sent fewer than
// `cap` in the window before it. `recent` (a sum) counts region `who`'s requests in the window ending at `now`.
const regional = (bug?: 'window one short') => rule('regional rate limit')
  .params({window: nat, cap: nat, now: nat, who: nat})
  .inputs({region: nat, t: nat})
  .log('region', 't')
  .sums({recent: (r, {now, window, who}) => count(r.region.eq(who).and(r.t.atMost(now), now.lt(r.t.plus(window))))})
  .queries({sent: (r, {t, window, region}) => when(r.region.eq(region), count(bug ? t.plus(1).lt(r.t.plus(window)) : t.lt(r.t.plus(window))), 0)})
  .flags(({sent, cap}) => ({ok: sent.plus(1).atMost(cap)}))
  .keep(({ok}) => ok)
  .relations(({t, now, region, who, recent, sent}) => [relation(recent.atMost(sent), t.atMost(now).and(region.eq(who)))])
const regionalLaws = (r: ReturnType<typeof regional>) => [r.law('requests from who in the window ending at now <= cap', ({recent, cap}) => recent.atMost(cap))]

// Draining a node before maintenance: each turn moves some connections off it; the rank is the connections left.
const drain = (bug?: 'a turn may move none') => {
  const base = loop('draining a node')
    .params({connections: nat})
    .inputs({moved: nat})
    .state({left: ({connections}) => connections, done: 0})
    .while(({left}) => left.gt(0))
    .body(({left, done, moved}) => ({left: left.minus(min(left, moved)), done: done.plus(min(left, moved))}))
    .rank(({left}) => left)
  return bug ? base : base.assume(({moved}) => moved.atLeast(1))
}
const drainLaws = (l: ReturnType<typeof drain>) => [l.law('left + done = connections', ({left, done, connections}) => left.plus(done).eq(connections))]

// Backup retention: a backup is kept within the retention period, a monthly one for a year, and always while a legal
// hold is in force.
const retention = rule('backup retention').inputs({age: nat, retention: nat, monthly: bool, holdUntil: maybe(nat), now: nat})
type RetentionEnv = {age: Term, retention: Term, monthly: Bool, holdUntil: Maybe<Term>, now: Term}
const kept = ({age, retention: keep, monthly, holdUntil, now}: RetentionEnv, bug?: 'hold read backwards') =>
  age.atMost(keep).or(monthly.and(age.atMost(365)), holdUntil.match({none: () => no, some: u => (bug ? u.lt(now) : now.lt(u))}))
const retentionDecisions = [
  retention.decide('a backup under a legal hold is kept', ({holdUntil, now}) => holdUntil.match({none: () => no, some: u => now.lt(u)}), env => kept(env)),
  retention.decide('a backup within retention is kept', ({age, retention: keep}) => age.atMost(keep), env => kept(env)),
  retention.decide('an old daily backup with no hold may go', ({age, retention: keep, monthly, holdUntil}) => [keep.lt(age), monthly.not(), holdUntil.isNone], env => kept(env).not()),
]
const retentionBroken = [
  {name: 'hold read backwards', why: 'the legal hold is compared the wrong way, so it protects only expired holds', decision: retention.decide('a backup under a legal hold is kept', ({holdUntil, now}) => holdUntil.match({none: () => no, some: u => now.lt(u)}), env => kept(env, 'hold read backwards'))},
]

const quotasOld = quotas('checks the old usage')
const scalerFloor = scaler('scale-down ignores the floor')
const leaseOwn = lease('checks only its own flag')
const rollingMin = rolling('takes down at the minimum')
const storageOld = storage('put checks the old total')
const regionalShort = regional('window one short')
const drainNone = drain('a turn may move none')

export const domain: Domain = {
  domain: 'cloud',
  about: 'tenant quotas, autoscaling, leases, rolling deploys, storage quotas, regional rate limits, draining, backup retention',
  cases: [
    machineCase('tenant quotas', 'no tenant ever uses more than its quota', quotas(), quotaLaws(quotas()), [
      {name: 'checks the old usage', why: 'an allocation is checked before its amount is added', rule: quotasOld, laws: quotaLaws(quotasOld)},
    ]),
    machineCase('autoscaling within bounds', 'the replica count stays within [min, max] and moves by at most stepSize', scaler(), scalerLaws(scaler()), [
      {name: 'scale-down ignores the floor', why: 'a scale-down clamps to the maximum only, so it can drop below the minimum', rule: scalerFloor, laws: scalerLaws(scalerFloor), steps: scalerSteps(scalerFloor)},
    ], {steps: scalerSteps(scaler())}),
    machineCase('lease held by one node', 'at most one node holds the lease at a time', lease(), leaseLaws(lease()), [
      {name: 'checks only its own flag', why: 'a node checks whether it holds the lease itself, not whether anyone does', rule: leaseOwn, laws: leaseLaws(leaseOwn)},
    ]),
    machineCase('rolling deploy', 'a deploy never takes healthy instances below minHealthy, and none goes missing', rolling(), rollingLaws(rolling()), [
      {name: 'takes down at the minimum', why: 'the check uses >= and drains an instance when exactly minHealthy are up', rule: rollingMin, laws: rollingLaws(rollingMin)},
    ]),
    machineCase('storage quota with deletes', 'stored bytes stay under the quota, and a delete never raises them', storage(), storageLaws(storage()), [
      {name: 'put checks the old total', why: 'a put is checked before its size is added', rule: storageOld, laws: storageLaws(storageOld), steps: storageSteps(storageOld)},
    ], {steps: storageSteps(storage())}),
    machineCase('regional rate limit', 'no region sends more than cap requests in any window ending at now, read from the log', regional(), regionalLaws(regional()), [
      {name: 'window one short', why: 'the query counts a window one tick shorter than the limit\'s', rule: regionalShort, laws: regionalLaws(regionalShort)},
    ]),
    loopCase('draining a node', 'draining halts with every connection moved', drain(), drainLaws(drain()), [
      {name: 'a turn may move none', why: 'without a minimum per turn, a drain can stall forever', loop: drainNone, laws: drainLaws(drainNone)},
    ]),
    decisionCase('backup retention', 'backups are kept within retention, monthly ones for a year, and always under a legal hold', retentionDecisions, retentionBroken),
  ],
}
