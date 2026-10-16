// Operations and infrastructure: rate limiters, circuit breakers, retries, queues, autoscaling, rollouts, pools, load
// shedding. Each rule takes the bug its broken variant carries, so a variant is the same rule with one check changed.
import {type Bool, type Choice, type Maybe, type Term, bool, forall, loop, max, maybe, min, nat, no, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A token bucket: a tick adds `refill` tokens up to the bucket size, a request takes n tokens if there are n. `minted`
// counts every token a tick offered, so what was served plus what is left never exceeds the bucket plus the refills.
const tokenBucket = (bug?: 'checks the size' | 'no clamp') => rule('token bucket')
  .params({cap: nat, refill: nat})
  .inputs({op: oneOf('tick', 'take'), n: nat})
  .state({tokens: ({cap}) => cap, served: 0, minted: 0})
  .flags(({op, n, cap, tokens}) => ({granted: op.is('take').and(n.atMost(bug === 'checks the size' ? cap : tokens))}))
  .step(({op, n, cap, refill, tokens, served, minted, granted}) => ({
    tokens: when(op.is('tick'), bug === 'no clamp' ? tokens.plus(refill) : min(cap, tokens.plus(refill)), when(granted, tokens.minus(n), tokens)),
    served: when(granted, served.plus(n), served),
    minted: when(op.is('tick'), minted.plus(refill), minted),
  }))
const bucketLaws = [
  tokenBucket().law('tokens <= bucket size', ({tokens, cap}) => tokens.atMost(cap)),
  tokenBucket().law('served + tokens <= bucket size + refills', ({served, tokens, cap, minted}) => served.plus(tokens).atMost(cap.plus(minted))),
]

// A leaky bucket as a queue: arrivals join if they fit, each leak sends at most `rate`. Nothing is lost or invented:
// what was sent plus what is still in the bucket is exactly what was accepted.
const leakyBucket = (bug?: 'checks the old level' | 'counts the full rate') => rule('leaky bucket')
  .params({capacity: nat, rate: nat})
  .inputs({op: oneOf('arrive', 'leak'), n: nat})
  .state({level: 0, accepted: 0, sent: 0})
  .flags(({op, n, level, capacity}) => ({fits: op.is('arrive').and(bug === 'checks the old level' ? level.lt(capacity) : level.plus(n).atMost(capacity))}))
  .step(({op, n, rate, level, accepted, sent, fits}) => ({
    level: when(fits, level.plus(n), when(op.is('leak'), level.minus(min(level, rate)), level)),
    accepted: when(fits, accepted.plus(n), accepted),
    sent: when(op.is('leak'), sent.plus(bug === 'counts the full rate' ? rate : min(level, rate)), sent),
  }))
const leakyLaws = [
  leakyBucket().law('level <= capacity', ({level, capacity}) => level.atMost(capacity)),
  leakyBucket().law('sent + level = accepted', ({sent, level, accepted}) => sent.plus(level).eq(accepted)),
]

// A sliding-window limit per client: a request is admitted if its client's requests logged within w before it (`seen`)
// leave room under the limit. `mine` counts one client's (`who`, any client) admitted requests in the window ending at
// now; the relation, proven record by record, says each of them is one `seen` counts for a request of that client at a
// time t <= now. Pruned, requests come in time order and records older than the window are dropped.
const perClient = (pruned: boolean, bug?: 'forgets the request' | 'prunes a tick early') => {
  const base = rule(pruned ? 'per-client sliding window, pruned' : 'per-client sliding window')
    .params({w: nat, limit: nat, who: nat, now: nat})
    .inputs({client: nat, t: nat})
    .log('client', 't')
    .sums({mine: (r, {who, now, w}) => when(r.client.eq(who).and(r.t.atMost(now), now.lt(r.t.plus(w))), 1, 0)})
    .queries({seen: (r, {client, t, w}) => when(r.client.eq(client).and(t.lt(r.t.plus(w))), 1, 0)})
    .flags(({seen, limit}) => ({admitted: (bug === 'forgets the request' ? seen : seen.plus(1)).atMost(limit)}))
    .keep(({admitted}) => admitted)
    .relations(({client, who, t, now, mine, seen}) => [relation(mine.atMost(seen), client.eq(who).and(t.atMost(now)))])
  return pruned ? base.prune('t', ({w}) => (bug === 'prunes a tick early' ? w.minus(1) : w)) : base
}
const windowLaw = perClient(false).law('a client\'s admitted requests in the window ending at now <= limit', ({mine, limit}) => mine.atMost(limit))

// A circuit breaker: closed lets calls through and counts failures; at the threshold it trips open, where no call goes
// through; after `cooldown` ticks it goes half-open and lets exactly one probe through, whose result closes or reopens
// it. `leaked` counts calls let through while open.
const CLOSED = 0, OPEN = 1, HALF = 2
const breaker = (bug?: 'decides by the failure count' | 'half-open lets all through') => rule('circuit breaker')
  .params({threshold: nat, cooldown: nat})
  .inputs({ev: oneOf('call', 'success', 'failure', 'tick')})
  .state({mode: CLOSED, failures: 0, idle: 0, probes: 0, leaked: 0})
  .flags(({ev, mode, failures, threshold, probes}) => ({
    pass: ev.is('call').and(bug === 'decides by the failure count' ? failures.lt(threshold) : bug === 'half-open lets all through' ? mode.ne(OPEN) : mode.eq(CLOSED).or(mode.eq(HALF).and(probes.eq(0)))),
  }))
  .flags(({ev, mode, failures, threshold, idle, cooldown}) => ({
    trip: mode.eq(CLOSED).and(ev.is('failure'), failures.plus(1).atLeast(threshold)).or(mode.eq(HALF).and(ev.is('failure'))),
    retry: mode.eq(OPEN).and(ev.is('tick'), idle.plus(1).atLeast(cooldown)),
  }))
  .step(({ev, mode, failures, idle, probes, leaked, pass, trip, retry}) => ({
    mode: when(trip, OPEN, when(retry, HALF, when(mode.eq(HALF).and(ev.is('success')), CLOSED, mode))),
    failures: when(ev.is('success').or(trip), 0, when(mode.eq(CLOSED).and(ev.is('failure')), failures.plus(1), failures)),
    idle: when(trip, 0, when(mode.eq(OPEN).and(ev.is('tick')), idle.plus(1), idle)),
    probes: when(mode.eq(HALF), when(pass, probes.plus(1), probes), 0),
    leaked: when(pass.and(mode.eq(OPEN)), leaked.plus(1), leaked),
  }))
const breakerLaws = [
  breaker().law('no call goes through while open', ({leaked}) => leaked.eq(0)),
  breaker().law('half-open lets at most one probe through', ({probes}) => probes.atMost(1)),
  breaker().law('the mode is closed, open or half-open', ({mode}) => mode.atMost(HALF)),
]

// A retry loop with backoff: each turn either sleeps one backoff step or makes an attempt (spending a retry and, on
// failure, waiting `delay` steps). The tuple rank (retries left, backoff left) drops on every turn: an attempt lowers
// the first, a sleep the second.
const retry = (bug?: 'counts only successes' | 'caps at tries <= max') => loop(bug ? `retry with backoff, ${bug}` : 'retry with backoff')
  .params({max: nat, delay: nat})
  .inputs({ok: bool})
  .state({left: ({max}) => max, wait: 0, tries: 0, done: 0})
  .while(({left, tries, max, done}) => done.eq(0).and(bug === 'caps at tries <= max' ? tries.atMost(max) : left.gt(0)))
  .body(({ok, delay, left, wait, tries}) => ({
    left: when(wait.gt(0), left, bug === 'counts only successes' ? when(ok, left.minus(1), left) : left.minus(1)),
    wait: when(wait.gt(0), wait.minus(1), delay),
    tries: when(wait.gt(0), tries, bug === 'counts only successes' ? when(ok, tries.plus(1), tries) : tries.plus(1)),
    done: when(wait.eq(0).and(ok), 1, 0),
  }))
  .rank(({left, wait}) => [left, wait])
const retryLaws = (l: ReturnType<typeof retry>) => [
  l.law('tries + retries left = max', ({tries, left, max}) => tries.plus(left).eq(max)),
  l.law('tries <= max', ({tries, max}) => tries.atMost(max)),
  l.law('backoff <= delay', ({wait, delay}) => wait.atMost(delay)),
]

// A bounded queue with backpressure: a batch is enqueued only if it fits (otherwise refused, and counted), a dequeue
// takes what is there up to n.
const queue = (bug?: 'room for one' | 'dequeues the request') => rule('bounded queue')
  .params({capacity: nat})
  .inputs({op: oneOf('enqueue', 'dequeue'), n: nat})
  .state({length: 0, enqueued: 0, dequeued: 0, refused: 0})
  .flags(({op, n, length, capacity}) => ({accepted: op.is('enqueue').and(bug === 'room for one' ? length.lt(capacity) : length.plus(n).atMost(capacity))}))
  .step(({op, n, length, enqueued, dequeued, refused, accepted}) => ({
    length: when(accepted, length.plus(n), when(op.is('dequeue'), length.minus(min(n, length)), length)),
    enqueued: when(accepted, enqueued.plus(n), enqueued),
    dequeued: when(op.is('dequeue'), dequeued.plus(bug === 'dequeues the request' ? n : min(n, length)), dequeued),
    refused: when(op.is('enqueue').and(accepted.not()), refused.plus(1), refused),
  }))
const queueLaws = [
  queue().law('length <= capacity', ({length, capacity}) => length.atMost(capacity)),
  queue().law('dequeued + length = enqueued', ({dequeued, length, enqueued}) => dequeued.plus(length).eq(enqueued)),
]

// An autoscaler: a tick moves the replicas toward the desired count by at most `stepMax`, clamped to [lo, hi]; an
// operator's manual setting is taken only within the bounds.
const autoscaler = (bug?: 'no floor' | 'manual unchecked') => rule('autoscaler')
  .params({lo: nat, hi: nat, stepMax: nat})
  .inputs({op: oneOf('tick', 'manual'), desired: nat})
  .state({replicas: ({lo}) => lo})
  .pre(({lo, hi}) => lo.atMost(hi))
  .step(({op, desired, lo, hi, stepMax, replicas}) => {
    const target = max(replicas.minus(stepMax), min(replicas.plus(stepMax), desired))
    return {
      replicas: when(op.is('manual'),
        when(bug === 'manual unchecked' ? yes : desired.atLeast(lo).and(desired.atMost(hi)), desired, replicas),
        bug === 'no floor' ? min(hi, target) : min(hi, max(lo, target))),
    }
  })
const scalerLaws = [
  autoscaler().law('lo <= replicas', ({lo, replicas}) => lo.atMost(replicas)),
  autoscaler().law('replicas <= hi', ({replicas, hi}) => replicas.atMost(hi)),
]

// A canary rollout: traffic (a percentage) is bumped up to the cap until `need` health checks pass, then up to 100; a
// failed canary rolls back to 0; promotion sends everything once healthy.
const canary = (bug?: 'promotes unchecked' | 'rollback keeps traffic') => rule('canary rollout')
  .params({cap: upTo(100), need: nat})
  .inputs({op: oneOf('bump', 'check', 'fail', 'promote'), by: upTo(100), ok: bool})
  .state({traffic: 0, passes: 0, healthy: 0})
  .step(({op, by, ok, cap, need, traffic, passes, healthy}) => ({
    traffic: op.match({
      bump: () => min(when(healthy.eq(1), 100, cap), traffic.plus(by)),
      check: () => traffic,
      fail: () => (bug === 'rollback keeps traffic' ? traffic : 0),
      promote: () => when(bug === 'promotes unchecked' ? yes : healthy.eq(1), 100, traffic),
    }),
    passes: op.match({bump: () => passes, check: () => when(ok, passes.plus(1), passes), fail: () => 0, promote: () => passes}),
    healthy: op.match({bump: () => healthy, check: () => when(ok.and(passes.plus(1).atLeast(need)), 1, healthy), fail: () => 0, promote: () => healthy}),
  }))
const canaryLaws = [
  canary().law('traffic <= 100%', ({traffic}) => traffic.atMost(100)),
  canary().law('until healthy, traffic <= the cap', ({healthy, traffic, cap}) => healthy.eq(1).or(traffic.atMost(cap))),
]

// A connection pool: an acquire takes a connection if the pool has one free and the client is under its own cap; a
// release gives one back if the client holds one.
const pool = (bug?: 'release unchecked' | 'no per-client cap') => rule('connection pool')
  .params({size: nat, perClient: nat})
  .inputs({op: oneOf('acquire', 'release'), client: nat})
  .state({inUse: 0, acquired: 0, released: 0})
  .maps({Held: 0})
  .flags(({op, client, size, perClient, inUse, Held}) => ({
    got: op.is('acquire').and(inUse.lt(size), bug === 'no per-client cap' ? yes : Held.at(client).lt(perClient)),
    back: op.is('release').and(bug === 'release unchecked' ? yes : Held.at(client).gt(0).and(inUse.gt(0))),
  }))
  .step(({client, inUse, acquired, released, Held, got, back}) => ({
    inUse: when(got, inUse.plus(1), when(back, inUse.minus(1), inUse)),
    acquired: when(got, acquired.plus(1), acquired),
    released: when(back, released.plus(1), released),
    Held: Held.set(client, when(got, Held.at(client).plus(1), when(back, Held.at(client).minus(1), Held.at(client)))),
  }))
const poolLaws = [
  pool().law('in use <= pool size', ({inUse, size}) => inUse.atMost(size)),
  pool().law('in use + released = acquired', ({inUse, released, acquired}) => inUse.plus(released).eq(acquired)),
  pool().law('released <= acquired', ({released, acquired}) => released.atMost(acquired)),
  pool().law('every client holds <= its cap', ({Held, perClient}) => forall(c => Held.at(c).atMost(perClient))),
]

// A feature flag's rollout percentage: a new setting is taken only if it doesn't lower the percentage, and the kill
// switch drops it to 0 for good. `before` is the percentage before the last step, so "only increases" is a law.
const featureFlag = (bug?: 'takes any setting' | 'revives after the kill') => rule('feature flag rollout')
  .inputs({op: oneOf('set', 'kill'), pct: upTo(100)})
  .state({percent: 0, before: 0, killed: 0})
  .step(({op, pct, percent, killed}) => ({
    before: percent,
    percent: when(op.is('kill'), 0, when((bug === 'revives after the kill' ? yes : killed.eq(0)).and(bug === 'takes any setting' ? yes : pct.atLeast(percent)), pct, percent)),
    killed: when(op.is('kill'), 1, killed),
  }))
const flagLaws = [
  featureFlag().law('percent <= 100', ({percent}) => percent.atMost(100)),
  featureFlag().law('until killed, the percentage only increases', ({killed, before, percent}) => killed.eq(1).or(before.atMost(percent))),
  featureFlag().law('killed means 0%', ({killed, percent}) => killed.eq(0).or(percent.eq(0))),
]

// Load shedding at the edge: a draining node admits nothing; internal traffic is always welcome otherwise; paid traffic
// while the queue is at most 90% full; free traffic only with a measured latency within the SLO and the queue at most
// half full.
const shed = rule('load shedding')
  .params({slo: nat})
  .inputs({tier: oneOf('free', 'paid', 'internal'), latency: maybe(nat), queue: upTo(100), draining: bool})
const admit = ({slo, tier, latency, queue, draining}: {slo: Term, tier: Choice<'free' | 'paid' | 'internal'>, latency: Maybe<Term>, queue: Term, draining: Bool}) =>
  draining.not().and(tier.match({
    internal: () => yes,
    paid: () => queue.atMost(90),
    free: () => queue.atMost(50).and(latency.match({none: () => no, some: l => l.atMost(slo)})),
  }))
const shedDecisions = [
  shed.decide('a draining node admits nothing', ({draining}) => draining, env => admit(env).not()),
  shed.decide('free traffic with no latency measurement is shed', ({tier, latency}) => [tier.is('free'), latency.isNone], env => admit(env).not()),
  shed.decide('admitted outside traffic leaves 10% of the queue', env => [admit(env), env.tier.is('internal').not()], ({queue}) => queue.atMost(90)),
]
const shedInternalAlways = shed.decide('internal traffic is always admitted', ({tier}) => tier.is('internal'), env => admit(env))
const shedFreeUnmeasured = shed.decide('free traffic within the queue is admitted', ({tier, queue, draining}) => [tier.is('free'), queue.atMost(50), draining.not()], env => admit(env))

export const domain: Domain = {
  domain: 'operations',
  about: 'rate limiters, circuit breakers, retries, queues, autoscaling, canaries, pools, feature flags, load shedding',
  cases: [
    machineCase('token bucket', 'the bucket never overflows, and served requests never pass the bucket plus its refills', tokenBucket(), bucketLaws, [
      {name: 'checks the size', why: 'a take is checked against the bucket size, not the tokens in it', rule: tokenBucket('checks the size'), laws: bucketLaws},
      {name: 'no clamp', why: 'a refill forgets to stop at the bucket size', rule: tokenBucket('no clamp'), laws: bucketLaws},
    ]),
    machineCase('leaky bucket', 'the bucket stays within capacity, and sent plus queued is exactly what was accepted', leakyBucket(), leakyLaws, [
      {name: 'checks the old level', why: 'an arrival is checked for room before its own size is added', rule: leakyBucket('checks the old level'), laws: leakyLaws},
      {name: 'counts the full rate', why: 'a leak counts the full rate as sent even when the bucket holds less', rule: leakyBucket('counts the full rate'), laws: leakyLaws},
    ]),
    machineCase('per-client sliding window', 'every client\'s admitted requests in any window ending at now stay within the limit, read from the log', perClient(false), [windowLaw], [
      {name: 'forgets the request', why: 'the check reads the client\'s window without the request itself (an off-by-one)', rule: perClient(false, 'forgets the request'), laws: [windowLaw]},
    ]),
    machineCase('per-client sliding window, pruned', 'the same, the log dropping requests older than the window', perClient(true), [windowLaw], [
      {name: 'prunes a tick early', why: 'records are dropped at w - 1, while the window still counts them', rule: perClient(true, 'prunes a tick early'), laws: [windowLaw]},
    ]),
    machineCase('circuit breaker', 'no call goes through while open, and half-open lets one probe through', breaker(), breakerLaws, [
      {name: 'decides by the failure count', why: 'calls pass while failures are under the threshold, but tripping resets the count', rule: breaker('decides by the failure count'), laws: breakerLaws},
      {name: 'half-open lets all through', why: 'half-open forgets that only one probe may be in flight', rule: breaker('half-open lets all through'), laws: breakerLaws},
    ], {depth: 16}),
    loopCase('retry with backoff', 'retries end (the rank: retries left, then backoff left), with at most max attempts', retry(), retryLaws(retry()), [
      {name: 'counts only successes', why: 'a failed attempt isn\'t counted, so a call that keeps failing is retried forever', loop: retry('counts only successes'), laws: retryLaws(retry('counts only successes'))},
      {name: 'caps at tries <= max', why: 'the loop condition allows one attempt past the cap', loop: retry('caps at tries <= max'), laws: retryLaws(retry('caps at tries <= max'))},
    ]),
    machineCase('bounded queue', 'the queue never passes its capacity, and nothing is lost or invented', queue(), queueLaws, [
      {name: 'room for one', why: 'a batch is accepted when there is room for one item', rule: queue('room for one'), laws: queueLaws},
      {name: 'dequeues the request', why: 'a dequeue counts what was asked for, not what was there', rule: queue('dequeues the request'), laws: queueLaws},
    ]),
    machineCase('autoscaler', 'replicas stay within [lo, hi]', autoscaler(), scalerLaws, [
      {name: 'no floor', why: 'scaling down clamps to hi but forgets lo', rule: autoscaler('no floor'), laws: scalerLaws},
      {name: 'manual unchecked', why: 'an operator\'s setting bypasses the bounds', rule: autoscaler('manual unchecked'), laws: scalerLaws},
    ]),
    machineCase('canary rollout', 'traffic never passes the cap until the canary is healthy', canary(), canaryLaws, [
      {name: 'promotes unchecked', why: 'promotion forgets to check the health', rule: canary('promotes unchecked'), laws: canaryLaws},
      {name: 'rollback keeps traffic', why: 'a failure marks the canary unhealthy but leaves its traffic', rule: canary('rollback keeps traffic'), laws: canaryLaws},
    ]),
    machineCase('connection pool', 'in use within the pool size, released within acquired, every client within its cap', pool(), poolLaws, [
      {name: 'release unchecked', why: 'a double release is counted though nothing was held', rule: pool('release unchecked'), laws: poolLaws},
      {name: 'no per-client cap', why: 'an acquire checks the pool but not the client\'s own cap', rule: pool('no per-client cap'), laws: poolLaws},
    ]),
    machineCase('feature flag rollout', 'the rollout percentage only increases until the kill switch, which holds it at 0', featureFlag(), flagLaws, [
      {name: 'takes any setting', why: 'a setting below the current percentage is taken', rule: featureFlag('takes any setting'), laws: flagLaws},
      {name: 'revives after the kill', why: 'a setting after the kill switch turns the flag back on', rule: featureFlag('revives after the kill'), laws: flagLaws},
    ]),
    decisionCase('load shedding', 'draining sheds everything, unmeasured free traffic is shed, admitted outside traffic leaves headroom', shedDecisions, [
      {name: 'internal traffic is always admitted', why: 'a draining node sheds internal traffic too', decision: shedInternalAlways},
      {name: 'free traffic within the queue is admitted', why: 'free traffic also needs a measured latency within the SLO', decision: shedFreeUnmeasured},
    ]),
  ],
}
