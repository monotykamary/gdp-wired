// Telecom and networking: a token bucket, connections per IP, a SYN window, a congestion window, a DHCP pool, firewall
// rules, retransmission that gives up.
import {type Bool, type Choice, type Maybe, type Term, bool, count, forall, loop, max, maybe, min, nat, no, oneOf, relation, rule, upTo, when} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A token bucket: each tick adds `rate` tokens up to the capacity; a request of `cost` goes through only if the bucket
// holds that many. What was served is bounded by the capacity plus everything the ticks added (a product of two terms).
const bucket = (bug?: 'refill unclamped') => rule('token bucket')
  .params({capacity: nat, rate: nat})
  .inputs({op: oneOf('tick', 'request'), cost: nat})
  .state({tokens: 0, ticks: 0, served: 0})
  .flags(({op, cost, tokens}) => ({serves: op.is('request').and(cost.atMost(tokens))}))
  .step(({op, cost, capacity, rate, tokens, ticks, served, serves}) => ({
    tokens: when(op.is('tick'), bug ? tokens.plus(rate) : min(capacity, tokens.plus(rate)), when(serves, tokens.minus(cost), tokens)),
    ticks: when(op.is('tick'), ticks.plus(1), ticks),
    served: when(serves, served.plus(cost), served),
  }))
const bucketLaws = (r: ReturnType<typeof bucket>) => [
  r.law('tokens <= capacity', ({tokens, capacity}) => tokens.atMost(capacity)),
  r.law('served + tokens <= rate × ticks', ({served, tokens, rate, ticks}) => served.plus(tokens).atMost(rate.mul(ticks))),
]
const bucketUnclamped = bucket('refill unclamped')

// Connections per IP: a new connection opens only while the address is under its limit; closing frees one.
const conns = (bug?: 'off by one') => rule('connections per IP')
  .params({limit: nat})
  .inputs({op: oneOf('open', 'close'), ip: nat})
  .maps({Open: 0})
  .flags(({op, ip, limit, Open}) => ({opens: op.is('open').and(bug ? Open.at(ip).atMost(limit) : Open.at(ip).lt(limit))}))
  .step(({op, ip, opens, Open}) => ({Open: Open.set(ip, when(opens, Open.at(ip).plus(1), when(op.is('close'), Open.at(ip).minus(1), Open.at(ip))))}))
const connLaw = (r: ReturnType<typeof conns>) => r.law('every IP: open connections <= limit', ({Open, limit}) => forall(k => Open.at(k).atMost(limit)))
const connsOff = conns('off by one')

// A SYN window: at most `limit` half-open handshakes accepted in any `window` ticks, read from the log of accepted SYNs.
const syn = (opts: {pruned?: boolean, bug?: 'prunes early'} = {}) => {
  const base = rule(opts.pruned ? 'SYN flood window, pruned' : 'SYN flood window')
    .params({window: nat, limit: nat, now: nat})
    .inputs({t: nat})
    .log('t')
    .sums({recent: (r, {now, window}) => count(r.t.atMost(now).and(now.lt(r.t.plus(window))))})
    .queries({seen: (r, {t, window}) => count(t.lt(r.t.plus(window)))})
    .flags(({seen, limit}) => ({accepts: seen.plus(1).atMost(limit)}))
    .keep(({accepts}) => accepts)
    .relations(({t, now, recent, seen}) => [relation(recent.atMost(seen), t.atMost(now))])
  return opts.pruned ? base.prune('t', ({window}) => (opts.bug ? window.minus(1) : window)) : base
}
const synLaw = (r: ReturnType<typeof syn>) => r.law('SYNs accepted in the window ending at now <= limit', ({recent, limit}) => recent.atMost(limit))
const synEarly = syn({pruned: true, bug: 'prunes early'})

// A congestion window: each ack grows it by one up to the receiver's window, a loss cuts it by `backoff` but never below
// one segment. Bounds are laws; "an ack grows it by at most one" is a law about the step.
const cwnd = (bug?: 'slow start unbounded') => rule('congestion window')
  .params({rwnd: nat, backoff: nat})
  .inputs({op: oneOf('ack', 'loss')})
  .pre(({rwnd}) => rwnd.atLeast(1))
  .state({w: 1})
  .step(({op, rwnd, backoff, w}) => ({w: when(op.is('ack'), bug ? w.plus(w) : min(rwnd, w.plus(1)), max(1, w.minus(backoff)))}))
const cwndLaws = (r: ReturnType<typeof cwnd>) => [
  r.law('the window <= the receiver\'s window', ({w, rwnd}) => w.atMost(rwnd)),
  r.law('the window >= one segment', ({w}) => w.atLeast(1)),
]
const cwndSteps = (r: ReturnType<typeof cwnd>) => [r.stepLaw('an ack grows the window by at most one segment', ({w}, after) => after.w.atMost(w.plus(1)), ({op}) => op.is('ack'))]
const cwndSlowStart = cwnd('slow start unbounded')

// A DHCP pool: an address is leased only when free and the client holds no lease; a release frees it only for its
// holder. Each client holds at most one lease, and a leased address never changes hands without a release.
const dhcp = (bug?: 'leases a taken address') => rule('DHCP pool')
  .inputs({op: oneOf('lease', 'release'), addr: nat, client: upTo(15)})
  .maps({Holder: 0, Leases: 0})
  .flags(({op, addr, client, Holder, Leases}) => ({
    leases: op.is('lease').and(client.gt(0), Leases.at(client).eq(0), bug ? client.gt(0) : Holder.at(addr).eq(0)),
    releases: op.is('release').and(client.gt(0), Holder.at(addr).eq(client)),
  }))
  .step(({addr, client, leases, releases, Holder, Leases}) => ({
    Holder: Holder.set(addr, when(leases, client, when(releases, 0, Holder.at(addr)))),
    Leases: Leases.set(client, when(leases, Leases.at(client).plus(1), when(releases, Leases.at(client).minus(1), Leases.at(client)))),
  }))
const dhcpLaws = (r: ReturnType<typeof dhcp>) => [r.law('every client holds at most one lease', ({Leases}) => forall(c => Leases.at(c).atMost(1)))]
const dhcpSteps = (r: ReturnType<typeof dhcp>) => [
  r.stepLaw('a lease never takes an address someone holds', ({addr, Holder}, after) => Holder.at(addr).eq(0).or(after.Holder.at(addr).eq(Holder.at(addr))), ({op}) => op.is('lease')),
]
const dhcpTaken = dhcp('leases a taken address')

// Firewall rules: SSH only from the admin network; nothing from a blocked source, and a source with no blocklist answer
// is treated as blocked; ICMP only from inside. Ports are service ids here: 2 is SSH, 3 is DNS.
const SSH = 2, DNS = 3
const fw = rule('firewall rules').inputs({proto: oneOf('tcp', 'udp', 'icmp'), port: upTo(7), source: oneOf('internal', 'admin', 'external'), blocked: maybe(bool)})
type FwEnv = {proto: Choice<'tcp' | 'udp' | 'icmp'>, port: Term, source: Choice<'internal' | 'admin' | 'external'>, blocked: Maybe<Bool>}
const clean = ({blocked}: Pick<FwEnv, 'blocked'>) => blocked.match({none: () => no, some: b => b.not()})
const accept = (env: FwEnv) => clean(env).and(env.proto.match({
  tcp: () => env.port.eq(SSH).implies(env.source.is('admin')),
  udp: () => env.port.eq(DNS).or(env.source.is('external').not()),
  icmp: () => env.source.is('external').not(),
}))
const acceptUnknownClean = (env: FwEnv) => env.blocked.match({none: () => env.proto.is('icmp').not(), some: b => b.not()}).and(env.proto.match({
  tcp: () => env.port.eq(SSH).implies(env.source.is('admin')),
  udp: () => env.port.eq(DNS).or(env.source.is('external').not()),
  icmp: () => env.source.is('external').not(),
}))
const fwDecisions = [
  fw.decide('SSH only from the admin network', env => [env.proto.is('tcp'), env.port.eq(SSH), accept(env)], env => env.source.is('admin')),
  fw.decide('no blocklist answer, nothing accepted', env => env.blocked.isNone, env => accept(env).not()),
  fw.decide('no ICMP from outside', env => [env.proto.is('icmp'), env.source.is('external')], env => accept(env).not()),
]
const fwUnknownClean = fw.decide('no blocklist answer, nothing accepted', env => env.blocked.isNone, env => acceptUnknownClean(env).not())

// Retransmission: unacked segments are resent until all are acked or the tries run out; each turn spends a try. A
// partial ack must not refill the tries, or a lossy link retries forever.
const retransmit = (refills: boolean) => loop(refills ? 'retransmission, tries refilled on a partial ack' : 'retransmission')
  .params({segments: nat, tries: nat})
  .inputs({acked: nat})
  .state({left: ({segments}) => segments, budget: ({tries}) => tries})
  .while(({left, budget}) => left.gt(0).and(budget.gt(0)))
  .body(({left, budget, acked, tries}) => ({left: left.minus(min(left, acked)), budget: refills ? when(acked.gt(0), tries, budget.minus(1)) : budget.minus(1)}))
  .rank(({budget}) => budget)
const retransmitLaws = (r: ReturnType<typeof retransmit>) => [r.law('tries left <= tries', ({budget, tries}) => budget.atMost(tries)), r.law('segments left <= segments', ({left, segments}) => left.atMost(segments))]

export const domain: Domain = {
  domain: 'networking',
  about: 'token buckets, connections per IP, SYN windows, congestion windows, DHCP pools, firewall rules, retransmission',
  cases: [
    machineCase('token bucket', 'the bucket never overflows, and what was served never passes what the ticks added', bucket(), bucketLaws(bucket()), [
      {name: 'refill unclamped', why: 'a tick adds the rate without the capacity clamp', rule: bucketUnclamped, laws: bucketLaws(bucketUnclamped)},
    ]),
    machineCase('connections per IP', 'no address holds more than `limit` connections', conns(), [connLaw(conns())], [
      {name: 'off by one', why: 'the check admits a connection at the limit', rule: connsOff, laws: [connLaw(connsOff)]},
    ]),
    machineCase('SYN flood window', 'at most `limit` SYNs accepted in any window, read from the log', syn(), [synLaw(syn())]),
    machineCase('SYN flood window, pruned', 'the same, the log dropping SYNs older than the window', syn({pruned: true}), [synLaw(syn({pruned: true}))], [
      {name: 'prunes one tick early', why: 'a SYN still inside the window is dropped, so the next request sees one fewer', rule: synEarly, laws: [synLaw(synEarly)]},
    ]),
    machineCase('congestion window', 'the window stays within one segment and the receiver\'s window, and an ack grows it by one', cwnd(), cwndLaws(cwnd()), [
      {name: 'slow start unbounded', why: 'an ack doubles the window with no cap at the receiver\'s window', rule: cwndSlowStart, laws: cwndLaws(cwndSlowStart), steps: cwndSteps(cwndSlowStart)},
    ], {steps: cwndSteps(cwnd())}),
    machineCase('DHCP pool', 'each client holds one lease at most, and a held address is never leased again', dhcp(), dhcpLaws(dhcp()), [
      {name: 'leases a taken address', why: 'a lease forgets to check the address is free, taking it from its holder', rule: dhcpTaken, laws: dhcpLaws(dhcpTaken), steps: dhcpSteps(dhcpTaken)},
    ], {steps: dhcpSteps(dhcp())}),
    decisionCase('firewall rules', 'SSH from admins only, unknown sources fail closed, no ICMP from outside', fwDecisions, [
      {name: 'unknown source read as clean', why: 'a source with no blocklist answer is accepted for TCP and UDP', decision: fwUnknownClean},
    ]),
    loopCase('retransmission', 'each turn spends a try, so resending ends', retransmit(false), retransmitLaws(retransmit(false)), [
      {name: 'tries refilled on a partial ack', why: 'a partial ack refills the tries, so a link that acks a little each time retries forever', loop: retransmit(true), laws: retransmitLaws(retransmit(true))},
    ]),
  ],
}
