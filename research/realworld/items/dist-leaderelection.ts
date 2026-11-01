// kubernetes/client-go at b51563e, tools/leaderelection: LeaderElector.tryAcquireOrRenew over a LeaseLock (the leader
// lease every controller manager and scheduler runs). Apache-2.0, (c) The Kubernetes Authors.
// https://github.com/kubernetes/client-go/blob/b51563e839b761a4b85dca15faf4a9bac49a84c0/tools/leaderelection/leaderelection.go
//
// Mapping:
// - Candidates are ids >= 1 (Lock.Identity()); 0 is the empty HolderIdentity. Each keeps its own observedRecord
//   (holder, LeaderTransitions), observedTime, observedRawRecord and the LeaseLock's cached lease (`Seen`, `Cache`:
//   the resourceVersion of the record they were read or written at; the raw record's bytes change with every write,
//   as RenewTime does, so a version stands for them).
// - The lease is one object on the API server: `holder`, `trans` and its resourceVersion `rv`. Update is a
//   compare-and-swap on the cached lease's resourceVersion (leaselock.go:73-95, the API server's optimistic
//   concurrency); Create fails when the lease exists.
// - One call of tryAcquireOrRenew is up to three API calls, each its own request (`fast`: step 1's optimistic Update;
//   `get`: step 2-3's Get, or Create when there is none, and the decision; `put`: step 4's Update), so other
//   candidates' calls interleave between them as they do on the wire. `err`: the API call fails (a timeout, a conflict
//   the server reports, any error).
// - Time: `now`, in seconds, sent in, one time line read by every candidate (clocks at one rate: the docs' skew-rate
//   tolerance is not modelled). LeaseDurationSeconds is the config's `D`, the same for every candidate.
// - Ghosts: `clock`, the latest time seen; `wrote`, the time of the last successful write to the lease.
import {bool, max, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, stepLaw} from '../lib.ts'

const src = {repo: 'kubernetes/client-go', commit: 'b51563e839b761a4b85dca15faf4a9bac49a84c0', licence: 'Apache-2.0', author: 'The Kubernetes Authors', language: 'Go'}
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})

export const leaderElector = () => rule('client-go LeaderElector over a LeaseLock')
  .params({D: nat})
  .pre(({D}) => D.atLeast(1))
  .inputs({op: oneOf('fast', 'get', 'put'), c: nat, now: nat, err: bool})
  .state({exists: bool.from(false), holder: 0, trans: 0, rv: 0, clock: 0, wrote: 0})
  // Per candidate: observedRecord's holder and transitions, observedTime, observedRawRecord's version, the cached
  // lease's version (0: none yet), and a planned step-4 Update (`Plan`: none, as leader, as a new leader).
  .maps({OH: 0, OT: 0, OTime: 0, Seen: 0, Cache: 0, Plan: oneOf('none', 'renew', 'take').from('none')})
  .assume(({c, now, clock}) => c.atLeast(1).and(now.atLeast(clock)))
  .flags(({op, c, now, err, D, exists, holder, rv, OH, OTime, Seen, Cache, Plan}) => {
    const leader = OH.at(c).eq(c) // IsLeader (:327-329)
    const valid = (t: typeof now) => OTime.at(c).plus(D).gt(t) // isLeaseValid (:874-882)
    const cas = exists.and(Cache.at(c).eq(rv), Cache.at(c).gt(0), err.not())
    // step 1 (:766-779): the leader, its lease valid by its clock, updates optimistically.
    const fastWrites = op.is('fast').and(leader, valid(now), cas)
    // step 2 (:782-796): no lease: Create (fails if another created it first).
    const creates = op.is('get').and(exists.not(), err.not())
    const reads = op.is('get').and(exists, err.not())
    // step 3 (:799-807): a changed raw record is observed now; a lease held by another and valid is left alone.
    const changed = reads.and(Seen.at(c).eq(rv).not())
    const oh = when(changed, holder, OH.at(c)), ot = when(changed, now, OTime.at(c))
    const blocked = oh.gt(0).and(ot.plus(D).gt(now), oh.eq(c).not())
    const plans = reads.and(blocked.not())
    // step 4 (:809-826): the Update, with the cached lease's version.
    const puts = op.is('put').and(Plan.at(c).is('none').not(), cas)
    return {fastWrites, creates, reads, changed, plans, plansRenew: plans.and(oh.eq(c)), puts, writes: fastWrites.or(creates, puts)}
  })
  .step(({op, c, now, holder, trans, rv, exists, clock, wrote, OH, OT, OTime, Seen, Cache, Plan, fastWrites, creates, reads, changed, plans, plansRenew, writes}) => {
    // The record written: the leader keeps AcquireTime and LeaderTransitions (fast: the observed record's; step 4:
    // the record just read); a new leader writes transitions + 1 (:812-818); a created lease 0.
    const newTrans = when(creates, 0, when(fastWrites, OT.at(c), when(Plan.at(c).is('renew'), trans, trans.plus(1))))
    const at = (k: typeof c) => k.eq(c)
    return {
      exists: exists.or(creates),
      holder: when(writes, c, holder),
      trans: when(writes, newTrans, trans),
      rv: when(writes, rv.plus(1), rv),
      clock: max(clock, now),
      wrote: when(writes, now, wrote),
      // setObservedRecord (:884-892) after every successful write and on a changed raw record; observedRawRecord only
      // on the latter (:799-803).
      OH: OH.each(k => when(at(k).and(writes), c, when(at(k).and(changed), holder, OH.at(k)))),
      OT: OT.each(k => when(at(k).and(writes), newTrans, when(at(k).and(changed), trans, OT.at(k)))),
      OTime: OTime.each(k => when(at(k).and(writes.or(changed)), now, OTime.at(k))),
      Seen: Seen.each(k => when(at(k).and(changed), rv, Seen.at(k))),
      // ll.lease: set by Get, Create and a successful Update (leaselock.go:42-95).
      Cache: Cache.each(k => when(at(k).and(writes), rv.plus(1), when(at(k).and(reads), rv, Cache.at(k)))),
      Plan: Plan.each(k => when(at(k).and(plansRenew), 'renew', when(at(k).and(plans), 'take', when(at(k).and(op.is('get').or(op.is('put'))), 'none', Plan.at(k))))),
    }
  })

const r = leaderElector()
export const items: RealItem[] = [{
  id: 'distributed/client-go/leaderelection',
  domain: 'distributed',
  source: cite('tools/leaderelection/leaderelection.go', '749-826,874-892', 'LeaderElector.tryAcquireOrRenew, isLeaseValid, setObservedRecord'),
  also: [cite('tools/leaderelection/resourcelock/leaselock.go', '42-95', 'LeaseLock.Get, Create, Update'), cite('tools/leaderelection/leaderelection.go', '17-45,137-150', 'package doc, LeaseDuration')],
  summary: 'Candidates race for one Lease object: a candidate takes it only once it has watched the record go unchanged for a full LeaseDuration on its own clock; the holder renews it, first optimistically, then through a fresh read; every write is a compare-and-swap on the resource version.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'each API call is one request; the renew loop, RetryPeriod, RenewDeadline and the callbacks are left out'},
    {gap: 'time', blocks: 'part', detail: 'le.clock.Now() read inside the call is the request\'s `now`; one time line for every candidate (no clock skew rate)'},
    {gap: 'external', blocks: 'part', detail: 'the API server\'s optimistic concurrency (resourceVersion) is the CAS the rule states'},
    {gap: 'scope', blocks: 'part', detail: 'release (ReleaseOnCancel), coordinated leader election and lease recovery left out; every candidate has the same LeaseDuration'},
  ],
  laws: [
    stepLaw(r, r.stepLaw('the lease changes hands only after a full LeaseDuration without a write', ({now, wrote, D}) => wrote.plus(D).atMost(now),
      ({writes, exists, holder, c}) => writes.and(exists, holder.gt(0), holder.eq(c).not())),
    'safety', 'docs', 'leaderelection.go:137-142 "LeaseDuration is the duration that non-leader candidates will wait to force acquire leadership... A client needs to wait a full LeaseDuration without observing a change to the record before it can attempt to take over"'),
    stepLaw(r, r.stepLaw('LeaderTransitions grows by one exactly when the holder changes', ({holder, trans}, after) => after.trans.eq(when(after.holder.eq(holder), trans, trans.plus(1))),
      ({writes, exists}) => writes.and(exists)), 'step', 'docs', 'leaderelection.go:812-818: a leader keeps LeaderTransitions, a new leader writes it + 1'),
    stepLaw(r, r.stepLaw('an optimistic renewal only renews the candidate\'s own lease', ({holder, c}) => holder.eq(c), ({fastWrites}) => fastWrites),
      'safety', 'docs', 'leaderelection.go:766-767 "fast path for the leader to update optimistically assuming that the record observed last time is the current version"'),
    stepLaw(r, r.stepLaw('a candidate that sees a valid lease held by another writes nothing', ({holder, rv}, after) => after.holder.eq(holder).and(after.rv.eq(rv)),
      ({op, reads, plans}) => op.is('get').and(reads, plans.not())), 'step', 'docs', 'leaderelection.go:804-807 "Lease is held by and has not yet expired": return false'),
  ],
}]

