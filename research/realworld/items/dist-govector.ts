// DistributedClocks/GoVector at ae07272: one process's vector clock as its GoLog keeps it (govec/govec.go:
// tickClock, LogLocalEvent, PrepareSend, mergeIncomingClock, UnpackReceive) over govec/vclock/vclock.go (Tick, Merge).
// MIT, (c) the GoVector authors (DistributedClocks, UBC).
// https://github.com/DistributedClocks/GoVector/blob/ae07272d0ebd45e80275adb5b83e121df02719d8/govec/vclock/vclock.go
//
// Mapping:
// - `VC[k]`: currentVC[k] for process id k (an absent key reads 0, as Go's map does; presence is read only by Compare,
//   left out). `me`: gv.pid. InitGoVector's own Tick(pid) is the first `local` event.
// - A received message carries the sender's clock (`Other`, VClockPayload.VcMap). The environment's own law is
//   assumed of it: no sender knows more of this process's events than it has had (Other[me] <= VC[me]); every other
//   entry is any value.
// - Ghost: `events`, the events this process logged (local, send, receive), each one tickClock.
import {forall, max, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'DistributedClocks/GoVector', commit: 'ae07272d0ebd45e80275adb5b83e121df02719d8', licence: 'MIT', author: 'DistributedClocks (GoVector authors)', language: 'Go'}
export const goLog = () => rule('GoVector GoLog vector clock')
  .params({me: nat})
  .inputs({op: oneOf('local', 'send', 'receive')})
  .carries('Other')
  .state({events: 0})
  .maps({VC: 0})
  .assume(({op, me, Other, VC}) => op.is('receive').implies(Other.at(me).atMost(VC.at(me))))
  .step(({op, me, Other, events, VC}) => ({
    events: events.plus(1),
    // tickClock (govec.go:483-489) then, for a receive, Merge (vclock.go:81-87: each entry the larger of the two).
    VC: VC.each(k => {
      const ticked = when(k.eq(me), VC.at(k).plus(1), VC.at(k))
      return when(op.is('receive'), max(ticked, Other.at(k)), ticked)
    }),
  }))

const g = goLog()
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})
export const items: RealItem[] = [{
  id: 'distributed/GoVector/vclock',
  domain: 'distributed',
  source: cite('govec/vclock/vclock.go', '59-87', 'VClock.Tick, Merge'),
  also: [cite('govec/govec.go', '483-580', 'GoLog.tickClock, LogLocalEvent, PrepareSend, mergeIncomingClock, UnpackReceive')],
  summary: 'A process\'s vector clock: each local event, send and receive ticks its own entry; a receive then takes the larger of each entry and the sender\'s.',
  expressible: 'partial',
  gaps: [
    {gap: 'string', blocks: 'part', detail: 'process ids are strings in the code, naturals here (compared only for equality)'},
    {gap: 'scope', blocks: 'part', detail: 'Compare (its length-based shortcut reads which keys are present), Set, CopyFromMap, broadcast mode and log priorities left out'},
  ],
  laws: [
    stepLaw(g, g.stepLaw('no entry of the clock ever decreases', ({VC}, after) => forall(k => VC.at(k).atMost(after.VC.at(k)))), 'safety', 'docs', 'vclock.go:79-80 Merge "takes the max of all clock values in other"; Tick adds one'),
    stepLaw(g, g.stepLaw('after a receive the clock is at least the sender\'s everywhere', ({Other}, after) => forall(k => Other.at(k).atMost(after.VC.at(k))), ({op}) => op.is('receive')),
      'safety', 'docs', 'vclock.go:79-80 "Merge takes the max of all clock values in other and updates the values of the callee"'),
    invariant(g, g.law('the process\'s own entry counts its events', ({VC, me, events}) => VC.at(me).eq(events)), 'safety', 'inferred', 'the vector clock definition: a process\'s own entry is the number of its events; govec.go ticks once per logged event'),
    stepLaw(g, g.stepLaw('every event advances the process\'s own entry by one', ({VC, me}, after) => after.VC.at(me).eq(VC.at(me).plus(1))), 'step', 'docs', 'govec.go:483-489 tickClock on every LogLocalEvent, PrepareSend and UnpackReceive'),
  ],
}]
