// Repro for approval/openzeppelin/Governor's refuted laws (Solidity: not run; reasoned from the source at
// OpenZeppelin/openzeppelin-contracts@cab19933c33c2ad1d4c7a84864a3601dddfd16f3, MIT, and replayed on the rule).
//
// GovernorTimelockControl._queueOperations (GovernorTimelockControl.sol:81-93) schedules the proposal's batch on the
// timelock with predecessor 0 and salt bytes20(governor) ^ descriptionHash, and records the id in _timelockIds; its
// _cancel (:121-138) cancels a timelock operation only when _timelockIds[proposalId] != 0, i.e. only one it queued.
// TimelockController.scheduleBatch (TimelockController.sol:289-312) lets any PROPOSER_ROLE holder schedule any id,
// and executeBatch (:383-408) lets any EXECUTOR_ROLE holder (or anyone, if the role is open) execute it once ready.
// So with a second proposer on the timelock: that account schedules the same calls with the same salt (the same id),
// waits minDelay and executes them, while the Governor's proposal is Pending, Active, Defeated or Canceled. The
// Governor's state() never looks at the timelock outside Queued (GovernorTimelockControl.sol:43-60). This is the
// documented risk (GovernorTimelockControl.sol:19-22 "Setting up the TimelockController to have additional proposers
// or cancelers besides the governor is very risky, as it grants them the ability to: 1) execute operations as the
// timelock"), so the laws were restated to the setup the docs prescribe.
//   bun research/realworld/repro/governor.ts
import {governor} from '../items/invapprove-governor.ts'

const r = governor(), m = r.interpreter()
const p = r.encodeParams({votingDelay: 5, votingPeriod: 5, quorum: 1, threshold: 0, minDelay: 2, others: true, other: 9, open: false, b0: 1, t0: 2})
let st = m.init(p)
const base = {sender: 0, support: 'for', weight: 0, db: 0, dt: 0}
for (const i of [{op: 'tlSchedule', sender: 9}, {op: 'propose', sender: 1}, {op: 'cancel', sender: 1}, {op: 'wait', dt: 3}, {op: 'tlExecute', sender: 9}]) {
  st = m.step(p, st, r.encodeInput({...base, ...i}))
  const d = r.decode(st) as Record<string, unknown>
  console.log(i.op.padEnd(10), JSON.stringify({canceled: d.canceled, executed: d.executed, timelockTimestamp: d.Ts, callsRun: d.runs}))
}
