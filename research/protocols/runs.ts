// Hand-written runs of the broken variants the search did not refute (research/protocols/README.md), replayed by the
// interpreter on each variant: the broken one ends with two leaders, the correct one with one.
//   bun research/protocols/runs.ts
import {interpret} from '../../core/machine.ts'
import {protocols} from './models.ts'

const runs: Record<string, {params: Record<string, number>, trace: Record<string, unknown>[]}> = {
  // two nodes vote twice each (no `voted` check): 0 and 1 both win the quorum {0, 1}
  consensus_wo_decide: {params: {}, trace: [
    {op: 'init', Q: [0, 1], w: 0},
    {op: 'send_request_vote', src: 0, dst: 0}, {op: 'send_request_vote', src: 0, dst: 1}, {op: 'send_request_vote', src: 1, dst: 0}, {op: 'send_request_vote', src: 1, dst: 1},
    {op: 'send_vote', src: 0, dst: 0, nondet: true}, {op: 'send_vote', src: 1, dst: 0, nondet: true}, {op: 'send_vote', src: 0, dst: 1, nondet: true}, {op: 'send_vote', src: 1, dst: 1, nondet: true},
    {op: 'recv_vote', dst: 0, src: 0}, {op: 'recv_vote', dst: 0, src: 1}, {op: 'recv_vote', dst: 1, src: 0}, {op: 'recv_vote', dst: 1, src: 1},
    {op: 'become_leader', src: 0}, {op: 'become_leader', src: 1},
  ]},
  // a ring of two forwarding every id: each id comes back to its owner, two leaders
  ring_leader_election: {params: {size: 2}, trace: [
    {op: 'send', n: 0, n1: 1}, {op: 'send', n: 1, n1: 0},
    {op: 'receive', n: 1, m: 0 ^ 5, n1: 0}, {op: 'receive', n: 0, m: 1 ^ 5, n1: 1},
    {op: 'become_leader', n: 0}, {op: 'become_leader', n: 1},
  ]},
}
for (const [id, {params, trace}] of Object.entries(runs)) for (const bug of [undefined, 'bug']) {
  const p = protocols.find(q => q.id === id)!, r = p.make(bug && p.bug), run = interpret(r.machine), ps = r.encodeParams(params)
  const fill = (i: Record<string, unknown>) => ({...Object.fromEntries(r.machine.inputs.map((k: string) => [k, k === 'nondet' ? false : 0])), ...((r.machine.inputMaps ?? []).length ? {Q: []} : {}), ...i})
  let st = run.init(ps)
  for (const i of trace) st = run.step(ps, st, r.encodeInput(fill(i), params))
  const leaders = [...(st.maps.Leader as Map<number, number>)].filter(([, c]) => c).map(([k]) => k)
  console.log(`${id} ${bug ? `(${p.bug})` : '(correct)'}: after ${trace.length} steps the leaders are ${leaders.join(', ')}${leaders.length > 1 ? ': safety broken' : ''}`)
}
