// Laws about ids handed out by a counter: a state variable that only goes up (the next id), and maps written at the
// ids it has handed out. Code that numbers its sessions, tokens, grants or rows so (the n-th created gets id n) keeps
//   ∀k. c <= k → M[k] is M's initial value          (no row exists yet at an id not handed out)
//   ∀k. G[k] is G's initial value ∨ M[k] < c        (a row that exists holds an id handed out, of a counter c)
// and laws about one id often need them: a deleted session never comes back, a rotated token's old value is rejected.
// The candidates are each counter (never lower after a step of the runs, and some map's cell at its value written as it
// goes on: an id handed out) with each map, and each map with each map of the
// same record (`Tok.st`, `Tok.grant`) or itself; those the runs' states keep, then those proven inductive together
// (Houdini: a candidate whose goal fails is dropped, the rest proven again). Nothing new is trusted: what is kept is
// laws the kernel proves.
import {type C, type E, type Law, type Machine, type State, evalC, interpret, seeded} from './machine.ts'
import {clock, proveLaws} from '../kernel/prove.ts'
import {allowed, watch} from './watch.ts'
import type {Draws} from './live.ts'

const v = (name: string): E => ({op: 'var', name}), get = (map: string, key: E): E => ({op: 'get', map, key})
export type FreshLaw = {law: Law, text: string}
export function freshLaws(m: Machine, kinds: Law[], draws: Draws, opts: {ms?: number} = {}): FreshLaw[] {
  const maps = Object.entries(m.maps ?? {}).filter(([n]) => !(m.inputMaps ?? []).includes(n))
  if (!maps.length || m.history) return []
  const until = clock() + (opts.ms ?? 5000), run = interpret(m), rand = seeded(53), bound = 4
  // the runs: their states, and the variables some step lowers
  const states: {ps: Record<string, number>, st: State}[] = [], lowered = new Set<string>(), handed = new Set<string>()
  for (let trial = 0; trial < 60 && clock() < until; trial++) {
    let ps: Record<string, number>, st: State
    try { ps = draws.params(rand, bound); if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) continue; st = run.init(ps) } catch { continue }
    for (let d = 0, tries = 0; d < 20 && tries < 60; tries++) {
      try {
        const input = draws.input(rand, bound, ps)
        if (!allowed(m, run, ps, st, input)) continue
        const next = run.step(ps, st, input)
        for (const x of Object.keys(m.state)) {
          const was = st.scalars[x]!, now = next.scalars[x]!
          if (now < was) lowered.add(x)
          // an id handed out: the counter goes on, and some map's cell at its old value is written
          else if (now > was && maps.some(([n, init]) => (st.maps[n]?.get(was) ?? init) !== (next.maps[n]?.get(was) ?? init))) handed.add(x)
        }
        st = next; d++
        states.push({ps, st})
      } catch { /* refused: another */ }
    }
  }
  const counters = [...handed].filter(c => !lowered.has(c))
  if (!counters.length) return []
  const key = 'k$fresh', record = (n: string) => n.slice(0, Math.max(0, n.indexOf('.')))
  const cands: FreshLaw[] = []
  for (const c of counters) for (const [map, init] of maps) {
    const at = get(map, v(key)), initial: C = {op: '=', a: at, b: {op: 'const', value: init}}
    cands.push({law: {name: `ids from ${c}: ${map} unset past them`, holds: {op: 'or', xs: [{op: '<', a: v(key), b: v(c)}, initial]}, forall: key}, text: `∀k. ${c} <= k → ${map}[k] = ${init}`})
    for (const [g, gi] of maps) {
      if (g !== map && (!record(g) || record(g) !== record(map))) continue
      cands.push({law: {name: `ids from ${c}: ${map} below them where ${g} is set`, holds: {op: 'or', xs: [{op: '=', a: get(g, v(key)), b: {op: 'const', value: gi}}, {op: '<', a: at, b: v(c)}]}, forall: key}, text: `∀k. ${g}[k] ≠ ${gi} → ${map}[k] < ${c}`})
    }
  }
  let alive = cands.filter(f => states.every(({ps, st}) => { try { return watch(m, run, f.law, ps, bound).start(st) } catch { return false } }))
  while (alive.length && clock() < until) {
    let out: ReturnType<typeof proveLaws>
    try { out = proveLaws(m, [...kinds, ...alive.map(f => f.law)]) } catch { return [] }
    if (out.proven && out.checked) return alive
    const failed = out.failed?.goal ?? '', drop = alive.findIndex(f => failed.startsWith(`${f.law.name} @`) || failed.startsWith(`${f.law.name}:`))
    if (drop < 0) return []
    alive = alive.filter((_, i) => i !== drop)
  }
  return []
}
