// Candidate invariants for simple helpful steps. Everything in this file is search guidance: even a syntactically
// matched write may take a different branch or alias a watched key. Only proveLiveness may accept the proposals.
import {type C, type E, type Law, type Machine, walk} from './machine.ts'
import {type Liveness, livenessHelpful, substE, trueC} from '../kernel/kernel.ts'
import {clock, proveLiveness, proveProgress, withDeadline} from '../kernel/prove.ts'
import {type LeadsVerdict, showC} from './cycles.ts'

const id = (x: unknown) => JSON.stringify(x)
const same = (a: E, b: E) => id(a) === id(b)
const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const at = (map: string, key: E): E => ({op: 'get', map, key})
const eq = (a: E, b: E): C => ({op: '=', a, b}), le = (a: E, b: E): C => ({op: '<=', a, b})
const implies = (x: C, y: C): C => ({op: 'or', xs: [{op: 'not', x}, y]})
const and = (x: C, y: C): C => ({op: 'and', xs: [x, y]})
const conjuncts = (x: C): C[] => x.op === 'and' ? x.xs.flatMap(conjuncts) : [x]
const addends = (x: E): E[] => x.op === 'add' ? [...addends(x.a), ...addends(x.b)] : [x]
const outcomes = (x: E): E[] => x.op === 'if' ? [...outcomes(x.then), ...outcomes(x.else)] : [x]
const mentions = (t: unknown, f: (o: Record<string, unknown>) => boolean): boolean => {
  let hit = false
  walk(t, o => { if (f(o)) hit = true })
  return hit
}
const reads = (t: unknown, names: string[]) => mentions(t, o => o.op === 'var' && names.includes(o.name as string))

export function helpfulWriteSupports(m: Machine, l: Liveness): Law[] {
  if (m.history || m.sums && Object.keys(m.sums).length || m.inputMaps?.length || livenessHelpful(l).length !== 1) return []
  const request = livenessHelpful(l)[0]!.request, stored = Object.entries(m.step.maps ?? {})
  if (!stored.length || stored.length > 32) return []
  const updates = Object.entries(m.step.state ?? {}), found = new Map<string, Law>()
  const add = (holds: C) => {
    const key = id(holds)
    if (found.size >= 8 || found.has(key)) return
    found.set(key, {name: `liveness write support ${found.size + 1}: ${showC(holds)}`, holds})
  }

  // A helpful request names a key past a max/frontier. Where a scalar is either retained or written from that
  // same request key, compare its value with the written expression at the frontier. Ordinary freshness laws about
  // cells beyond the frontier are separately supplied by freshLaws. No clock assumption is added to the machine.
  for (const [mark, next] of updates) if (next.op === 'max') {
    const key = same(next.a, v(mark)) ? next.b : same(next.b, v(mark)) ? next.a : undefined
    if (key?.op !== 'var' || !request[key.name] || !reads(request[key.name], [mark]) ||
        !stored.some(([, w]) => 'key' in w && same(w.key, key))) continue
    for (const [x, e] of updates) if (e.op === 'if' && same(e.else, v(x)) && reads(e.then, [key.name])) {
      if (mentions(e.then, o => o.op === 'flag' || o.op === 'get') || reads(e.then, m.inputs.filter(y => y !== key.name))) continue
      add(le(v(x), substE(e.then, {vars: {[key.name]: v(mark)}, maps: {}, flags: {}})))
    }
  }

  // A fixed observer is pending when its row's tag equals a constant. Follow its write selector to sibling payloads
  // at the same write key and simple bounds on those payloads. Each projection is only a proposed reachable law.
  for (const trigger of conjuncts(l.from)) if (trigger.op === '=') {
    const tag = trigger.a.op === 'get' && trigger.b.op === 'const' ? trigger.a :
      trigger.b.op === 'get' && trigger.a.op === 'const' ? trigger.b : undefined
    if (!tag || reads(tag.key, [...m.inputs, ...Object.keys(m.state)]) || mentions(tag.key, o => o.op === 'get')) continue
    const write = m.step.maps?.[tag.map]
    if (!write || !('key' in write) || write.value.op !== 'if' || !same(write.value.else, at(tag.map, write.key))) continue
    const guard = write.value.c, bounds = new Map<string, {a: E, b: E}>(), expanded = new Set<string>()
    const scan = (x: C) => walk(x, o => {
      if (o.op === 'flag' && typeof o.name === 'string' && !expanded.has(o.name)) {
        expanded.add(o.name); const f = m.step.flags?.[o.name]; if (f) scan(f)
      }
      if (o.op === '<=' && (o.b as E | undefined)?.op === 'var' && (o.a as E | undefined)?.op === 'add' && !reads(o.b, m.inputs)) {
        bounds.set(id(o), {a: o.a as E, b: o.b as E})
      }
    })
    scan(guard)
    for (const [field, w] of stored) {
      if (field === tag.map || !('key' in w) || !same(w.key, write.key) || w.value.op !== 'if') continue
      const cells = at(field, tag.key), init = m.maps?.[field], old = at(field, w.key)
      if (!same(w.value.else, old) || id(w.value.c) !== id(guard)) {
        // A Boolean payload can be encoded after the row update as `if (updated predicate) then 1 else 0`.
        // Recognize a sibling only if that predicate reads its own old bit and the row's update selector.
        const c = w.value.c
        if ((init === 0 || init === 1) && same(w.value.then, k(1)) && same(w.value.else, k(0)) &&
            mentions(c, o => o.op === 'get' && same(o as E, old)) && mentions(c, o => id(o) === id(guard))) {
          add(implies(trigger, eq(cells, k(init))))
        }
        continue
      }
      const val = w.value.then, leaves = outcomes(val)
      // A co-written small choice or bit; the pending state may preserve its initial value.
      if (init !== undefined && leaves.every(x => x.op === 'const' && x.value <= 4) &&
          leaves.some(x => same(x, k(init)))) add(implies(trigger, eq(cells, k(init))))
      for (const {a, b} of bounds.values()) if (addends(a).some(x => same(val, x))) {
        add(implies(trigger, le(cells, b)))
        // A simultaneously accumulated value using the same amount may be capped by the same guard bound.
        for (const [x, e] of updates) if (!same(v(x), b) && mentions(e, o => o.op === 'add' && addends(o as E).some(t => same(t, val)))) add(le(v(x), b))
        // With a parameter-or-request payload, zero in the watched cell may identify the zero parameter case.
        if (leaves.some(x => x.op === 'var' && m.inputs.includes(x.name))) {
          for (const x of leaves) if (x.op === 'var' && m.params.includes(x.name)) add(implies(and(trigger, eq(cells, k(0))), eq(x, k(0))))
        }
      }
    }
  }
  return [...found.values()]
}

// Proof proposal only. The ordinary prover checks initiation, simultaneous preservation, stay, coverage,
// all helpful branches and the original fairness obligations. A wrong projection costs at most this stage's grant.
export function leadsByWriteSupports(m: Machine, laws: Law[], l: Liveness, ms: number): LeadsVerdict | undefined {
  if (ms < 500 || l.fairness === 'strong') return undefined
  const until = clock() + ms, rank = [k(0)], candidates = helpfulWriteSupports(m, l)
  if (!candidates.length) return undefined
  let alive = candidates.filter(c => !laws.some(law => law.name === c.name))
  while (alive.length && clock() < until) {
    const all = [...laws, ...alive]
    const out = withDeadline(until, () => proveLiveness(m, all, {...l, rank}))
    if (out.proven && out.checked) {
      // The legacy step proof with unnamed weak-help fields need not show enabledness. For this new route, require
      // one checked completion in each pending state: fill the spare fields with constants (a proof witness, not a
      // new assumption about the scheduler or what values all executions must send).
      const h = livenessHelpful(l)[0]!
      if (m.assume && m.inputs.some(i => !(i in h.request))) {
        const request = Object.fromEntries(m.inputs.map(i => [i, h.request[i] ?? k(0)]))
        const a = withDeadline(until, () => proveProgress(m, all, {name: `${l.name}: helpful completion is allowed`,
          when: and(and(l.from, {op: 'not', x: l.to}), h.when), then: trueC, request}))
        if (!a.proven || !a.checked) return undefined
      }
      return {proven: true, checked: true, rank, laws: alive, found: {rank: '(0)', laws: alive.map(c => showC(c.holds))}}
    }
    const drop = alive.findIndex(c => out.failed?.goal.startsWith(`${c.name} @`))
    if (drop < 0) return undefined
    alive = alive.filter((_, i) => i !== drop)
  }
  return undefined
}
