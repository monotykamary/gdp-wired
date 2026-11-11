// Untrusted operation-local containment. This chooses original hypotheses,
// never facts: every successful tree must be transported to the complete goal.
import {type C, type E, type Law, type Machine, n, walkOnce} from './machine.ts'
import {type Goal, substC, substE, truth} from '../kernel/kernel.ts'
import {finiteCountChoice} from './count-cases.ts'
// Same finite-operation recognizer as B's count-frames module, without its
// unrelated strategy and frame-certificate dependencies.
function fixedCountFrameCase(m: Machine): {name: string, value: number} | undefined {
  const choice = finiteCountChoice(m)
  if (!choice) return
  const [name, values] = choice, fixed = new Set<number>()
  const visit = (c: C): void => {
    if (c.op === 'and') { c.xs.forEach(visit); return }
    if (c.op !== '=') return
    const [a, b] = c.a.op === 'var' ? [c.a, c.b] : [c.b, c.a]
    if (a.op === 'var' && a.name === name && b.op === 'const') fixed.add(b.value)
  }
  if (m.assume) visit(m.assume)
  if (fixed.size !== 1) return
  const value = [...fixed][0]!
  return Number.isSafeInteger(value) && value >= 0 && values.has(value) ? {name, value} : undefined
}

import {late} from '../kernel/prove.ts'
export type PremiseView = {goal: Goal, selected: number[], omitted: number[], allowed: string[], guardReads: boolean}
const base = (name: string) => name.replace(/#$/, '')
export function countPremiseMaps(m: Machine, law: Law, until: number, guardReads = true, fixedOnly = true): Set<string> | undefined {
  const choice = fixedCountFrameCase(m)
  if ((!choice && fixedOnly) || late(until)) return
  // An unspecialized family keeps both branches; it assumes no operation value.
  const vars = choice ? {[choice.name]: n(choice.value)} : {}, flags: Record<string, C> = {}, resolving = new Set<string>()
  const flag = (name: string): C | undefined => {
    if (flags[name]) return flags[name]
    const source = m.step.flags?.[name]
    if (!source || resolving.has(name) || late(until)) return
    resolving.add(name)
    let missing = false
    walkOnce(source, node => {const c = node as C; if (c.op === 'flag' && !flag(c.name)) missing = true})
    resolving.delete(name)
    if (missing) return
    return flags[name] = substC(source, {vars, flags, maps: {}})
  }
  for (const name of Object.keys(m.step.flags ?? {})) if (!flag(name)) return
  const allowed = new Set<string>(), targets = new Set<string>()
  const binarySource = (name: string): boolean => {
    const initial = m.maps?.[name], write = m.step.maps?.[name]
    const value = (e: E): boolean => e.op === 'const' ? e.value === 0 || e.value === 1 : e.op === 'if' ? value(e.then) && value(e.else) : e.op === 'get' && e.map === name
    return (initial === 0 || initial === 1) && !!write && value(write.value)
  }
  const collect = (value: C | E): void => {
    if (late(until)) return
    if (value.op === 'get') {allowed.add('map:' + base(value.map)); collect(value.key); return}
    if (value.op === 'var') {if (Object.hasOwn(m.state, value.name)) allowed.add('state:' + value.name); return}
    if (value.op === 'if') {
      const known = truth(value.c, new Map())
      if (known !== undefined) {collect(known ? value.then : value.else); return}
      if (guardReads) collect(value.c)
      collect(value.then); collect(value.else); return
    }
    if (value.op === 'and' || value.op === 'or') {
      if (truth(value, new Map()) !== undefined) return
      value.xs.forEach(collect); return
    }
    if (value.op === 'not') {if (truth(value, new Map()) === undefined) collect(value.x); return}
    if (value.op === 'all') {collect(value.c); return}
    if ('a' in value) collect(value.a)
    if ('b' in value) collect(value.b)
  }
  walkOnce(law.holds, node => {const e = node as E; if (e.op === 'get') targets.add(base(e.map))})
  collect(law.holds)
  // Stored binary source data, read-only data and phase scalars used by a
  // target update can describe inherited rows in another operation. This is
  // only a vocabulary hint, not a range fact; request maps stay outside it.
  for (const name of targets) {
    const write = m.step.maps?.[name]
    if (!write) continue
    walkOnce(substE(write.value, {vars: {}, flags, maps: {}}), node => {
      const value = node as E
      if (value.op === 'var' && Object.hasOwn(m.state, value.name)) allowed.add('state:' + value.name)
    })
    // Named control guards stay opaque here. Expanding them would confuse a
    // Boolean control cell with a Boolean value copied into the target map.
    walkOnce(write.value, node => {
      const value = node as E
      if (value.op === 'get' && !m.inputMaps?.includes(value.map) && (binarySource(value.map) || !Object.hasOwn(m.step.maps ?? {}, value.map) && !Object.hasOwn(m.counts ?? {}, value.map))) allowed.add('map:' + base(value.map))
    })
  }
  // Only writes into the target's maps participate. Following writes into each
  // newly read support map would recreate an unrestricted transitive closure.
  for (const name of targets) {
    const write = m.step.maps?.[name]
    if (write) collect(substE(write.value, {vars, flags, maps: {}}))
  }
  // A derived count is in the vocabulary only when all of its underlying
  // reads are already in it; this is containment, never a shared-map union.
  let changed = true
  while (changed && !late(until)) {
    changed = false
    for (const [name, count] of Object.entries(m.counts ?? {})) {
      if (allowed.has('map:' + name)) continue
      let contained = true
      walkOnce(count, node => {
        const value = node as E
        if (value.op === 'get' && !allowed.has('map:' + base(value.map))) contained = false
        if (value.op === 'var' && Object.hasOwn(m.state, value.name) && !allowed.has('state:' + value.name)) contained = false
      })
      if (contained) {allowed.add('map:' + name); changed = true}
    }
  }
  return late(until) ? undefined : allowed
}
export function countPremiseView(goal: Goal, m: Machine, law: Law, conclusion: C, globals: readonly C[], until: number, guardReads = true): PremiseView | undefined {
  if (late(until) || goal.hyps.length > 1024) return
  const allowed = countPremiseMaps(m, law, until, guardReads)
  if (!allowed) return
  const root = JSON.stringify(conclusion), fixed = new Set(globals.map(h => JSON.stringify(h)))
  if (!goal.hyps.some(h => JSON.stringify(h) === root)) return
  const selected: number[] = [], omitted: number[] = []
  for (const [index, hypothesis] of goal.hyps.entries()) {
    if (late(until)) return
    let contained = true
    walkOnce(hypothesis, node => {
      const value = node as C | E
      if (value.op === 'get' && !allowed.has('map:' + base(value.map))) contained = false
      if (value.op === 'var' && Object.hasOwn(m.state, value.name) && !allowed.has('state:' + value.name)) contained = false
    })
    const key = JSON.stringify(hypothesis)
    if (contained || key === root || fixed.has(key)) selected.push(index)
    else omitted.push(index)
  }
  if (!omitted.length) return
  return {goal: {name: goal.name, hyps: selected.map(i => goal.hyps[i]!)}, selected, omitted, allowed: [...allowed].sort(), guardReads}
}

export type CountPremiseContext = {laws: Law[], selected: number[], omitted: number[], allowed: string[], guardReads: boolean}
// Family-level search uses exactly the same all-reads containment test as the
// operation-local view. Without a fixed operation no substitution is made:
// both branches contribute vocabulary, never a guessed transition or fact.
export function countPremiseContext(m: Machine, family: Law[], owner: Law, until: number, guardReads = true): CountPremiseContext | undefined {
  if (!family.includes(owner) || family.length > 1024 || late(until)) return
  const allowed = countPremiseMaps(m, owner, until, guardReads, false)
  if (!allowed) return
  const selected: number[] = [], omitted: number[] = []
  for (const [index, law] of family.entries()) {
    if (late(until)) return
    let contained = true
    walkOnce(law.holds, node => {
      const value = node as C | E
      if (value.op === 'get' && !allowed.has('map:' + base(value.map))) contained = false
      if (value.op === 'var' && Object.hasOwn(m.state, value.name) && !allowed.has('state:' + value.name)) contained = false
    })
    if (law === owner || contained) selected.push(index)
    else omitted.push(index)
  }
  return omitted.length ? {laws: selected.map(i => family[i]!), selected, omitted, allowed: [...allowed].sort(), guardReads} : undefined
}
