// Plan only local binder changes. The actual transform and semantic bridge are
// checked by QAlpha.lean; callers never rewrite the captured machine or proof data.
import type {Law, Machine} from '../core/machine.ts'
import {boundOf} from '../kernel/kernel.ts'
export type BinderRename = {flag: string, old: string, fresh: string}
const strings = (x: unknown, out: Set<string>): void => {
  if (typeof x === 'string') out.add(x)
  else if (Array.isArray(x)) x.forEach(y => strings(y, out))
  else if (x && typeof x === 'object') for (const [key,value] of Object.entries(x)) { out.add(key); strings(value,out) }
}
export function quantifiedRenames(m: Machine, laws: readonly Law[], reserved: readonly string[] = []): BinderRename[] {
  const allLaws = [...laws,...(m.facts ?? [])]
  const logical = new Set(['#',...allLaws.flatMap(l => [l.forall,...(l.keys ?? [])].flatMap(k => k ? [k,`${k}#`] : []))])
  const taken = new Set([...reserved,...logical])
  strings([m,laws],taken)
  const flags = Object.entries(m.step.flags ?? {})
  const out: BinderRename[] = []
  let serial = 0
  for (const [flag,q] of flags) {
    if (q.op !== 'all') continue
    // A variable used only locally by this binder needs no change. Any same-name
    // use elsewhere (including another binder or a law's skolem) is kept intact.
    const elsewhere = new Set(logical)
    strings([{...m,step:{...m.step,flags:Object.fromEntries(flags.filter(([f]) => f !== flag))}},laws],elsewhere)
    for (const old of new Set(boundOf(q))) {
      if (!elsewhere.has(old)) continue
      let fresh: string
      do { fresh = `qalpha$${serial++}` } while (taken.has(fresh))
      taken.add(fresh)
      out.push({flag,old,fresh})
    }
  }
  return out
}
