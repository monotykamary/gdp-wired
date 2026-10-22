// What inferLaws (core/infer.ts) searches on one task, without searching: `bun compare/chc/prof/template.ts <task.smt2>`.
// Prints one JSON line: the predicates and their sorts, the atoms (the state's integers and yes/nos; loc, a choice, is
// a guard, never a term), the coefficient magnitudes the forms use (1, 2, 3 and the first four of the machine's own
// constants in 4..1000, its expressions' constants as infer.ts's constantsOf collects them, the clause and location
// indices among them), and which shapes of two and three terms that leaves (its magnitudes, ±1 alone, or none), by
// infer.ts's own limits (maxCandidates 60,000). The gap analysis (gap.py) reads it beside Spacer's invariants.
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build} from '../translate.ts'
import type {C, E, Law, Machine} from '../../../core/machine.ts'

// infer.ts's constantsOf, as it is there (not exported).
function constantsOf(m: Machine, laws: Law[]): number[] {
  const out = new Set<number>()
  const e = (t: E): void => {
    switch (t.op) {
      case 'const': out.add(t.value); break
      case 'var': break
      case 'mul': out.add(t.k); e(t.a); break
      case 'add': case 'sub': case 'min': case 'max': case 'prod': e(t.a); e(t.b); break
      case 'if': c(t.c); e(t.then); e(t.else); break
      case 'get': e(t.key); break
    }
  }
  const c = (t: C): void => {
    switch (t.op) {
      case '<': case '<=': case '=': e(t.a); e(t.b); break
      case 'and': case 'or': t.xs.forEach(c); break
      case 'not': c(t.x); break
      case 'flag': break
      case 'all': c(t.c); break
    }
  }
  Object.values(m.state).forEach(e)
  Object.values(m.step.state ?? {}).forEach(e)
  Object.values(m.step.flags ?? {}).forEach(c)
  for (const w of Object.values(m.step.maps ?? {})) { if ('key' in w) e(w.key); e(w.value) }
  if (m.assume) c(m.assume)
  if (m.pre) c(m.pre)
  laws.forEach(l => c(l.holds))
  return [...out].filter(k => Number.isSafeInteger(k) && Math.abs(k) <= 1e6)
}

const file = process.argv[2]!
const chc = parseChc(readFileSync(file, 'utf8'))
const b = build(chc), m = b.rule.machine
const consts = [...new Set(constantsOf(m, [b.law]).map(Math.abs))].filter(k => k > 0).sort((p, q) => p - q)
const mags = [...new Set([1, 2, 3, ...consts.filter(k => k > 3 && k <= 1000).slice(0, 4)])]
const P = b.nInt + b.nBool, maxCandidates = 60000
const choose = (k: number, of: number) => { let r = 1; for (let i = 0; i < k; i++) r = r * (of - i) / (i + 1); return r }
const two = choose(2, P) * 4 * mags.length ** 2 <= maxCandidates / 4 ? 'mags' : 'unit'
const three = choose(3, P) * 8 * mags.length ** 3 <= maxCandidates / 2 ? 'mags' : choose(3, P) * 8 <= maxCandidates / 2 ? 'unit' : 'none'
console.log(JSON.stringify({stage: 'answer', answer: 'template', preds: Object.fromEntries(chc.preds), clauses: chc.clauses.length, nInt: b.nInt, nBool: b.nBool, P, mags, two, three, consts: consts.slice(0, 40)}))
