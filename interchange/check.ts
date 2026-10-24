// The standalone checker (gdp-wired-check): a document in, accepted or refused for each claim out. Every verdict is the
// trusted kernel's (kernel/kernel.ts, kernel/cyclic.ts, core/check.ts, as they are): each kind's check is the kernel's
// own entry point where it has one (checkLaws, checkStepLaws, checkKInduction, checkRecur, refuseCyclic, checkQMachine,
// checkQTree, check), and where it has none, the kernel's goals with the tree named for each (as checkLaws reads them):
// loops (loopObligations), folds (foldObligations), progress (progressObligations), liveness (livenessParts, then
// checkStepLaws). Around them, untrusted: reading the document (format.ts) and the guard that it was read faithfully
// (written again, it must be the document read).
import {check, checkKInduction, checkLaws, checkQMachine, checkQTree, checkRecur, checkStepLaws, foldObligations, kInductionStart, kInductionSteps, livenessParts, loopObligations, obligations, progressObligations, qObligations, recurGoal, stepLawObligations} from '../kernel/kernel.ts'
import type {Goal, Tree} from '../kernel/kernel.ts'
import {descentGoal, mainGoal, premiseGoal, refuseCyclic} from '../kernel/cyclic.ts'
import type {Cyclic} from '../kernel/cyclic.ts'
import {type Certificate, type Document, type Json, FormatError, fromInterchange, resolved, sameJson, toInterchange} from './format.ts'

export type Claim = {name: string, accepted: boolean, why?: string}
// `accepted`: every claim is. `refused`, where the document isn't one: malformed (outside the format, or read unfaithfully).
export type Report = {kind?: string, accepted: boolean, claims: Claim[], malformed?: string}

const attempt = (f: () => boolean): {ok: boolean, why?: string} => { try { return {ok: f()} } catch (e) { return {ok: false, why: e instanceof Error ? e.message : String(e)} } }
const treeOk = (g: Goal, trees: Record<string, Tree>) => trees[g.name] !== undefined && check(g, trees[g.name]!)
// Each goal's own answer, for a refusal's why (never the verdict: that is the kernel's entry point's).
const failing = (goals: () => Goal[], trees: Record<string, Tree>): string | undefined => {
  try {
    const bad = goals().filter(g => !treeOk(g, trees)).map(g => (trees[g.name] ? `${g.name}: its tree doesn't refute it` : `${g.name}: no tree`))
    return bad.length ? bad.slice(0, 3).join('; ') + (bad.length > 3 ? `; and ${bad.length - 3} more` : '') : undefined
  } catch (e) { return e instanceof Error ? e.message : String(e) }
}
// (A certificate of no claims, an empty set of laws, is the kernel's answer on it all the same: a claim of its own.)
const all = (names: string[], r: {ok: boolean, why?: string}, why?: () => string | undefined): Claim[] =>
  (names.length ? names : ['(no claims)']).map(name => ({name, accepted: r.ok, ...(r.ok ? {} : {why: r.why ?? why?.() ?? 'refused'})}))

// The kernel's verdict on a certificate, for each thing it claims.
export function checkCertificate(c: Certificate): Claim[] {
  switch (c.kind) {
    case 'goals': return c.goals.map(g => { const r = attempt(() => check(g.goal, g.tree)); return {name: g.goal.name, accepted: r.ok, ...(r.ok ? {} : {why: r.why ?? 'the tree doesn\'t refute the goal'})} })
    case 'qgoals': return c.goals.map(g => { const r = attempt(() => checkQTree(g.goal, g.tree)); return {name: g.goal.name, accepted: r.ok, ...(r.ok ? {} : {why: r.why ?? 'the tree doesn\'t refute the goal'})} })
    // A set of laws is proven together (each step assumes them all), so each is accepted exactly when the set is.
    case 'laws': return all(c.laws.map(l => l.name), attempt(() => checkLaws(c.machine, c.laws, c.proof)), () => failing(() => obligations(c.machine, c.laws, c.proof.instances), c.proof.trees))
    case 'stepLaws': return all([...c.laws.map(l => l.name), ...c.stepLaws.map(s => s.name)], attempt(() => checkStepLaws(c.machine, c.laws, c.stepLaws, c.proof)),
      () => failing(() => [...obligations(c.machine, c.laws, c.proof.laws.instances), ...c.stepLaws.flatMap(s => stepLawObligations(c.machine, c.laws, c.proof.perStep?.[s.name] ?? c.proof.instances, s))], {...c.proof.laws.trees, ...c.proof.trees})
        ?? 'a later step\'s names read before it (the zone condition)')
    case 'kInduction': return all([c.kInduction.law.name], attempt(() => checkKInduction(c.machine, c.laws, c.kInduction, c.proof)),
      () => failing(() => [kInductionStart(c.machine, c.kInduction, c.proof.perStep?.[`${c.kInduction.law.name} @start`] ?? c.proof.instances), ...kInductionSteps(c.machine, c.kInduction).flatMap(s => stepLawObligations(c.machine, c.laws, c.proof.perStep?.[s.name] ?? c.proof.instances, s))], c.proof.trees)
        ?? failing(() => obligations(c.machine, c.laws, c.proof.laws.instances), c.proof.laws.trees))
    case 'liveness': {
      const r = attempt(() => { const {stay, cover, helps} = livenessParts(c.machine, c.liveness); return checkStepLaws(c.machine, c.laws, [stay, cover, ...helps], c.proof) })
      return all([c.liveness.name], r, () => failing(() => { const {stay, cover, helps} = livenessParts(c.machine, c.liveness); return [stay, cover, ...helps].flatMap(s => stepLawObligations(c.machine, c.laws, c.proof.perStep?.[s.name] ?? c.proof.instances, s)) }, c.proof.trees))
    }
    // Progress assumes the laws: proven here by their own trees where the document has them, else not accepted.
    case 'progress': {
      if (!c.lawsProof) return [{name: c.progress.name, accepted: false, why: 'the laws it assumes have no proof in this document (lawsProof)'}]
      const lp = c.lawsProof
      return all([c.progress.name], attempt(() => checkLaws(c.machine, c.laws, lp) && progressObligations(c.machine, c.laws, c.instances, c.progress).every(g => treeOk(g, c.trees))),
        () => failing(() => obligations(c.machine, c.laws, lp.instances), lp.trees) ?? failing(() => progressObligations(c.machine, c.laws, c.instances, c.progress), c.trees))
    }
    case 'loop': return all([`${c.loop.name} halts`, ...c.laws.map(l => l.name)], attempt(() => loopObligations(c.loop, c.laws, c.rank).every(g => treeOk(g, c.trees))), () => failing(() => loopObligations(c.loop, c.laws, c.rank), c.trees))
    case 'fold': return all(c.laws.map(l => l.name), attempt(() => foldObligations(c.fold, c.laws).every(g => treeOk(g, c.trees))), () => failing(() => foldObligations(c.fold, c.laws), c.trees))
    case 'recur': return all([`${c.loop.name} never ends`], attempt(() => checkRecur(c.loop, c.recur)), () => failing(() => [recurGoal(c.loop, c.recur)], {[recurGoal(c.loop, c.recur).name]: c.recur.tree}) ?? 'the start or the stem')
    case 'cyclic': { const why = attempt(() => refuseCyclic(c.cyclic) === undefined); return all(c.cyclic.nodes.map(n => n.name), why, () => refuseCyclic(c.cyclic)) }
    case 'qmachine': return all(c.laws.map(l => l.name), attempt(() => checkQMachine(c.machine, c.laws, c.trees)))
    // A ring's termination: each call's obligation by its cyclic proof (that these are the measure's obligations is
    // read from the ring's definitions, which the format doesn't carry: Lean checks that, Data.lean's termination_by).
    case 'termination': return c.obligations.map(o => { const r = attempt(() => refuseCyclic(o.cyclic) === undefined); return {name: `${o.function}: ${o.law}`, accepted: r.ok, ...(r.ok ? {} : {why: r.why ?? refuseCyclic(o.cyclic) ?? 'refused'})} })
  }
}

// A document's report: read, guarded, checked. Never throws.
export function checkDocument(doc: unknown): Report {
  let c: Certificate
  try {
    c = fromInterchange(doc)
    // The guard: the certificate read, written again, is the document (its columns in any order).
    if (!sameJson(resolved(toInterchange(c, (doc as Document).meta)), resolved(doc as Document))) return {accepted: false, claims: [], malformed: 'read back, the document is not the same (a field the format drops, or a value it changes)'}
  } catch (e) {
    return {accepted: false, claims: [], malformed: e instanceof FormatError ? e.message : `unreadable: ${e instanceof Error ? e.message : String(e)}`}
  }
  const claims = checkCertificate(c)
  return {kind: c.kind, accepted: claims.every(x => x.accepted), claims}
}

// Every goal the kernel builds for a certificate, with the tree the certificate names for it: the tree part of every
// check, as a `goals` (or `qgoals`) certificate a second checker reads (interchange/py/check.py checks trees alone).
// (The checks past trees stay the kernel's: a stem evaluated, a cyclic proof's ranks of one length, the step laws' zone.)
export function goalsOf(c: Certificate): Certificate {
  const pick = (goals: Goal[], trees: Record<string, Tree>) => goals.flatMap(goal => (trees[goal.name] ? [{goal, tree: trees[goal.name]!}] : []))
  const cyclic = (p: Cyclic) => p.nodes.flatMap(n => [{goal: mainGoal(p.facts, p.nodes, n), tree: n.main}, ...n.uses.flatMap(u => {
    const m = p.nodes[u.node]
    return m ? [...m.hyps.flatMap((h, i) => (u.premises[i] ? [{goal: premiseGoal(p.facts, n, u, h, i), tree: u.premises[i]!}] : [])), ...(m.rank.length === n.rank.length ? [{goal: descentGoal(p.facts, n, u, m), tree: u.descent}] : [])] : []
  })])
  const steps = (m: Certificate & {kind: 'stepLaws' | 'liveness' | 'kInduction'}, sls: Parameters<typeof stepLawObligations>[3][]) =>
    [...pick(obligations(m.machine, m.laws, m.proof.laws.instances), m.proof.laws.trees), ...pick(sls.flatMap(s => stepLawObligations(m.machine, m.laws, m.proof.perStep?.[s.name] ?? m.proof.instances, s)), m.proof.trees)]
  switch (c.kind) {
    case 'goals': case 'qgoals': return c
    case 'qmachine': return {kind: 'qgoals', goals: c.laws.flatMap(l => { const g = qObligations(c.machine, c.laws, l), t = c.trees[l.name]; return t ? [{goal: g.start, tree: t.start}, {goal: g.step, tree: t.step}] : [] })}
    case 'laws': return {kind: 'goals', goals: pick(obligations(c.machine, c.laws, c.proof.instances), c.proof.trees)}
    case 'stepLaws': return {kind: 'goals', goals: steps(c, c.stepLaws)}
    case 'liveness': { const {stay, cover, helps} = livenessParts(c.machine, c.liveness); return {kind: 'goals', goals: steps(c, [stay, cover, ...helps])} }
    case 'kInduction': {
      const start = kInductionStart(c.machine, c.kInduction, c.proof.perStep?.[`${c.kInduction.law.name} @start`] ?? c.proof.instances)
      return {kind: 'goals', goals: [...pick([start], c.proof.trees), ...steps(c, kInductionSteps(c.machine, c.kInduction))]}
    }
    case 'progress': return {kind: 'goals', goals: [...(c.lawsProof ? pick(obligations(c.machine, c.laws, c.lawsProof.instances), c.lawsProof.trees) : []), ...pick(progressObligations(c.machine, c.laws, c.instances, c.progress), c.trees)]}
    case 'loop': return {kind: 'goals', goals: pick(loopObligations(c.loop, c.laws, c.rank), c.trees)}
    case 'fold': return {kind: 'goals', goals: pick(foldObligations(c.fold, c.laws), c.trees)}
    case 'recur': return {kind: 'goals', goals: [{goal: recurGoal(c.loop, c.recur), tree: c.recur.tree}]}
    case 'cyclic': return {kind: 'goals', goals: cyclic(c.cyclic)}
    case 'termination': return {kind: 'goals', goals: c.obligations.flatMap(o => cyclic(o.cyclic))}
  }
}
export type {Json}
