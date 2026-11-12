import {searchNow as countedSearchNow} from '../wall.ts'
import {BudgetExpired} from '../work-admission.ts'
import type {ReplayDiagnosticContext} from '../count-replay-diagnostic.ts'
export type NativeCutContext=Readonly<{counts:Count[],frames?:FrameCut[],monos?:MonoCut[],lins?:LinCut[]}>
export type TransportPart='main'|'independent-lemma'
export type ConditionalTransportDecline=Readonly<{
 stage:'cut-validation'|'leaf-mapping'|'lemma-retarget'|'transport'|'transport-check'|'collection'|'collection-check'|'exception'
 part:TransportPart,reason:string,inputIndex?:number,sourceRowCount?:number,targetRowCount?:number,
 sourceRow?:unknown,sourceFact?:unknown,sourcePath?:Path,targetPath?:Path
}>
export type ConditionalTransportOptions = Readonly<{
 rethrowBudgetExpired?:boolean,
 diagnostic?:ReplayDiagnosticContext,
 native?:Readonly<{from:NativeCutContext,to:NativeCutContext}>,
 onDecline?:(detail:ConditionalTransportDecline)=>void,
}>
// Untrusted metadata and exact transport for conditional count proofs. The kernel
// never reads this WeakMap: only ordinary trees and independent LemmaCuts escape.
import {type Goal, type LemmaCut, type Path, type Tree, type Count, type FrameCut, type MonoCut, type LinCut, canon, canonFlip, check, checkGoalLemmas, facts, leafConstraintsReusing as rowsAt, lemmaPath, framePath, frameOk, monoOk, linOk} from '../../kernel/kernel.ts'
import {type Lin, type Step, add, k, scale} from '../solver.ts'
import {independentHit, rememberIndependent, retargetHit, rememberRetarget, slicedCheck, targetIndex} from './conditional-check-cache.ts'
export {conditionalProofStats} from './conditional-check-cache.ts'

type Context = {goal: Goal, lemmas: LemmaCut[]}
type Reporter=(detail:ConditionalTransportDecline)=>undefined
const noReport:Reporter=()=>undefined
// Failure metadata is observational and must not replace the original refusal.
const reporter=(options?:ConditionalTransportOptions):Reporter=>detail=>{try{options?.onDecline?.(detail)}catch{/* observational callback only */}return undefined}
const mainPath=(native:NativeCutContext|undefined,lemmas:LemmaCut[],path:Path):Path=>native?framePath(native.frames??[],lemmas,path,native.monos??[],native.lins??[]):lemmaPath(lemmas,path)
// Validate actual count definitions before using their cut atoms. Independent
// lemma trees deliberately never receive this main-tree context.
function validNative(native:NativeCutContext|undefined):boolean{
 if(!native)return true
 if(!Array.isArray(native.counts))return false
 return (native.frames??[]).every(cut=>frameOk(native.counts,cut))
  &&(native.monos??[]).every(cut=>monoOk(native.counts,cut))
  &&(native.lins??[]).every(cut=>linOk(native.counts,cut))
}
const marked = new WeakMap<Tree, Context>()
const alive = (until: number): boolean => countedSearchNow() < until
const flip = (lin: Lin): Lin => add(k(1), scale(lin, -1))
const put = (path: Path, lin: Lin, holds: boolean): Path => new Map(path).set(canon(lin), {lin, holds})
const sameGoal = (a: Goal, b: Goal): boolean => a === b || JSON.stringify(a.hyps) === JSON.stringify(b.hyps)

/** A proposer hint, not an admission check. Rows in tree use lemmaPath at each
 * leaf; branches still use the ordinary split path, exactly as in the kernel. */
export function markConditionalProof(goal: Goal, tree: Tree, lemmas: LemmaCut[]): Tree {
  marked.set(tree, {goal, lemmas})
  return tree
}

export function hasConditionalProof(tree: Tree): boolean {
  const seen = new WeakSet<Tree>()
  const visit = (t: Tree): boolean => {
    if (marked.has(t)) return true
    if (seen.has(t)) return false
    seen.add(t)
    return 'split' in t && (visit(t.yes) || visit(t.no))
  }
  return visit(tree)
}

// Match prependAtoms, including duplicate rows and first-occurrence lookups.
// Negcut must precede guards even when a guard has the very same canonical key.
const proofPath = (when: Lin[], cut: Lin): Path => {
  const path: Path = new Map()
  let duplicate = 0
  for (const atom of [{lin: cut, holds: false}, ...when.map(lin => ({lin, holds: true}))]) {
    const id = canon(atom.lin)
    path.set(path.has(id) ? `@${duplicate++}` : id, atom)
  }
  return path
}
const validLin = (lin: Lin): boolean => !!lin && typeof lin === 'object' && !Array.isArray(lin)
  && (Object.getPrototypeOf(lin) === Object.prototype || Object.getPrototypeOf(lin) === null)
  && Object.values(lin).every(Number.isSafeInteger)
const localGoal = (goal: Goal, lemma: LemmaCut): Goal | undefined => {
  if (lemma.slice === undefined) return goal
  if (!Array.isArray(lemma.slice) || !Array.from(lemma.slice).every(i => Number.isSafeInteger(i) && i >= 0 && i < goal.hyps.length)) return undefined
  return {...goal, hyps: lemma.slice.map(i => goal.hyps[i]!)}
}
function independent(goal: Goal, lemmas: LemmaCut[], until: number): boolean {
  if (!alive(until) || !Array.isArray(lemmas)) return false
  for (const lemma of Array.from(lemmas)) {
    if (!alive(until) || !lemma || !Array.isArray(lemma.when) || !Array.from(lemma.when).every(validLin) || !validLin(lemma.cut)) return false
    if (independentHit(goal, lemma)) continue
    const local = localGoal(goal, lemma)
    if (!local || !check(local, lemma.tree, proofPath(lemma.when, lemma.cut))) return false
    rememberIndependent(goal, lemma)
  }
  return alive(until)
}
const legalSplit = (tree: Extract<Tree, {split: Lin}>, path: Path): boolean =>
  !path.has(canon(tree.split)) && !Object.keys(tree.split).every(key => key === '1')

function checked(goal: Goal, tree: Tree, path: Path, until: number, native?:NativeCutContext): boolean {
  const visit = (t: Tree, p: Path, context: Context): boolean => {
    if (!alive(until)) return false
    const own = marked.get(t)
    if (own) {
      if (!sameGoal(goal, own.goal) || !independent(own.goal, own.lemmas, until)) return false
      context = own
    }
    if ('leaf' in t) return slicedCheck(goal, t, mainPath(native, context.lemmas, p)) && alive(until)
    return legalSplit(t, p) && visit(t.yes, put(p, t.split, true), context)
      && visit(t.no, put(p, t.split, false), context)
  }
  return visit(tree, path, {goal, lemmas: []}) && alive(until)
}

/** Check each marked region with its independent cuts, and unmarked regions
 * with the ordinary kernel rules. A nested mark replaces its parent's list. */
export function checkConditionalProof(goal: Goal, tree: Tree, path: Path = new Map()): boolean {
  try { return checked(goal, tree, path, Infinity) } catch { return false }
}

const decide = (lin: Lin, path: Path): boolean | undefined => {
  if (!Object.values(lin).every(Number.isSafeInteger)) return undefined
  if (Object.keys(lin).every(name => name === '1')) return (lin['1'] ?? 0) <= 0
  const direct = path.get(canon(lin))?.holds
  if (direct !== undefined) return direct
  const opposite = path.get(canonFlip(lin))?.holds
  return opposite === undefined ? undefined : !opposite
}

// No solver fallback. Only exact base rows and identical square/product offsets
// move; a target constant-positive row is already a complete refutation.
function leaf(from: Goal, to: Goal, tree: Extract<Tree, {leaf: Step[]}>, before: Path, after: Path, until: number, report:Reporter=noReport, part:TransportPart='main'): Tree | undefined {
  if (!alive(until)) return undefined
  const old = rowsAt(from, before), rows = rowsAt(to, after), at = new Map<string, number>()
  for (const [i, row] of rows.entries()) {
    if (!alive(until)) return undefined
    if (Number.isSafeInteger(row.lin['1']) && (row.lin['1'] ?? 0) > 0
      && Object.entries(row.lin).every(([name, value]) => name === '1' || value === 0)) return {leaf: [{kind: 'input', index: i}]}
    const id = canon(row.lin)
    if (!at.has(id)) at.set(id, i)
  }
  const index = (i: number): number | undefined => {
    if (!Number.isSafeInteger(i) || i < 0) return undefined
    return i >= old.length ? i - old.length + rows.length : at.get(canon(old[i]!.lin))
  }
  const missing=(inputIndex:number,reason:string):undefined=>{
    const sourceRow=old[inputIndex],src=sourceRow?.src
    return report({stage:'leaf-mapping',part,reason,inputIndex,sourceRowCount:old.length,targetRowCount:rows.length,sourceRow,sourceFact:src&&'fact'in src?from.hyps[src.fact]:undefined,sourcePath:before,targetPath:after})
  }
  const steps: Step[] = [], products: [number, number][] = []
  for (const step of tree.leaf) {
    if (!alive(until)) return undefined
    if (step.kind !== 'input') steps.push(step)
    else {
      const i = index(step.index)
      if (i === undefined) return missing(step.index,'missing-input-row')
      steps.push({...step, index: i})
    }
  }
  for (const [a, b] of tree.products ?? []) {
    if (!alive(until)) return undefined
    const i = index(a), j = index(b)
    if (i === undefined || j === undefined) return missing(i===undefined?a:b,'missing-product-row')
    products.push([i, j])
  }
  return alive(until) ? {leaf: steps, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: tree.squares} : {})} : undefined
}

function ordinary(from: Goal, to: Goal, tree: Tree, before: Path, after: Path, until: number, report:Reporter=noReport): Tree | undefined {
  if (!alive(until)) return undefined
  if ('leaf' in tree) return leaf(from, to, tree, before, after, until,report,'independent-lemma')
  const known = decide(tree.split, after)
  if (known !== undefined) return ordinary(from, to, known ? tree.yes : tree.no, put(before, tree.split, known), after, until,report)
  const yes = ordinary(from, to, tree.yes, put(before, tree.split, true), put(after, tree.split, true), until,report)
  const no = yes && ordinary(from, to, tree.no, put(before, tree.split, false), put(after, tree.split, false), until,report)
  return yes && no ? {split: tree.split, yes, no} : undefined
}

// Preserve mapped source hypotheses, including their order and duplicates. A
// removed hypothesis is dispensable only if exact independent-proof transport
// succeeds without it (e.g. an inserted guard is now an explicit entry atom).
// Even an unsliced source proof gets an explicit slice in an enlarged target.
function retarget(from: Goal, to: Goal, lemmas: LemmaCut[], scope: Path, until: number, onlyMissing = false, report:Reporter=noReport): LemmaCut[] | undefined {
  if (!independent(from, lemmas, until)) return report({stage:'lemma-retarget',part:'independent-lemma',reason:'source-independent-check'})
  const out: LemmaCut[] = [], target = targetIndex(to, until)
  if (!target) return undefined
  for (const lemma of lemmas) {
    if (!alive(until)) return undefined
    const source = localGoal(from, lemma)!, slice: number[] = [], texts: string[] = []
    const missing: Goal['hyps'] = []
    for (const hyp of source.hyps) {
      if (!alive(until)) return undefined
      const text = JSON.stringify(hyp), i = target.get(text)
      texts.push(text)
      if (i === undefined) missing.push(hyp)
      else slice.push(i)
    }
    // A fully mapped transport does not consume the entry scope. Include the
    // matched content as well as the slice, so different goals cannot alias.
    // Missing hypotheses and root collection remain exactly scope-sensitive.
    const key = onlyMissing && !missing.length ? JSON.stringify([slice, texts]) : undefined
    const cached = key === undefined ? undefined : retargetHit(lemma, key)
    if (cached) { out.push(cached); continue }
    const when = [...lemma.when]
    for (const atom of !onlyMissing || missing.length ? scope.values() : []) {
      if (!alive(until)) return undefined
      when.push(atom.holds ? atom.lin : flip(atom.lin))
    }
    const path = proofPath(when, lemma.cut)
    if (missing.length) {
      const supplied = new Set([...scope.values()].map(atom => canon(atom.holds ? atom.lin : flip(atom.lin))))
      for (const hyp of missing) {
        if (!alive(until)) return undefined
        const rows = facts(hyp, path)
        // Only explicit scope atoms may replace removed hypotheses. A missing
        // unrelated hypothesis is not silently discarded, even if unused.
        if (!rows.length || !rows.every(row => supplied.has(canon(row)))) return report({stage:'lemma-retarget',part:'independent-lemma',reason:'missing-hypothesis',sourceFact:hyp,sourcePath:scope})
      }
    }
    const local = {...to, hyps: slice.map(i => to.hyps[i]!)}
    const tree = ordinary(source, local, lemma.tree, proofPath(lemma.when, lemma.cut), path, until,report)
    if (!tree || !alive(until) || !check(local, tree, proofPath(when, lemma.cut)) || !alive(until)) return report({stage:'lemma-retarget',part:'independent-lemma',reason:'target-independent-check'})
    const moved = {when, cut: lemma.cut, tree, slice}
    if (key !== undefined) rememberRetarget(lemma, key, moved)
    out.push(moved)
  }
  return alive(until) ? out : undefined
}

/** Retarget an annotated or mixed proof, without turning cuts into split trees.
 * before/after are ordinary entry paths, not paths already augmented by cuts. */
export function transportConditionalProof(from: Goal, to: Goal, tree: Tree, before: Path, after: Path, until: number, options?: ConditionalTransportOptions): Tree | undefined {
  const report=reporter(options)
  try {
    if(!validNative(options?.native?.from)||!validNative(options?.native?.to))return report({stage:'cut-validation',part:'main',reason:'invalid-native-cuts-or-counts'})
    const visit = (t: Tree, a: Path, b: Path, source: Context, target: Context): Tree | undefined => {
      if (!alive(until)) return undefined
      const own = marked.get(t)
      if (own) {
        const lemmas = retarget(own.goal, to, own.lemmas, b, until, true,report)
        if (!lemmas) return undefined
        source = own; target = {goal: to, lemmas}
      }
      let out: Tree | undefined
      if ('leaf' in t) out = leaf(source.goal, to, t, mainPath(options?.native?.from,source.lemmas,a), mainPath(options?.native?.to,target.lemmas,b), until,report)
      else {
        const known = decide(t.split, b)
        if (known !== undefined) out = visit(known ? t.yes : t.no, put(a, t.split, known), b, source, target)
        else {
          const yes = visit(t.yes, put(a, t.split, true), put(b, t.split, true), source, target)
          const no = yes && visit(t.no, put(a, t.split, false), put(b, t.split, false), source, target)
          if (yes && no) out = {split: t.split, yes, no}
        }
      }
      // If pruning exposed a separately marked child, do not overwrite it.
      if (out && own && !marked.has(out)) markConditionalProof(to, out, target.lemmas)
      return out
    }
    const out = visit(tree, before, after, {goal: from, lemmas: []}, {goal: to, lemmas: []})
    if(!out)return report({stage:'transport',part:'main',reason:alive(until)?'tree-transport-refused':'deadline'})
    return checked(to, out, after, until,options?.native?.to) ? out : report({stage:'transport-check',part:'main',reason:alive(until)?'native-tree-check':'deadline'})
  } catch (error) {
    if (options?.rethrowBudgetExpired && error instanceof BudgetExpired) throw error
    return reporter(options)({stage:'exception',part:'main',reason:error instanceof Error?error.name:'non-error'})
  }
}

/** Finalize at the empty root. Each local list is guarded by its entry path so
 * exporting it cannot add assumptions to unrelated ordinary siblings. Every
 * leaf is then reindexed, even if it did not originally carry metadata. */
export function collectConditionalCertificate(goal: Goal, tree: Tree, until: number, options?: ConditionalTransportOptions): {tree: Tree, lemmas: LemmaCut[]} | undefined {
  const report=reporter(options),native=options?.native?.to
  try {
    if(!validNative(native))return report({stage:'cut-validation',part:'main',reason:'invalid-native-cuts-or-counts'})
    const lemmas: LemmaCut[] = []
    const collect = (t: Tree, path: Path): boolean => {
      if (!alive(until)) return false
      const own = marked.get(t)
      if (own) {
        const cuts = retarget(own.goal, goal, own.lemmas, path, until,false,report)
        if (!cuts) return false
        for (const cut of cuts) { if (!alive(until)) return false; lemmas.push(cut) }
      }
      return 'leaf' in t || legalSplit(t, path) && collect(t.yes, put(path, t.split, true)) && collect(t.no, put(path, t.split, false))
    }
    if (!collect(tree, new Map())) return report({stage:'collection',part:'main',reason:alive(until)?'cut-or-branch-refused':'deadline'})
    const finish = (t: Tree, path: Path, context: Context): Tree | undefined => {
      if (!alive(until)) return undefined
      context = marked.get(t) ?? context
      if ('leaf' in t) return leaf(context.goal, goal, t, mainPath(native,context.lemmas,path), mainPath(native,lemmas,path), until,report)
      const yes = finish(t.yes, put(path, t.split, true), context)
      const no = yes && finish(t.no, put(path, t.split, false), context)
      return yes && no ? {split: t.split, yes, no} : undefined
    }
    const out = finish(tree, new Map(), {goal, lemmas: []})
    return out && alive(until) && checkGoalLemmas(goal, out, lemmas,native?.frames,native?.counts,native?.monos,native?.lins) && alive(until) ? {tree: out, lemmas} : report({stage:'collection-check',part:'main',reason:alive(until)?'native-certificate-check':'deadline'})
  } catch (error) {
    if (options?.rethrowBudgetExpired && error instanceof BudgetExpired) throw error
    return reporter(options)({stage:'exception',part:'main',reason:error instanceof Error?error.name:'non-error'})
  }
}
