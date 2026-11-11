// Compose fixed-operation proposals onto one unrestricted counted STEP goal.
// Every leaf is reindexed; the complete certificate is checked at the end.
import {type Law, all, n, same, x} from './machine.ts'
import {type GuardCountContext} from './count-guard-context.ts'
import {type CountRequestBuilder, type CountStrategyProof, finishCountStrategy} from './count-strategy.ts'
import {finiteCountChoice} from './count-cases.ts'
import {countCertificateRenamer} from './count-cert-rename.ts'
import {countStageTrace, type CountStageObserver} from './count-stage-trace.ts'
import {dedupeCountInstances, minimizeCountCertificate} from './count-certificate-minimize.ts'
import {countRowReindexer, operationRefutation} from './count-row-reindex.ts'
import {type CountCert, type Goal, type Instances, type Path, type Tree, boundOf, canon, canonFlip, checkMC, countedObligations, framePath, mcGoal} from '../kernel/kernel.ts'
import {late, rowsAt, withDeadline} from '../kernel/prove.ts'
import {type Lin, type Step, add, k} from './solver.ts'
export type FixedOperationProof = {value: number, proof: CountStrategyProof}
export function composeCountOperationProofs(context: GuardCountContext, family: Law[], law: Law, cases: FixedOperationProof[], until: number, requestFor: CountRequestBuilder, observe?: (stage: string, value?: number) => void, options: {reindexMode?: 'offset' | 'exact', initial?: CountCert, trace?: CountStageObserver, minimize?: boolean} = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    const trace = countStageTrace(options.trace, 'composition-total')
    try {
      trace.mark('composition-setup', 'untrusted-assembly')
      const m = context.machine, choice = finiteCountChoice(m), target = family.indexOf(law)
      if (!choice || target < 0 || late(until)) return
      const [operation, values] = choice, ordered = [...values].sort((a, b) => a - b)
      if (cases.length !== ordered.length || ordered.some(value => cases.filter(c => c.value === value).length !== 1)) return
      trace.mark('certificate-prefix', 'untrusted-assembly')
      let prefix = 'countCase$'
      const scope = JSON.stringify([m, family, cases])
      while (scope.includes('"' + prefix)) prefix = '$' + prefix
      trace.mark('merge-setup', 'untrusted-assembly')
      const common: CountCert = {reads: [], insts: [], picks: [], frames: [], monos: [], lins: [], tree: {leaf: []}}
      const readNames = new Map<string, string>(), instanceNames = new Map<string, string>(), tuples = new Map<string, Set<string>>()
      let instances: Instances = {}
      const sources: {value: number, cert: CountCert, instances: Instances}[] = []
      let transferring: number | undefined
      const arity = (name: string): number | undefined => {
        const found = [...family, ...(m.facts ?? [])].find(l => l.name === name)
        if (found) return found.forall ? 1 + (found.keys?.length ?? 0) : 0
        const flag = name.startsWith('?') && m.step.flags?.[name.slice(1)]
        return flag && flag.op === 'all' ? boundOf(flag).length : undefined
      }
      for (const value of ordered) {
        trace.mark('merge-case', 'untrusted-assembly', value)
        if (late(until)) return
        const source = cases.find(c => c.value === value)!, raw = source.proof.certs[`${law.name} @step`]
        if (!raw || raw.lemmas?.length || raw.picks?.length) return
        const renamed = new Map<string, string>()
        for (const [id, map, key] of raw.reads) {
          const signature = JSON.stringify([map, key]); let name = readNames.get(signature)
          if (!name) {name = prefix + 'r' + common.reads.length; readNames.set(signature, name); common.reads.push([name, map, key])}
          renamed.set(id, name)
        }
        for (const inst of raw.insts) {
          const terms = inst.terms.map(([coefficient, id]) => [coefficient, renamed.get(id) ?? id] as [number, string])
          const signature = JSON.stringify([inst.unit, inst.below, [...terms].sort((a, b) => a[1].localeCompare(b[1]) || a[0] - b[0])])
          let name = instanceNames.get(signature)
          if (!name) {name = prefix + 'w' + common.insts.length; instanceNames.set(signature, name); common.insts.push({...inst, wit: name, terms})}
          if (renamed.has(inst.wit) && renamed.get(inst.wit) !== name) return
          renamed.set(inst.wit, name)
        }
        const rename = countCertificateRenamer(renamed, until), cert = rename.certificate(raw)
        if (new Set(cert.reads.map(r => r[0])).size !== cert.reads.length) return
        const local: Instances = {}
        for (const [name, terms] of Object.entries(source.proof.instances)) {
          const n = arity(name)
          if (n === undefined || n === 0 && terms.length || n && terms.length % n) return
          const converted = terms.map(rename.expression); local[name] = converted
          const seen = tuples.get(name) ?? new Set<string>(); tuples.set(name, seen)
          if (n) for (let i = 0; i < converted.length; i += n) {const tuple = converted.slice(i, i + n), key = JSON.stringify(tuple); if (!seen.has(key)) {seen.add(key); (instances[name] ??= []).push(...tuple)}}
        }
        for (const key of ['frames', 'monos', 'lins'] as const) {
          const known = new Set(common[key]!.map(c => JSON.stringify(c)))
          for (const cut of cert[key] ?? []) if (!known.has(JSON.stringify(cut))) {known.add(JSON.stringify(cut)); (common[key] as unknown[]).push(cut)}
        }
        sources.push({value, cert, instances: local})
      }
      if (options.minimize) {
        const compact = dedupeCountInstances(family, m.facts ?? [], instances)
        instances = compact.instances
        options.trace?.({stage: 'minimize-instances', removed: compact.removed.length})
      }
      trace.mark('target-obligation-build', 'untrusted-assembly')
      const packet = countedObligations(m, family, {[law.name]: instances}, target).at(-1)!, goal = mcGoal(packet.goal.hyps, packet.decls, common)
      if (!goal) return
      trace.mark('reindex-setup', 'untrusted-assembly')
      const stats = {hits: 0, layouts: 0}, offsets = options.reindexMode !== 'exact'
      const reindex = countRowReindexer(goal, {offsets, stats})
      const fallback = (path: Path): Tree | undefined => late(until) ? undefined :
        operationRefutation(rowsAt(goal, framePath(common.frames!, [], path, common.monos!, common.lins!)), operation)
      const transport = (sourceGoal: Goal, source: CountCert, tree: Tree, before: Path, after: Path): Tree | undefined => {
        if (late(until)) return
        if ('split' in tree) {
          const id = canon(tree.split), known = Object.keys(tree.split).every(k => k === '1') ? (tree.split['1'] ?? 0) <= 0 : after.get(id)?.holds ?? (after.has(canonFlip(tree.split)) ? !after.get(canonFlip(tree.split))!.holds : undefined)
          const add = (p: Path, holds: boolean) => new Map(p).set(id, {lin: tree.split, holds})
          if (known !== undefined) return transport(sourceGoal, source, known ? tree.yes : tree.no, add(before, known), after)
          const yes = transport(sourceGoal, source, tree.yes, add(before, true), add(after, true)), no = yes && transport(sourceGoal, source, tree.no, add(before, false), add(after, false))
          return yes && no ? {split: tree.split, yes, no} : undefined
        }
        const old = rowsAt(sourceGoal, framePath(source.frames ?? [], [], before, source.monos ?? [], source.lins ?? [])), current = rowsAt(goal, framePath(common.frames!, [], after, common.monos!, common.lins!)), index = reindex(sourceGoal, old, current)
        const leaf: Step[] = []
        for (const step of tree.leaf) {if (step.kind !== 'input') leaf.push(step); else {const i = index(step.index); if (i === undefined) {observe?.('missing-row:' + (old[step.index] ? canon(old[step.index]!.lin) : step.index), transferring); return}; leaf.push({...step, index: i})}}
        const products: [number, number][] = []
        for (const [a, b] of tree.products ?? []) {const i = index(a), j = index(b); if (i === undefined || j === undefined) return; products.push([i, j])}
        return {leaf, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: tree.squares} : {})}
      }
      const branch = (i: number, path: Path): Tree | undefined => {
        if (late(until)) return
        if (i === ordered.length) return fallback(path)
        const value = ordered[i]!, source = sources.find(c => c.value === value)!, upper: Lin = add({[operation]: 1}, k(-value)), lower: Lin = add({[operation]: -1}, k(value))
        const yesUpper = new Map(path).set(canon(upper), {lin: upper, holds: true}), exact = new Map(yesUpper).set(canon(lower), {lin: lower, holds: true})
        trace.mark('source-obligation-build', 'untrusted-assembly', value)
        const fixed = {...m, assume: all(...(m.assume ? [m.assume] : []), same(x(operation), n(value)))}, original = countedObligations(fixed, family, {[law.name]: source.instances}, target).at(-1)!, from = mcGoal(original.goal.hyps, original.decls, source.cert)
        if (!from) return
        trace.mark('reindex-case', 'untrusted-assembly', value)
        transferring = value; observe?.('reindex', value)
        const yes = transport(from, source.cert, source.cert.tree, new Map(), exact), tooLow = yes && fallback(new Map(yesUpper).set(canon(lower), {lin: lower, holds: false})), no = tooLow && branch(i + 1, new Map(path).set(canon(upper), {lin: upper, holds: false}))
        return yes && tooLow && no ? {split: upper, yes: {split: lower, yes, no: tooLow}, no} : undefined
      }
      const tree = branch(0, new Map())
      if (!tree) {
        if (!offsets || late(until)) return
        trace.pause()
        observe?.('offset-retry-exact')
        return composeCountOperationProofs(context, family, law, cases, until, requestFor, observe, {...options, reindexMode: 'exact'})
      }
      trace.mark('tree-shape-check', 'untrusted-assembly')
      observe?.('offset-layouts', stats.layouts); observe?.('offset-hits', stats.hits)
      observe?.('final-check')
      const shape = (t: Tree, path: Set<string>): string | undefined => {
        if ('leaf' in t) return
        const key = canon(t.split)
        if (path.has(key)) return 'repeated:' + key
        if (Object.keys(t.split).every(k => k === '1')) return 'constant:' + key
        const next = new Set(path).add(key); return shape(t.yes, next) ?? shape(t.no, next)
      }
      const badShape = shape(tree, new Set())
      if (badShape) observe?.('bad-tree-shape:' + badShape)
      const original = {...common, tree}
      let certificate: CountCert = original
      if (options.minimize) {
        trace.mark('certificate-minimize', 'untrusted-assembly')
        const smaller = minimizeCountCertificate(packet.goal.hyps, packet.decls, original, until)
        certificate = smaller.cert
        options.trace?.({stage: 'minimize', ...smaller.stats})
      }
      trace.pause()
      const finish = (certificate: CountCert) => options.initial ? (() => {
        trace.mark('final-obligation-build', 'untrusted-assembly')
        const packets = countedObligations(m, family, {[law.name]: instances}, target)
        if (packets.length !== 2 || late(until)) return
        const initial = packets[0]!, step = packets[1]!, cert = certificate
        trace.mark('native-step-check', 'trusted-check')
        if (!checkMC(step.goal.hyps, step.decls, cert)) return
        trace.mark('native-init-check', 'trusted-check')
        if (!checkMC(initial.goal.hyps, initial.decls, options.initial!)) return
        trace.mark('certificate-return', 'untrusted-assembly')
        return late(until) ? undefined : {instances, certs: {[step.goal.name]: cert, [initial.goal.name]: options.initial!}}
      })() : finishCountStrategy(m, family, law, instances, context.shape.voteMap, certificate, until, requestFor, (stage, checked) => observe?.(stage + ':' + checked), {tailTrace: options.trace})
      let result = finish(certificate)
      if (!result && certificate !== original && !late(until)) {
        options.trace?.({stage: 'minimize-fallback'})
        result = finish(original)
      }
      if (!result && offsets && !late(until)) {
        trace.pause()
        observe?.('offset-retry-exact')
        return composeCountOperationProofs(context, family, law, cases, until, requestFor, observe, {...options, reindexMode: 'exact'})
      }
      return result
    } catch (error) {observe?.('compose-error:' + (error instanceof Error ? error.message : String(error))); return}
    finally {trace.finish()}
  })
}
