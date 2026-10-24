// The conformance cases through the interchange format, to Lean: the cases are written as interchange documents (one
// certificate each, its tampered twins documents of their own), then read back in another process, checked by the
// standalone checker (checkDocument) and written as Lean through lean-kernel's emitters, each claim computed to the
// checker's answer, for Lean to compute again:
//   bun interchange/lean.ts write <dir> [nonterm kind rationals goals cyclic rings counts, e.g. --nonterm 40]
//   bun interchange/lean.ts emit <dir> <lean dir>        (IxNonTerm.lean, IxKind.lean, IxRat.lean, IxGoals.lean, IxCyclic.lean, IxRings.lean)
// Each `example : check… = b := by decide +kernel` holds in Lean exactly when Lean's check computes the checker's b. The
// kinds and the Lean check each is computed by:
//   recur      NonTerm.lean's checkRecur (core/conformance.ts's recurCases: found, tampered, forged)
//   kInduction KInd.lean's checkKInd (kindCases: found; each twin as KInd's literal, meta.lean, or a certificate of its own)
//   qgoals     Rationals.lean's Q.checkGoal (randomQCase's goals, growQ's trees, qtampered's twins)
//   goals      Kernel.lean's checkGoal, each goal of a machine's laws (examples' rules, usual trees; twins tampered in the JSON)
//   cyclic     Cyclic.lean's checkCyclic (the examples' rules' cyclic certificates; twins with a node changed in the JSON)
//   termination Data.lean's termination_by under the measures the document holds (ringCase; the functions' Lean from
//              the case, which the format doesn't carry), each obligation's cyclic proof the checker's
import {mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {checkDocument} from './check.ts'
import {type Certificate, type Document, type Json, fromInterchange, toInterchange} from './format.ts'

const [mode, dir, leanDir] = process.argv.slice(2)
const num = (f: string, d: number) => { const i = process.argv.indexOf(`--${f}`); return i >= 0 ? Number(process.argv[i + 1]) : d }
if (!dir || (mode !== 'write' && mode !== 'emit') || (mode === 'emit' && !leanDir)) { console.error('usage: lean.ts write <dir> [--nonterm N --kind N --rationals N --goals N --cyclic N --rings N] | emit <dir> <lean dir>'); process.exit(2) }
mkdirSync(dir, {recursive: true})
const put = (name: string, c: Certificate, meta: Json) => { writeFileSync(join(dir, `${name}.json`), JSON.stringify(toInterchange(c, meta))); return `${name}.json` }

if (mode === 'write') {
  const conf = await import('../core/conformance.ts')
  conf.reseed(Number(process.env.FUZZ_SEED ?? 4242))
  const kernel = await import('../kernel/kernel.ts')
  const counts: Record<string, number> = {}
  const count = (k: string) => { counts[k] = (counts[k] ?? 0) + 1 }
  // nontermination: each loop's found certificate, its twins pointing to it
  const found = new Map<object, string>()
  conf.recurCases(num('nonterm', 40)).forEach((k, i) => {
    let ans: boolean
    try { ans = kernel.checkRecur(k.loop, k.recur) } catch { ans = false }
    const of = found.get(k.loop)
    const name = put(`recur-${String(i).padStart(3, '0')}`, {kind: 'recur', loop: k.loop, recur: k.recur}, {what: k.what, family: k.family, kernel: ans, ...(of ? {of} : {})})
    if (k.what === 'found') found.set(k.loop, name)
    count(`recur ${k.what === 'found' ? 'found' : 'twin'}`)
  })
  // k-induction
  conf.kindCases(num('kind', 12)).forEach((c, i) => {
    const of = put(`kind-${String(i).padStart(3, '0')}`, {kind: 'kInduction', machine: c.m, laws: c.laws, kInduction: c.kl, proof: c.proof}, {what: 'found', kernel: conf.kindAnswer(c, c)})
    count('kInduction found')
    c.tampers.forEach((t, j) => {
      put(`kind-${String(i).padStart(3, '0')}-t${j}`, {kind: 'kInduction', machine: c.m, laws: c.laws, kInduction: t.kl, proof: t.proof}, {what: t.what, of, kernel: conf.kindAnswer(c, t), ...(t.lean ? {lean: t.lean as unknown as Json} : {})})
      count('kInduction twin')
    })
  })
  // rationals
  const {growQ} = await import('../kernel/qprove.ts')
  for (let i = 0, n = num('rationals', 60); i < n; i++) {
    const k = conf.randomQCase(1 + (i % 3))
    for (const [gi, g] of conf.qgoals(k).proven.entries()) {
      const r = growQ(g)
      if (!('tree' in r)) continue
      const of = put(`rat-${String(i).padStart(3, '0')}-${gi}`, {kind: 'qgoals', goals: [{goal: g, tree: r.tree}]}, {what: 'proven', kernel: kernel.checkQTree(g, r.tree)})
      count('qgoals proven')
      conf.qtampered(r.tree).forEach((t, j) => { put(`rat-${String(i).padStart(3, '0')}-${gi}-t${j}`, {kind: 'qgoals', goals: [{goal: g, tree: t.tree}]}, {what: t.what, of, kernel: kernel.checkQTree(g, t.tree)}); count('qgoals twin') })
    }
  }
  // machines' laws (the examples' rules): usual trees as `laws` documents, cyclic certificates as `cyclic` ones
  const {proveLaws} = await import('../kernel/prove.ts')
  const {domains} = await import('../examples/index.ts') as {domains: {domain: string, cases: {kind: string, name: string, rule?: {machine: import('../core/machine.ts').Machine}, laws?: import('../core/machine.ts').Law[]}[]}[]}
  const rules = domains.flatMap(d => d.cases.flatMap(c => (c.kind === 'rule' && c.rule && c.laws ? [{name: `${d.domain} ${c.name}`, m: c.rule.machine, laws: c.laws}] : [])))
  const pickRules = (n: number) => rules.filter((_, i) => i % Math.max(1, Math.floor(rules.length / n)) === 0).slice(0, n)
  const env = process.env as Record<string, string | undefined>
  const tamperJson = (doc: Document, f: (x: Record<string, Json>) => boolean): Document | undefined => {
    const twin = JSON.parse(JSON.stringify(doc)) as Document
    const walk = (x: Json | undefined): boolean => (Array.isArray(x) ? x.some(walk) : x && typeof x === 'object' ? f(x as Record<string, Json>) || Object.entries(x).some(([k, y]) => k !== 'meta' && k !== 'columns' && walk(y)) : false)
    return walk(twin as Json) ? twin : undefined
  }
  const leafTampers: [string, (x: Record<string, Json>) => boolean][] = [
    ['a leaf\'s last step dropped', x => (Array.isArray(x.leaf) && x.leaf.length >= 2 ? (x.leaf.pop(), true) : false)],
    ['a combination\'s multiplier raised', x => { const s = Array.isArray(x.leaf) ? x.leaf.find(y => Array.isArray(y) && y[0] === 'combine') as number[] | undefined : undefined; return s ? ((s[3] = s[3]! + 1), true) : false }],
    ['a split\'s constant moved', x => (Array.isArray(x.split) ? ((x.split[0] = ((x.split[0] as number | null) ?? 0) + 1), true) : false)],
  ]
  // kernel.ts's answer on a document made here (a twin exists as JSON alone: read back, then the kernel's entry point)
  const {checkCertificate} = await import('./check.ts')
  const kernelOn = (doc: Document): boolean => { try { return checkCertificate(fromInterchange(JSON.parse(JSON.stringify(doc)))).every(x => x.accepted) } catch { return false } }
  const was = env.GDP_CERT
  env.GDP_CERT = 'usual'
  pickRules(num('goals', 12)).forEach((r, i) => {
    const p = proveLaws(r.m, r.laws)
    if (!p.proven || !p.checked || !p.proof) return
    const doc = toInterchange({kind: 'laws', machine: p.machine ?? r.m, laws: p.laws ?? r.laws, proof: {instances: p.proof.instances, trees: p.proof.trees}}, {what: 'proven', rule: r.name})
    const of = `laws-${String(i).padStart(3, '0')}.json`
    doc.meta = {what: 'proven', rule: r.name, kernel: kernelOn(doc)}
    writeFileSync(join(dir, of), JSON.stringify(doc)); count('laws proven')
    leafTampers.forEach(([what, f], j) => { const t = tamperJson(doc, f); if (t) { t.meta = {what, of, kernel: kernelOn(t)}; writeFileSync(join(dir, `laws-${String(i).padStart(3, '0')}-t${j}.json`), JSON.stringify(t)); count('laws twin') } })
  })
  if (was === undefined) delete env.GDP_CERT; else env.GDP_CERT = was
  const falseC = {op: '<', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const nodeTampers: [string, (x: Record<string, Json>) => boolean][] = [
    ['a node\'s conclusion made false', x => (Array.isArray(x.hyps) && 'concl' in x ? ((x.concl = falseC), true) : false)],
    ['a use made of another node', x => (Array.isArray(x.premises) && typeof x.node === 'number' ? ((x.node = x.node + 1), true) : false)],
    ['a node\'s rank made constant', x => (Array.isArray(x.rank) && x.rank.length > 0 && 'concl' in x ? ((x.rank = x.rank.map(() => ({op: 'const', value: 0}))), true) : false)],
  ]
  pickRules(num('cyclic', 12)).forEach((r, i) => {
    const p = proveLaws(r.m, r.laws)
    const cyc = (p.proof as {cyclic?: import('../kernel/cyclic.ts').Cyclic} | undefined)?.cyclic
    if (!p.proven || !cyc) return
    const doc = toInterchange({kind: 'cyclic', cyclic: cyc}, {what: 'found', rule: r.name})
    const of = `cyclic-${String(i).padStart(3, '0')}.json`
    doc.meta = {what: 'found', rule: r.name, kernel: kernelOn(doc)}
    writeFileSync(join(dir, of), JSON.stringify(doc)); count('cyclic found')
    nodeTampers.forEach(([what, f], j) => { const t = tamperJson(doc, f); if (t) { t.meta = {what, of, kernel: kernelOn(t)}; writeFileSync(join(dir, `cyclic-${String(i).padStart(3, '0')}-t${j}.json`), JSON.stringify(t)); count('cyclic twin') } })
  })
  // rings: the measures found, as a termination document (the functions' Lean definitions kept beside it, from the case)
  for (let i = 0, n = num('rings', 24); i < n; i++) {
    const r = conf.ringCase()
    let ts: ({measure: {comps: {coef: number[], c: number}[]}, text: string, obligations: {law: {name: string}, proof?: {proven: boolean, proof?: import('../kernel/cyclic.ts').Cyclic}}[]} | undefined)[]
    try { ts = r.fns.map(f => (void f.fn.ring, f.fn.termination)) } catch { count('ring refused (runs forever)'); continue }
    if (!ts.every(t => t)) { count('ring structural'); continue }
    const obligations = ts.flatMap((t, j) => t!.obligations.flatMap(o => (o.proof?.proven && o.proof.proof ? [{function: r.fns[j]!.fn.name, law: o.law.name, cyclic: o.proof.proof}] : [])))
    const cyc = await import('../kernel/cyclic.ts')
    put(`ring-${String(i).padStart(3, '0')}`, {kind: 'termination', functions: r.fns.map(f => f.fn.name), text: ts[0]!.text, measures: ts.map(t => t!.measure), obligations},
      {what: 'taken', kernel: obligations.every(o => cyc.refuseCyclic(o.cyclic) === undefined), family: r.family, name: r.name, params: r.fns.map(f => f.fn.params.map(q => q.name)), lean: r.lean('\u0001F', '\u0001G')})
    count('termination')
  }
  console.log(JSON.stringify(counts))
  process.exit(0)
}

// --- emit: each document read back, checked, and written as Lean --------------------------------------------------------
const emitter = await import('../lean-kernel/emit.ts'), qlean = await import('../lean-kernel/qlean.ts'), kernel = await import('../kernel/kernel.ts')
mkdirSync(leanDir!, {recursive: true})
const files = readdirSync(dir).filter(f => f.endsWith('.json')).sort()
const docs = new Map(files.map(f => [f, JSON.parse(readFileSync(join(dir, f), 'utf8')) as Document]))
const metaOf = (d: Document) => (d.meta ?? {}) as {what?: string, of?: string, kernel?: boolean, lean?: {k: number, base: number[], law?: import('../core/machine.ts').C}, name?: string, params?: string[][], lean_?: string} & Record<string, Json>
const tally: Record<string, {examples: number, accepted: number, refused: number, kernelAgrees: number, kernelKnown: number, notWritten: number}> = {}
const t = (k: string) => (tally[k] ??= {examples: 0, accepted: 0, refused: 0, kernelAgrees: 0, kernelKnown: 0, notWritten: 0})
const answer = (f: string) => {
  const d = docs.get(f)!, r = checkDocument(d), k = metaOf(d).kernel, row = t(String(d.kind))
  if (typeof k === 'boolean') { row.kernelKnown++; if (k === r.accepted) row.kernelAgrees++ }
  return r.accepted
}
// A cyclic twin whose every goal the original's trees refute once each leaf's inputs are found again by their rows'
// values among the twin's rows (kernel.ts reads them by place): what the twin keeps of the proof up to the rows' order.
const {mainGoal, premiseGoal, descentGoal, factsAvoid} = await import('../kernel/cyclic.ts')
function byValue(p: import('../kernel/cyclic.ts').Cyclic, q: import('../kernel/cyclic.ts').Cyclic): boolean {
  const re = (g0: import('../kernel/kernel.ts').Goal, g1: import('../kernel/kernel.ts').Goal, t: import('../kernel/kernel.ts').Tree): boolean => {
    let lost = false
    const go = (u: import('../kernel/kernel.ts').Tree, path: import('../kernel/kernel.ts').Path): import('../kernel/kernel.ts').Tree => {
      if ('split' in u) { const id = kernel.canon(u.split); return {split: u.split, yes: go(u.yes, new Map(path).set(id, {lin: u.split, holds: true})), no: go(u.no, new Map(path).set(id, {lin: u.split, holds: false}))} }
      if (u.products?.length || u.squares?.length) { lost = true; return u }
      const r0 = kernel.leafConstraints(g0, path), r1 = kernel.leafConstraints(g1, path).map(r => kernel.canon(r.lin))
      return {leaf: u.leaf.map(st => { if (st.kind !== 'input') return st; const j = r0[st.index] ? r1.indexOf(kernel.canon(r0[st.index]!.lin)) : -1; if (j < 0) lost = true; return {...st, index: j < 0 ? st.index : j} })}
    }
    const t2 = go(t, new Map())
    try { return !lost && kernel.check(g1, t2) } catch { return false }
  }
  if (p.nodes.length !== q.nodes.length) return false
  return q.nodes.every((n, i) => {
    const o = p.nodes[i]!
    if (!re(mainGoal(p.facts, p.nodes, o), mainGoal(q.facts, q.nodes, n), o.main) || n.uses.length !== o.uses.length) return false
    return n.uses.every((u, j) => {
      const ou = o.uses[j]!, m = q.nodes[u.node], om = p.nodes[ou.node]
      if (!m || !om || m.rank.length !== n.rank.length || !factsAvoid(q.facts, u.subst) || m.hyps.length !== ou.premises.length) return false
      return m.hyps.every((h, k) => re(premiseGoal(p.facts, o, ou, om.hyps[k] ?? h, k), premiseGoal(q.facts, n, u, h, k), ou.premises[k]!)) && re(descentGoal(p.facts, o, ou, om), descentGoal(q.facts, n, u, m), ou.descent)
    })
  })
}
const counted = (kind: string, ok: boolean) => { const row = t(kind); row.examples++; if (ok) row.accepted++; else row.refused++ }
const out: Record<string, string[]> = {nonterm: [], kind: [], rat: [], goals: [], cyclic: [], byValue: [], rings: []}

for (const [f, d] of docs) {
  const m = metaOf(d)
  try {
    switch (d.kind) {
      case 'recur': {
        const c = fromInterchange(d) as Extract<Certificate, {kind: 'recur'}>, ok = answer(f)
        const fallback = m.of ? (fromInterchange(docs.get(m.of)!) as Extract<Certificate, {kind: 'recur'}>).recur : c.recur
        const {loop, recur} = emitter.recurLean(`ix ${f}`, c.loop, fallback)
        out.nonterm!.push(`-- ${f}: ${c.loop.name}: ${m.what}\nexample : checkRecur ${loop} ${recur(c.recur)} = ${ok} := by decide +kernel`)
        counted('recur', ok)
        break
      }
      case 'kInduction': {
        if (m.of) break // twins go with the certificate they are twins of
        const c = fromInterchange(d) as Extract<Certificate, {kind: 'kInduction'}>, ok = answer(f)
        const twins = [...docs].filter(([, x]) => metaOf(x).of === f)
        const start = kernel.kInductionStart(c.machine, c.kInduction, {})
        emitter.seedStepProof(c.machine, c.laws, kernel.kInductionSteps(c.machine, c.kInduction), {proven: true, checked: true, nodes: 0, leaves: 0, proof: c.proof})
        const tampers = twins.flatMap(([tf, x]) => { const tm = metaOf(x); return tm.lean ? [{what: `${tf}: ${tm.what}`, ...tm.lean, expect: answer(tf)}] : [] })
        if (!ok) { t('kInduction').notWritten++; break }
        const id = `ix_${f.replace(/\W/g, '_')}`
        out.kind!.push(emitter.smachineToLean(id, c.machine, c.laws, {kind: {kl: c.kInduction, start: {goal: start, tree: c.proof.trees[start.name]!, inst: {}}, tampers}, noFacts: true}))
        counted('kInduction', ok)
        for (const x of tampers) counted('kInduction', x.expect)
        // A twin with no literal of KInd's: a certificate of its own where the checker accepts it (Lean then proves it).
        for (const [tf, x] of twins) {
          if (metaOf(x).lean) continue
          const tc = fromInterchange(x) as Extract<Certificate, {kind: 'kInduction'}>, tok = answer(tf)
          if (!tok || tc.kInduction.k !== c.kInduction.k) { t('kInduction').notWritten++; continue }
          emitter.seedStepProof(tc.machine, tc.laws, kernel.kInductionSteps(tc.machine, tc.kInduction), {proven: true, checked: true, nodes: 0, leaves: 0, proof: tc.proof})
          const s2 = kernel.kInductionStart(tc.machine, tc.kInduction, {})
          out.kind!.push(`-- ${tf}: ${metaOf(x).what}: accepted\n${emitter.smachineToLean(`${id}_${tf.replace(/\W/g, '_')}`, tc.machine, tc.laws, {kind: {kl: tc.kInduction, start: {goal: s2, tree: tc.proof.trees[s2.name]!, inst: {}}}, noFacts: true})}`)
          counted('kInduction', tok)
        }
        break
      }
      case 'qgoals': {
        const c = fromInterchange(d) as Extract<Certificate, {kind: 'qgoals'}>, ok = answer(f)
        for (const {goal, tree} of c.goals) {
          const names: string[] = []
          const vars = (x: unknown): void => { if (Array.isArray(x)) x.forEach(vars); else if (x && typeof x === 'object') { const o = x as {op?: string, name?: string}; if (o.op === 'var' && o.name && !names.includes(o.name)) names.push(o.name); Object.values(o).forEach(vars) } }
          vars(goal.hyps)
          names.sort()
          const ix = (n: string) => { const j = names.indexOf(n); if (j < 0) names.push(n); return names.indexOf(n) }
          const tl = qlean.qTreeLean(goal, tree, ix), hyps = `[${goal.hyps.map(h => qlean.qCondLean(h, ix)).join(', ')}]`
          out.rat!.push(`-- ${f}: ${m.what}\nexample : Q.checkGoal ${hyps} ${tl} = ${ok} := by decide +kernel`)
        }
        counted('qgoals', ok)
        break
      }
      case 'laws': {
        const c = fromInterchange(d) as Extract<Certificate, {kind: 'laws'}>, ok = answer(f)
        const goals = kernel.obligations(c.machine, c.laws, c.proof.instances)
        let all = true
        for (const [gi, g] of goals.entries()) {
          const tree = c.proof.trees[g.name]
          if (!tree) { all = false; continue }
          let per: boolean
          try { per = kernel.check(g, tree) } catch { per = false }
          all &&= per
          try {
            const x = emitter.encode({name: g.name, goal: g, tree})
            out.goals!.push(`-- ${f}: ${g.name}${m.what ? ` (${m.what})` : ''}\ndef ix_${f.replace(/\W/g, '_')}_${gi}_goal : Goal := ⟨${x.tab},\n  ${x.hyps}⟩\nexample : checkGoal ix_${f.replace(/\W/g, '_')}_${gi}_goal (${x.tree}) = ${per} := by decide +kernel`)
            counted('goals', per)
          } catch (e) { t('goals').notWritten++; if (per) throw e }
        }
        if (all !== ok) throw new Error(`${f}: the goals' answers (${all}) aren't the checker's (${ok})`)
        break
      }
      case 'cyclic': {
        if (m.of) break
        const c = fromInterchange(d) as Extract<Certificate, {kind: 'cyclic'}>, ok = answer(f)
        if (!ok) { t('cyclic').notWritten++; break }
        const twins = [...docs].filter(([, x]) => metaOf(x).of === f).map(([tf, x]) => ({tf, what: `${tf}: ${metaOf(x).what}`, proof: (fromInterchange(x) as Extract<Certificate, {kind: 'cyclic'}>).cyclic, ok: answer(tf)}))
        // (cyclicToLean computes each twin's check to false: a twin the checker accepts goes as a proof of its own)
        // A twin refused only because its rows moved (its trees' rows all there, in another order) is one Lean's check
        // accepts: Lean finds a leaf's rows by value (the emitter claims them), kernel.ts by their place. Those go to
        // IxCyclicByValue.lean, each computed to true, beside the checker's false.
        const moved = (x: {proof: import('../kernel/cyclic.ts').Cyclic}) => byValue(c.cyclic, x.proof)
        const refused = twins.filter(x => !x.ok && !moved(x)), accepted = twins.filter(x => x.ok), shifted = twins.filter(x => !x.ok && moved(x))
        out.cyclic!.push(emitter.cyclicToLean(`ix_${f.replace(/\W/g, '_')}`, c.cyclic, refused.map(x => ({what: x.what, proof: x.proof}))))
        for (const x of accepted) out.cyclic!.push(emitter.cyclicToLean(`ix_${x.tf.replace(/\W/g, '_')}`, x.proof))
        for (const x of shifted) {
          const id = `ixv_${x.tf.replace(/\W/g, '_')}`
          out.byValue!.push(emitter.cyclicToLean(id, c.cyclic, [{what: `${x.what} (refused by the checker; its rows all there, moved)`, proof: x.proof}]).replace(`checkCyclic ${id}_facts ${id}_tampered0 = false`, `checkCyclic ${id}_facts ${id}_tampered0 = true`))
          t('cyclic by value').examples++
        }
        counted('cyclic', ok)
        for (const x of twins) if (x.ok || !moved(x)) counted('cyclic', x.ok)
        break
      }
      case 'termination': {
        const c = fromInterchange(d) as Extract<Certificate, {kind: 'termination'}>, ok = answer(f)
        if (!ok) { t('termination').notWritten++; break }
        const params = (m.params ?? []) as string[][]
        // a measure as Lean reads it (as lean-kernel/conformance.ts --rings writes it): Lx where it has several parts
        const comp = (ps: string[], q: {coef: number[], c: number}) => {
          const pos = [...q.coef.flatMap((k, i) => (k > 0 ? [`${k} * ${ps[i]}`] : [])), ...(q.c > 0 ? [String(q.c)] : [])], neg = [...q.coef.flatMap((k, i) => (k < 0 ? [`${-k} * ${ps[i]}`] : [])), ...(q.c < 0 ? [String(-q.c)] : [])]
          const sum = (ts: string[]) => (ts.length ? ts.join(' + ') : '0')
          return neg.length ? `(${sum(pos)} - (${sum(neg)}))` : `(${sum(pos)})`
        }
        const mOf = (j: number) => { const ms = c.measures[j]!, ps = params[j] ?? []; return ms.comps.length === 1 ? comp(ps, ms.comps[0]!) : `Lx.mk [${ms.comps.map(q => comp(ps, q)).join(', ')}]` }
        const text = (typeof m.lean === 'string' ? m.lean : '').replace('termination_by \u0001F', `termination_by ${mOf(0)}`).replace('termination_by \u0001G', `termination_by ${mOf(1)}`)
        out.rings!.push(`-- ${f}: ${c.text}\nnamespace ${String(m.name)}\n${text}\nend ${String(m.name)}`)
        counted('termination', ok)
        break
      }
      case 'goals': case 'stepLaws': case 'progress': case 'liveness': case 'loop': case 'fold': case 'qmachine': break // (no conformance case of Lean's here)
    }
  } catch (e) {
    console.error(`${f}: ${e instanceof Error ? e.message : String(e)}`)
    t(String(d.kind)).notWritten++
  }
}
const files2: [string, string, string][] = [
  ['IxNonTerm.lean', 'import NonTerm\nopen Kern Cert', 'nonterm'], ['IxKind.lean', 'import KInd\nopen Kern Cert', 'kind'], ['IxRat.lean', 'import Rationals\nopen Cert Kern', 'rat'],
  ['IxGoals.lean', 'import Kernel\nopen Kern Cert', 'goals'], ['IxCyclic.lean', 'import Cyclic\nopen Kern Cert', 'cyclic'], ['IxCyclicByValue.lean', 'import Cyclic\nopen Kern Cert', 'byValue'], ['IxRings.lean', 'import Data\nopen Kern\nset_option linter.unusedSimpArgs false', 'rings'],
]
for (const [file, head, key] of files2) writeFileSync(join(leanDir!, file), `${head}\n\n/-! Interchange documents read back, checked by gdp-wired-check and computed again by Lean: each example holds exactly\nwhen Lean's check gives the checker's answer. -/\n\n${out[key]!.join('\n\n')}\n`)
console.log(JSON.stringify(tally))
