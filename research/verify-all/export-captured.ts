// Export only certificates observed in accepted harness calls. No proof search is rerun here.
import {readFileSync, writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {checkLaws, checkCountedLaws, ghostedOk, someOfGhostsOk, substC, plainOf, sideGoals, type Ghosted} from '../../kernel/kernel.ts'
import {cmachineToLean, seedStepProof, smachineToLean} from '../../lean-kernel/emit.ts'
import {evalC, interpret} from '../../core/machine.ts'
import {watch} from '../../core/watch.ts'
const [file, target] = process.argv.slice(2)
const raw = readFileSync(file!, 'utf8'), x = JSON.parse(raw, (_k, v) => v?.__map ? new Map(v.__map) : v?.__set ? new Set(v.__set) : v)
const sha = (v: string) => createHash('sha256').update(v).digest('hex')
const canonical = (v: any): string => JSON.stringify(v, (_k, x) => x && typeof x === 'object' && !Array.isArray(x) ? Object.fromEntries(Object.keys(x).sort().filter(k => x[k] !== undefined).map(k => [k, x[k]])) : x)
// Rename only lexical quantifier, map-write and sum binders; never normalize free names or constants.
const alpha = (v: any, env = new Map<string, string>(), depth = 0): any => {
  if (!v || typeof v !== 'object') return v
  if (Array.isArray(v)) return v.map(y => alpha(y, env, depth))
  if (v.op === 'var' && env.has(v.name)) return {...v, name: env.get(v.name)}
  if (typeof v.each === 'string' && v.value !== undefined) {
    const inner = new Map(env); inner.set(v.each, `__verify_bound_${depth}`)
    return {...v, each:inner.get(v.each), value:alpha(v.value,inner,depth+1)}
  }
  if (typeof v.key === 'string' && v.term !== undefined) {
    const inner = new Map(env); inner.set(v.key, `__verify_bound_${depth}`)
    return {...v,key:inner.get(v.key),term:alpha(v.term,inner,depth+1)}
  }
  if (v.op === 'all') {
    const names = [v.key, ...(v.keys ?? [])], inner = new Map(env)
    names.forEach((name, i) => inner.set(name, `__verify_bound_${depth + i}`))
    return {...v, key: inner.get(v.key), ...(v.keys ? {keys: v.keys.map((k: string) => inner.get(k))} : {}), c: alpha(v.c, inner, depth + names.length), ...(v.witness ? {witness: alpha(v.witness, env, depth)} : {})}
  }
  return Object.fromEntries(Object.entries(v).map(([k, y]) => [k, alpha(y, env, depth)]))
}
const result: any = {id: x.row.id, captureSha256: sha(raw), harness: x.row, accepted: !!(x.verdict.out.proven && x.verdict.out.checked)}
const v = x.verdict.out
if (v.run) {
  const {machine: m} = x.verdict, it = interpret(m), run = v.run, states: any[] = []
  const pre = !m.pre || evalC(m.pre, run.params, {scalars: {}, maps: {}}, m)
  if (!pre) throw new Error('captured trace violates model precondition')
  let st = it.init(run.params)
  const checks = x.verdict.laws.map((law: any) => ({law, on: watch(m, it, law, run.params, 3)}))
  let failedLaw = checks.find((q: any) => !q.on.start(st))?.law.name
  states.push(st)
  for (const shown of run.trace) {
    const input = Object.fromEntries(Object.entries(shown).map(([k, v]) => [k, v && typeof v === 'object' ? new Map(Object.entries(v).map(([key, value]) => [Number(key), value])) : v]))
    const before = st
    st = it.step(run.params, st, input as any); states.push(st)
    failedLaw ??= checks.find((q: any) => !q.on.step(before, input, st))?.law.name
  }
  // p.bad is the small TLC-instance predicate (often only nodes 0..2). It is diagnostic, not a validator of arbitrary production-domain traces.
  const {protocols} = await import('../../research/protocols/ic3syn/models.ts')
  const p = protocols.find(p => p.id === x.row.id)!
  const read = {cell: (map: string, key: number) => st.maps[map]?.get(key) ?? (st as any).defaults?.[map] ?? m.maps?.[map] ?? 0, scalar: (name: string) => { const value = st.scalars[name]; if (value === undefined) throw new Error(`missing scalar ${name}`); return value }}
  result.replay = {steps: run.trace.length, pre, failedLaw: failedLaw ?? null, bad: p.bad?.(read) ?? null, method: 'interpret(machine).init(params); revive carried maps; step each input (assume checked); watch stated laws and p.bad(final)', runSha256: sha(JSON.stringify(run, (_k,v) => v instanceof Map ? [...v] : v))}
  writeFileSync(target!.replace(/\.lean$/, '.result.json'), JSON.stringify(result, null, 2))
  console.log(JSON.stringify(result)); process.exit(failedLaw ? 0 : 3)
}
if (!result.accepted) { console.log(JSON.stringify(result)); process.exit(0) }
let text: string
try {
  if (x.counted?.checked) {
    const c = x.counted
    if (!x.verdict.laws.every((l: any) => c.laws.some((a: any) => JSON.stringify(a) === JSON.stringify(l)))) throw new Error('captured counted family omits caller law')
    if (!checkCountedLaws(c.machine, c.laws, c.proof)) throw new Error('captured counted certificate no longer checks')
    const original=x.verdict.machine, projection={...c.machine,counts:original.counts}
    if (canonical(alpha(projection))!==canonical(alpha(original))) throw new Error('counted closure changed the original transition system')
    for (const [name,body] of Object.entries(original.counts??{})) if (canonical(c.machine.counts?.[name])!==canonical(body)) throw new Error(`counted closure changed original count ${name}`)
    result.kind = 'counted-machine'; result.laws = c.laws.length
    result.sourceLawEquality = true; result.countedProjectionAlphaEquivalent = true
    result.addedCountViews = Object.keys(c.machine.counts??{}).filter(k=>!(k in (original.counts??{})))
    text = 'import CountMachine\nopen Kern Cert\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n' + cmachineToLean('verified', c.machine, c.laws, c.proof)
  } else {
    const c = x.good
    if (!c) throw new Error('accepted harness verdict exposed no captured whole-family certificate')
    if (!x.verdict.laws.every((l: any) => c.laws.some((a: any) => a.name === l.name))) throw new Error('last captured whole-family certificate omits caller law')
    if (!checkLaws(c.machine, c.laws, c.proof)) throw new Error('captured ordinary trees do not pass checkLaws (possibly transformed existential certificate)')
    result.kind = c.proof.cyclic ? 'ordinary-trees-with-cyclic' : 'ordinary-trees'; result.laws = c.laws.length
    result.sourceLawEquality = x.verdict.laws.every((l: any) => c.laws.some((a: any) => JSON.stringify(a) === JSON.stringify(l)))
    result.machineEquality = canonical(c.machine) === canonical(x.verdict.machine)
    result.machineAlphaEquivalent = canonical(alpha(c.machine)) === canonical(alpha(x.verdict.machine))
    result.machineDifferences = [...new Set([...Object.keys(c.machine), ...Object.keys(x.verdict.machine)])].filter(k => canonical(c.machine[k]) !== canonical(x.verdict.machine[k])).map(k => ({key: k, original: canonical(x.verdict.machine[k])?.slice(0, 900), captured: canonical(c.machine[k])?.slice(0, 900)}))
    let exportLaws = c.laws, opts: any = {}
    const existentials = x.verdict.laws.filter((l: any) => l.some?.length)
    if (!existentials.length && !c.machine.sums && (!result.sourceLawEquality || !result.machineAlphaEquivalent)) throw new Error('ordinary closure differs from original laws/model')
    if (existentials.length) {
      // Recover ghosts and substitutions from captured syntax, not by calling a witness search.
      const original = x.verdict.machine
      const extraVars = Object.keys(c.machine.state).filter(k => !(k in original.state))
      const extraMaps = Object.keys(c.machine.maps ?? {}).filter(k => !(k in (original.maps ?? {})))
      const omit = (o: any, keys: string[]) => o === undefined ? undefined : Object.fromEntries(Object.entries(o).filter(([k]) => !keys.includes(k)))
      const projection = {...c.machine, state: omit(c.machine.state, extraVars), maps: original.maps === undefined ? undefined : omit(c.machine.maps, extraMaps), step: {...c.machine.step, state: original.step.state === undefined ? undefined : omit(c.machine.step.state, extraVars), maps: original.step.maps === undefined ? undefined : omit(c.machine.step.maps, extraMaps)}}
      if (canonical(alpha(projection)) !== canonical(alpha(original))) throw new Error('captured ghost-free projection differs from original beyond bound variable names')
      const g: Ghosted = {orig: projection, vars: Object.fromEntries(extraVars.map(k => [k,{start:c.machine.state[k],step:c.machine.step.state[k]}])), maps: Object.fromEntries(extraMaps.map(k => [k,{start:c.machine.maps[k],write:c.machine.step.maps[k]}]))}
      if (!ghostedOk(g)) throw new Error('captured extra state is not a valid ghost extension')
      const substitutions = existentials.map((law: any, lawIndex: number) => {
        const plain = c.laws.find((l: any) => l.name === law.name), bound = new Set<string>(law.some), sub: any = {}
        const unify = (a: any,b: any): boolean => {
          if (a?.op === 'var' && bound.has(a.name)) { if (sub[a.name] === undefined) sub[a.name] = b; return canonical(sub[a.name]) === canonical(b) }
          if (a === null || b === null || typeof a !== 'object' || typeof b !== 'object') return a === b
          if (Array.isArray(a) || Array.isArray(b)) return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((q,i)=>unify(q,b[i]))
          const ks=Object.keys(a); return ks.length===Object.keys(b).length && ks.every(k=>Object.hasOwn(b,k)&&unify(a[k],b[k]))
        }
        if (!plain || !unify(law.holds, plain.holds)) throw new Error(`cannot recover existential substitution for ${law.name}`)
        // A source existential binder may itself be the added scalar ghost. Give only the logical binder a fresh name.
        const fresh = law.some.map((_:string,i:number)=>`verify$existential$${lawIndex}$${i}`)
        const ren = Object.fromEntries(law.some.map((name:string,i:number)=>[name,{op:'var',name:fresh[i]}]))
        const renamed = {...law, some:fresh, holds:substC(law.holds,{vars:ren,maps:{},flags:{}} as any)}
        const renamedSub = Object.fromEntries(law.some.map((name:string,i:number)=>[fresh[i],sub[name]]))
        if (!someOfGhostsOk(g,renamed,plain,renamedSub)) throw new Error(`recovered existential bridge rejected for ${law.name}`)
        return {law: plain.name, body: renamed.holds, sub: renamedSub, bound:fresh}
      })
      // ex metadata is only a pretty-printing route. The stronger law, keys, instances and trees are unchanged.
      exportLaws = c.laws.map(({ex: _ex, ...l}: any) => l)
      opts = {ghosted:g, ghostSubst:substitutions, free:substitutions.flatMap((s:any)=>s.bound)}
      result.existentialBridge = {kind:'forall_some_of_ghostsubst',extraVars,extraMaps,laws:substitutions.map((s:any)=>s.law),projectionAlphaEquivalent:true}
    }
    if (c.machine.sums && Object.keys(c.machine.sums).length) {
      const names=Object.keys(c.machine.sums), original=x.verdict.machine
      const strip=(o:any)=>o===undefined?undefined:Object.fromEntries(Object.entries(o).filter(([k])=>!names.includes(k)))
      const projection={...c.machine,sums:undefined,state:strip(c.machine.state),step:{...c.machine.step,state:original.step.state===undefined?undefined:strip(c.machine.step.state)}}
      if (canonical(alpha(projection))!==canonical(alpha(original))) throw new Error('captured sum-free projection differs from original')
      result.sumBridge={kind:'Sums.lean',names,projectionAlphaEquivalent:true}
    }
    // The emitter seeds its effective plain machine (sums/history have separate side goals).
    for (const goal of sideGoals(c.machine, exportLaws)) if (!c.proof.trees[goal.name]) throw new Error(`captured certificate lacks side goal ${goal.name}`)
    opts.coverTrees = c.proof.trees
    seedStepProof(plainOf(c.machine), exportLaws, [], {proven: true, checked: true, nodes: 0, leaves: 0, proof: {laws: c.proof, instances: {}, trees: {}}} as any)
    text = 'import GhostMap\nimport History\n' + (c.machine.sums && Object.keys(c.machine.sums).length ? 'import Sums\n' : '') + 'open Kern Cert\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n' + smachineToLean('verified', c.machine, exportLaws, opts)
    if (result.sumBridge) text += '\n#print axioms verified_exact\n#print axioms verified_own\n'
    if (result.existentialBridge) text += '\n#print axioms verified_orig_laws\n' + existentials.map((_:any,i:number)=>`#print axioms verified_ex${i}`).join('\n') + '\n'
  }
  text += '\n#print axioms verified_laws\n'
  if (/\bsorry\b|\badmit\b|native_decide/.test(text)) throw new Error('unsafe theorem or native_decide in export')
  writeFileSync(target!, text); result.leanBytes = text.length; result.leanSha256 = sha(text)
} catch (e) { result.exportError = String(e) }
writeFileSync(target!.replace(/\.lean$/, '.result.json'), JSON.stringify(result, null, 2))
console.log(JSON.stringify(result))
process.exit(result.exportError ? 2 : 0)
