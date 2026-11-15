// Output-only projection of the captured skolem producer. This is not a Lean check.
import {isDeepStrictEqual} from 'node:util'
import type {E, Law, Machine} from '../../core/machine.ts'
import type {ProofOutputNode} from '../../core/proof-output.ts'
import {checkLaws, ghostedMachine, someOfGhostsOk, substC, type Ghosted} from '../../kernel/kernel.ts'
import {retainedSMachineToLean} from '../../lean-kernel/emit.ts'
import type {NativeBundle} from './proof-capture.ts'

type Skolem = {kind:'skolem', original:Machine, laws:Law[], G:Ghosted,
  plains:Record<string,{plain:Law,sub:Record<string,E>}>, family:Law[]}
type SourceTheorem = {publicIndex:number, familyIndex:number, name:string, type:'exists'|'ordinary'}

// Validate with fresh bound labels, but emit the ORIGINAL source body and labels.
// BoundGhost.lean discharges the stronger transfer: bound ghost variables are
// overwritten by the existential assignment; every other ghost remains avoided.
function boundSourceSubstitutionOk(G:Ghosted,law:Law,plain:Law,sub:Record<string,E>):boolean {
  const xs = law.some ?? []
  if(new Set(xs).size !== xs.length || Object.keys(sub).length !== xs.length || !xs.every(x => Object.hasOwn(sub,x))) return false
  if(!xs.some(x => Object.hasOwn(G.vars,x))) return someOfGhostsOk(G,law,plain,sub)
  const used = new Set<string>(), seen = new Set<object>()
  const walk = (x:unknown):void => {
    if(typeof x === 'string') used.add(x)
    else if(x && typeof x === 'object' && !seen.has(x)) {
      seen.add(x)
      for(const [k,v] of Object.entries(x)) { used.add(k); walk(v) }
    }
  }
  walk([G,law,plain,sub])
  const rename:Record<string,E> = Object.create(null), freshSub:Record<string,E> = Object.create(null), fresh:string[] = []
  for(const x of xs) {
    let name = '__source_bound_' + fresh.length
    while(used.has(name)) name += '_'
    used.add(name); fresh.push(name); rename[x] = {op:'var',name}; freshSub[name] = sub[x]!
  }
  return someOfGhostsOk(G,{...law,some:fresh,holds:substC(law.holds,{vars:rename,maps:{},flags:{}})},plain,freshSub)
}

// `body` is exactly the retained emitter's output; `publicBridge` contains only
// ordinary-law specializations. Both must be compiled together by Lean.
export function exportWitnessSource(bundle:NativeBundle,id:string): {
  status:'EMITTED_NOT_CHECKED', body:string, publicBridge:string,
  sourceTheorems:SourceTheorem[], publicLawIndices:number[]
} {
  if(bundle.route !== 'witness' || bundle.verdict.proven !== true || bundle.verdict.checked !== true)
    throw Error('expected a checked witness capsule')
  let node:ProofOutputNode = bundle.proof
  const visited = new Set<ProofOutputNode>()
  let sk:Skolem|undefined
  let witness: {original:Machine,laws:Law[],machine:Machine,plain:Law[],ghosts:string[]}|undefined
  while(node.kind === 'derived') {
    if(visited.has(node)) throw Error('cyclic witness provenance')
    visited.add(node)
    if(node.parents.length !== 1 || !node.parents[0]) throw Error('witness needs a unique parent path')
    const context = node.context as {kind?:unknown} | null
    if(context?.kind === 'skolem') {
      if(sk) throw Error('multiple skolem contexts')
      sk = context as Skolem
    } else if(context?.kind === 'witness') {
      if(witness) throw Error('multiple witness contexts')
      witness = context as unknown as NonNullable<typeof witness>
    } else if(context?.kind !== 'projection' || Object.keys(context).length!==1) throw Error('unsupported witness derivation context')
    node = node.parents[0]
  }
  if(node.kind !== 'usual' || (!!sk === !!witness)) throw Error('expected one witness context and a usual producer')
  if(witness) {
    const w = witness
    if(!Array.isArray(w.ghosts) || !Array.isArray(w.plain) || !Array.isArray(w.laws) ||
       !isDeepStrictEqual(w.machine,node.machine) || !isDeepStrictEqual(w.plain,node.laws)) throw Error('witness producer mismatch')
    const vars:Ghosted['vars'] = Object.create(null), state=w.machine.step.state??{}
    for(const name of w.ghosts) {
      if(Object.hasOwn(vars,name) || !Object.hasOwn(w.machine.state,name) || !Object.hasOwn(state,name)) throw Error('invalid captured scalar ghost')
      vars[name] = {start:w.machine.state[name]!,step:state[name]!}
    }
    const maps:Ghosted['maps'] = Object.create(null)
    for(const [name,start] of Object.entries(w.machine.maps ?? {})) {
      if(Object.hasOwn(w.original.maps ?? {},name)) continue
      const write = w.machine.step.maps?.[name]
      if(!Number.isSafeInteger(start) || start < 0 || !write) throw Error('invalid captured ghost map')
      maps[name] = {start,write}
    }
    const G:Ghosted = {orig:w.original,vars,maps}
    const plains:Skolem['plains'] = Object.create(null)
    for(const law of bundle.original.laws) {
      const i = w.laws.findIndex(l => l.name === law.name)
      if(i < 0) throw Error('public law absent from witness context')
      if(!law.some?.length) continue
      const matching = w.plain.filter(l => l.name === law.name)
      if(matching.length !== 1) throw Error('ambiguous captured witness plain')
      const plain = matching[0]!, ex = plain.ex
      if(!plain || !ex || !isDeepStrictEqual(ex.body,law.holds) || !isDeepStrictEqual(ex.vars,law.some)) throw Error('unsupported or renamed captured witness')
      const sub = ex.sub ?? (ex.ghost ? Object.fromEntries(ex.vars.map(name => [name,{op:'var' as const,name}])) :
        ex.map && ex.vars.length === 1 ? {[ex.vars[0]!]:{op:'get' as const,map:ex.map.name,key:ex.map.at}} : undefined)
      if(!sub) throw Error('missing captured witness substitution')
      plains[law.name] = {plain,sub}
    }
    sk = {kind:'skolem',original:w.original,laws:w.laws,G,plains,family:w.plain}
  }
  if(!sk) throw Error('missing witness context')
  const {G,original,laws:capturedLaws,plains,family} = sk
  const laws = bundle.original.laws
  for(const law of laws) {
    const matches = capturedLaws.filter(l => l.name === law.name)
    if(matches.length !== 1) throw Error('ambiguous or absent captured public law')
    const {witness:_advisory,...capturedPublic} = matches[0]!
    if(!isDeepStrictEqual(capturedPublic,law)) throw Error('captured public law differs from original')
  }
  if(!laws.length || laws.some(l=>l.stated!==undefined||l.ex!==undefined||l.finite!==undefined||l.witness!==undefined||(l.some!==undefined&&!l.some.length)))
    throw Error('unsupported public witness law semantics')
  if(Object.keys(original.counts??{}).length||Object.keys(node.machine.counts??{}).length)
    throw Error('counted source requires its own semantic bridge')
  if(!G || !plains || !Array.isArray(laws) || !Array.isArray(family) ||
     !isDeepStrictEqual(original,G.orig) || !isDeepStrictEqual(original,bundle.original.machine) ||
     !Array.isArray(capturedLaws)) throw Error('skolem public input mismatch')
  // Empty optional map records have the same machine semantics as absent ones.
  const normalize = (m:Machine):Machine => ({...m,maps:m.maps ?? {},step:{...m.step,maps:m.step.maps ?? {}}})
  if(!isDeepStrictEqual(normalize(node.machine),normalize(ghostedMachine(G))) || !isDeepStrictEqual(node.laws,family))
    throw Error('skolem producer family mismatch')
  if(!checkLaws(node.machine,node.laws,node.proof)) throw Error('captured usual family does not check')
  const names = new Set<string>()
  for(const l of family) { if(names.has(l.name)) throw Error('duplicate family law name'); names.add(l.name) }
  const publicNames = new Set<string>(), ghostSubst:{law:string,body:Law['holds'],sub:Record<string,E>,boundGhosts?:boolean}[] = []
  const publicLawIndices:number[] = [], sourceTheorems:SourceTheorem[] = [], free:string[] = []
  let publicBridge = ''
  const mem = (i:number):string => i === 0 ? 'List.mem_cons_self' : `List.mem_cons_of_mem _ (${mem(i-1)})`
  for(const [publicIndex,law] of laws.entries()) {
    if(publicNames.has(law.name)) throw Error('duplicate public law name')
    publicNames.add(law.name)
    if(law.some?.length) {
      const q = Object.hasOwn(plains,law.name) ? plains[law.name] : undefined
      if(!q || !family.includes(q.plain) || !boundSourceSubstitutionOk(G,law,q.plain,q.sub)) throw Error('invalid captured skolem plain')
      const index = family.indexOf(q.plain), j = ghostSubst.length
      ghostSubst.push({law:q.plain.name,body:law.holds,sub:q.sub,boundGhosts:true})
      free.push(...law.some)
      publicLawIndices.push(index)
      sourceTheorems.push({publicIndex,familyIndex:index,name:`${id}_ex${j}`,type:'exists'})
    } else {
      const index = family.findIndex(l => l.name === law.name)
      if(index < 0 || !isDeepStrictEqual(family[index],law)) throw Error('ordinary public law missing unchanged')
      publicLawIndices.push(index)
      const name = `${id}_public${publicIndex}`
      sourceTheorems.push({publicIndex,familyIndex:index,name,type:'ordinary'})
      publicBridge += `\ntheorem ${name} : ∀ ρ M, SReach ${id}_gm.orig ρ M → ${id}_e${index}.Holds ρ M := by\n  intro ρ M h\n  exact ${id}_orig_laws ρ M h ${id}_e${index} (${mem(index)}) (by decide +kernel) (by decide +kernel)\n`
    }
  }
  if(!ghostSubst.length) throw Error('no existential public law')
  const body = retainedSMachineToLean(id,node.machine,node.laws,node.proof,{ghosted:G,ghostSubst,free:[...new Set(free)]})
  return {status:'EMITTED_NOT_CHECKED',body,publicBridge,sourceTheorems,publicLawIndices}
}
