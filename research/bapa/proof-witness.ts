// Output-only projection of the captured skolem producer. This is not a Lean check.
import {isDeepStrictEqual} from 'node:util'
import {proposeWitnessAlpha,type WitnessAlpha} from './witness-alpha.ts'
import type {E, Law, Machine} from '../../core/machine.ts'
import type {ProofOutputNode} from '../../core/proof-output.ts'
import {checkLaws, ghostedMachine, someOfGhostsOk, substC, type Ghosted} from '../../kernel/kernel.ts'
import {retainedSMachineToLean} from '../../lean-kernel/emit.ts'
import type {NativeBundle} from './proof-capture.ts'

type Skolem = {kind:'skolem', original:Machine, laws:Law[], G:Ghosted,
  plains:Record<string,{plain:Law,sub:Record<string,E>}>, family:Law[]}
type SourceTheorem = {publicIndex:number, familyIndex:number|null, name:string, type:'exists'|'ordinary'}
type Witness = {kind:'witness',original:Machine,laws:Law[],machine:Machine,plain:Law[],ghosts:string[]}
type WitnessContext = Skolem | Witness
type Usual = Extract<ProofOutputNode,{kind:'usual'}>
export type WitnessPathReceipt = {path:number[],witnessPath:number[],familyTheorem:string,sourceTheorems:string[],publicLawIndices:number[]}
export type WitnessAlphaReceipt = WitnessAlpha & {id:string,theorems:string[]}
type WitnessExport = {status:'EMITTED_NOT_CHECKED',body:string,publicBridge:string,sourceTheorems:SourceTheorem[],publicLawIndices:number[],parentPaths?:WitnessPathReceipt[],alphaTransports?:WitnessAlphaReceipt[]}

type ParentPath = {path:number[],leaf:Usual,witnesses:{path:number[],context:WitnessContext}[],inferences:{path:number[],original:Machine,laws:Law[]}[]}
function parentPaths(root:ProofOutputNode):ParentPath[] {
  const result:ParentPath[] = [], active = new Set<ProofOutputNode>()
  const visit = (node:ProofOutputNode|undefined,path:number[],witnesses:ParentPath['witnesses'],inferences:ParentPath['inferences']):void => {
    if(!node || active.has(node)) throw Error('missing or cyclic witness provenance')
    if(path.length > 256 || result.length >= 128) throw Error('witness parent path limit')
    if(node.kind === 'usual') { result.push({path,leaf:node,witnesses,inferences}); return }
    if(node.kind !== 'derived') throw Error('witness path needs a usual producer')
    if(!Array.isArray(node.parents) || !node.parents.length || new Set(node.parents).size !== node.parents.length)
      throw Error('empty or duplicate witness parent path')
    const c=node.context as Record<string,unknown>|null
    if(c?.kind === 'witness' || c?.kind === 'skolem') witnesses=[...witnesses,{path,context:c as WitnessContext}]
    else if(c?.kind === 'inference' && Object.keys(c).sort().join(',') === 'kind,laws,original' && Array.isArray(c.laws))
      inferences=[...inferences,{path,original:c.original as Machine,laws:c.laws as Law[]}]
    else if(c?.kind !== 'projection' || Object.keys(c).length !== 1) throw Error('unsupported witness derivation context')
    active.add(node)
    node.parents.forEach((p,i)=>visit(p,[...path,i],witnesses,inferences))
    active.delete(node)
  }
  visit(root,[],[],[])
  return result
}

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
function exportWitnessLeaf(bundle:NativeBundle,publicId:string,node:Usual,context:WitnessContext):WitnessExport {
  let sk:Skolem|undefined = context.kind === 'skolem' ? context : undefined
  const witness = context.kind === 'witness' ? context : undefined
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
  const {G,original,laws:capturedLaws,plains,family:declaredFamily} = sk
  const family = node.laws
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
  if(!G || !plains || !Array.isArray(laws) || !Array.isArray(declaredFamily) ||
     !isDeepStrictEqual(original,G.orig) ||
     !Array.isArray(capturedLaws)) throw Error('skolem public input mismatch')
  const alpha=proposeWitnessAlpha(bundle.original.machine,original)
  const id=alpha ? publicId+'_producer' : publicId
  // Empty optional map records have the same machine semantics as absent ones.
  const normalize = (m:Machine):Machine => ({...m,maps:m.maps ?? {},step:{...m.step,maps:m.step.maps ?? {}}})
  if(!isDeepStrictEqual(normalize(node.machine),normalize(ghostedMachine(G))) ||
     declaredFamily.some(l => family.filter(f => isDeepStrictEqual(f,l)).length !== 1))
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
      if(!q || !declaredFamily.includes(q.plain) || !boundSourceSubstitutionOk(G,law,q.plain,q.sub)) throw Error('invalid captured skolem plain')
      const index = family.findIndex(l => isDeepStrictEqual(l,q.plain)), j = ghostSubst.length
      if(index < 0) throw Error('captured skolem plain absent from complete family')
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
  const alphaTransports:WitnessAlphaReceipt[]=[]
  if(alpha)free.push(...alpha.renames.flatMap(r=>[r.old,r.fresh]),...alpha.rows.flatMap(r=>[r.old,r.fresh]))
  const body = retainedSMachineToLean(id,node.machine,node.laws,node.proof,{ghosted:G,ghostSubst,free:[...new Set(free)],...(alpha?{after:(ix,mx,lit,c)=>{
    const renames=alpha.renames.map(r=>`⟨${ix('?'+r.flag)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`).join(', ')
    const rows=alpha.rows.map(r=>`⟨${mx(r.map)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`).join(', ')
    const claims=sourceTheorems.map(t=>{
      const law=laws[t.publicIndex]!,index=t.familyIndex!,name=t.name.replace(id+'_',publicId+'_')
      const conclusion=t.type==='exists'?`ExHolds (${c(law.holds)}) ${id}_e${index}.law.key [${law.some!.map(ix).join(', ')}] M ${id}_e${index}.keys2 ρ`:`${id}_e${index}.Holds ρ M`
      const apply=t.type==='exists'?`${t.name} ρ M hp`:`${id}_orig_laws ρ M hp ${id}_e${index} (${mem(index)}) (by decide +kernel) (by decide +kernel)`
      return `theorem ${name} : ∀ ρ M, SReach ${publicId}_source ρ M → ${conclusion} := by\n  intro ρ M hr\n  have hp := ${publicId}_source_reach ρ M hr\n  exact ${apply}`
    }).join('\n')
    return `def ${publicId}_source : SMachine := ${lit(bundle.original.machine)}
def ${publicId}_source_renames : List Kern.QAlpha.Rename := [${renames}]
def ${publicId}_source_row_renames : List Kern.RowAlpha.Rename := [${rows}]
theorem ${publicId}_alpha_valid : Kern.QAlpha.validAll ${publicId}_source ${publicId}_source_renames = true := by decide +kernel
theorem ${publicId}_row_valid : Kern.RowAlpha.validAll (Kern.QAlpha.renameAll ${publicId}_source ${publicId}_source_renames) ${publicId}_source_row_renames = true := by decide +kernel
theorem ${publicId}_alpha_result : Kern.RowAlpha.renameAll (Kern.QAlpha.renameAll ${publicId}_source ${publicId}_source_renames) ${publicId}_source_row_renames = ${id}_gm.orig := by rfl
theorem ${publicId}_source_reach : ∀ ρ M, SReach ${publicId}_source ρ M → SReach ${id}_gm.orig ρ M := by
  intro ρ M hr
  rw [← ${publicId}_alpha_result]
  have q := Kern.QAlpha.renameAll_equiv ${publicId}_source ${publicId}_source_renames ${publicId}_alpha_valid
  have r := Kern.RowAlpha.renameAll_equiv (Kern.QAlpha.renameAll ${publicId}_source ${publicId}_source_renames) ${publicId}_source_row_renames ${publicId}_row_valid
  exact r.symm.sreach_imp (q.symm.sreach_imp hr)
theorem ${publicId}_laws : ∀ ρ M, SReach ${id}_machine ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M := ${id}_laws
${claims}`
  }}:{})})
  if(alpha){
    alphaTransports.push({...alpha,id:publicId,theorems:['_alpha_valid','_row_valid','_alpha_result','_source_reach'].map(s=>publicId+s)})
    for(const t of sourceTheorems)t.name=t.name.replace(id+'_',publicId+'_')
    publicBridge=''
  }
  return {status:'EMITTED_NOT_CHECKED',body,publicBridge,sourceTheorems,publicLawIndices,...(alpha?{alphaTransports}:{})}
}

// Every provenance path is an obligation. A context-free inference branch may
// reuse the UNIQUE retained witness context, but must independently prove its
// exact source substitution with its own complete family. No leaf is selected.
export function exportWitnessSource(bundle:NativeBundle,id:string):WitnessExport {
  if(!/^[A-Za-z][A-Za-z0-9_]*$/.test(id)) throw Error('unsafe witness identifier')
  if(bundle.route !== 'witness' || bundle.verdict.proven !== true || bundle.verdict.checked !== true)
    throw Error('expected a checked witness capsule')
  const paths=parentPaths(bundle.proof)
  const contexts=new Map<WitnessContext,number[]>()
  for(const p of paths) for(const w of p.witnesses) contexts.set(w.context,w.path)
  const receipts:WitnessPathReceipt[]=[], exports:WitnessExport[]=[]
  for(const [i,p] of paths.entries()) {
    if(p.witnesses.length > 1) throw Error('multiple witness contexts on parent path')
    const own=p.witnesses[0]
    if(!own && contexts.size !== 1) throw Error('parent path has no unique compatible witness context')
    const context=own?.context ?? contexts.keys().next().value!
    for(const inf of p.inferences) {
      // An inference ABOVE this path's witness projects the original source
      // claims; below it (or on a sibling-only path) it describes the producer.
      if(own && inf.path.length < own.path.length) {
        try {
          const proposed=proposeWitnessAlpha(bundle.original.machine,inf.original)
          if(proposed && !isDeepStrictEqual(inf.original,context.original)) throw Error('different witness source')
        } catch { throw Error('source inference original differs from source machine beyond checked alpha transport') }
        if(new Set(inf.laws.map(l=>l.name)).size !== inf.laws.length || bundle.original.laws.some(l=>
          inf.laws.filter(f=>isDeepStrictEqual(f,l)).length !== 1))
          throw Error('source inference public laws missing or changed')
        const publicNames = new Set(bundle.original.laws.map(l=>l.name))
        if(inf.laws.some(l=>!publicNames.has(l.name) && p.leaf.laws.filter(f=>isDeepStrictEqual(f,l)).length !== 1))
          throw Error('source inference extra law absent from complete witness family')
        // No law is added to assumptions here. exportWitnessLeaf checks and
        // emits the complete family, including every retained candidate seed.
      } else if(!isDeepStrictEqual(inf.original,p.leaf.machine) || inf.laws.some(l=>p.leaf.laws.filter(f=>isDeepStrictEqual(f,l)).length !== 1)) {
        throw Error('inference parent differs from complete witness producer')
      }
    }
    const prefix=paths.length === 1 ? id : `${id}_path${i}`
    const emitted=exportWitnessLeaf(bundle,prefix,p.leaf,context)
    exports.push(emitted)
    receipts.push({path:p.path,witnessPath:own?.path ?? contexts.get(context)!,familyTheorem:prefix+'_laws',sourceTheorems:emitted.sourceTheorems.map(t=>t.name),publicLawIndices:emitted.publicLawIndices})
  }
  if(exports.length === 1) return exports[0]!
  const conjunction=(names:string[]):string => names.length === 1 ? `(@${names[0]})` : `And.intro (@${names[0]}) (${conjunction(names.slice(1))})`
  const sourceTheorems=exports[0]!.sourceTheorems.map(t=>({...t,familyIndex:null,name:t.name.replace(`${id}_path0_`,`${id}_`)}))
  const joinTheorem=(name:string,names:string[]):string => {
    const proof=conjunction(names)
    return `theorem ${name} : ${id}_claim (${proof}) := ${proof}`
  }
  // The reducible claim helper obtains the exact conjunction type from all
  // checked path proofs. It introduces no assumption or new proof principle.
  const joined=[`def ${id}_claim {p : Prop} (_proof : p) : Prop := p`,
    joinTheorem(id+'_laws',receipts.map(p=>p.familyTheorem)),
    ...sourceTheorems.map((t,j)=>joinTheorem(t.name,exports.map(e=>e.sourceTheorems[j]!.name)))].join('\n')
  return {status:'EMITTED_NOT_CHECKED',body:exports.map(e=>e.body+'\n'+e.publicBridge).join('\n'),publicBridge:joined,sourceTheorems,publicLawIndices:[],parentPaths:receipts,alphaTransports:exports.flatMap(e=>e.alphaTransports??[])}
}
