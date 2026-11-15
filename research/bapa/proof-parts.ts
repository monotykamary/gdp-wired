// Source generator for the retained counted family. Run ONLY in the separately
// authorized recheck worker after exact term-prelude replay. No search fallback.
import {createHash} from 'node:crypto'
import {retainedCMachineToLean} from '../../lean-kernel/emit.ts'
import type {FamilyBundle} from './proof-capture.ts'
import {makeFrontier,verifyFrontier,structuralWeight,type Frontier} from './proof-frontier.ts'
export type PartOptions={weightLimit:bigint,maxOutputBytes:number,maxFiles:number,heartbeats:number,recursionDepth:number}
export type GeneratedPart={module:string,role:string,text:string,sha256:string}
export type CountedParts={status:'EMITTED_NOT_CHECKED',files:GeneratedPart[],frontiers:{law:string,phase:'start'|'step',frontier:Frontier}[],familySize:number,primaryObligations:number,finalModule:string}
const sha=(s:string)=>createHash('sha256').update(s).digest('hex')
const list=(xs:string[])=>'['+xs.join(', ')+']'
const address=(s:string)=>list([...s].map(x=>x==='1'?'true':'false'))
// Lean constructor data only; brackets/tuples nested inside each entry must not
// be mistaken for the outer list. The emitter emits no string literals here.
export function splitEntryData(text:string):string[] {
 const source=text.trim()
 if(!source.startsWith('[')||!source.endsWith(']'))throw Error('expected emitted entry list')
 const values:string[]=[],stack:string[]=[];let start=1
 const pairs:Record<string,string>={')':'(',']':'[','}':'{','⟩':'⟨'}
 for(let i=1;i<source.length-1;i++){
  const c=source[i]!
  if(c==='"'||c==='`')throw Error('unexpected literal in emitted entry data')
  if('([{⟨'.includes(c))stack.push(c)
  else if(Object.hasOwn(pairs,c)){if(stack.pop()!==pairs[c])throw Error('unbalanced entry data')}
  else if(c===','&&!stack.length){const item=source.slice(start,i).trim();if(!item)throw Error('empty entry');values.push(item);start=i+1}
 }
 if(stack.length)throw Error('unclosed entry data')
 const last=source.slice(start,-1).trim();if(last)values.push(last)
 return values
}
export function emitCountedParts(id:string,bundle:FamilyBundle,options:PartOptions):CountedParts {
 if(!/^[A-Za-z][A-Za-z0-9_]*$/.test(id)||id.length>80)throw Error('unsafe Lean identifier')
 for(const value of [options.maxOutputBytes,options.maxFiles,options.heartbeats,options.recursionDepth])if(!Number.isSafeInteger(value)||value<1)throw Error('finite positive generator limits required')
 const {machine,laws,proof}=bundle.final
 if(!laws.length)throw Error('empty retained family')
 const text=retainedCMachineToLean(id,machine,laws,proof)
 const match=new RegExp(`\\n(?:noncomputable )?def ${id}_proof : List (CEntryF|CEntry) := `).exec(text),check=text.indexOf(`\ntheorem ${id}_check :`)
 if(!match||check<0)throw Error('unexpected retained family emission layout')
 const begin=match.index+match[0].length,entries=splitEntryData(text.slice(begin,check))
 if(entries.length!==laws.length)throw Error('family entry count mismatch')
 const entryType=match[1]!,defsModule=`${id}_Defs`,family=`${id}_family`,es=`(${family}.map (·.e))`,decls=`${id}_decls`
 const checked=text.includes(`def ${id}_checkedMachine :`)?`${id}_checkedMachine`:`${id}_machine`
 const files:GeneratedPart[]=[],frontiers:CountedParts['frontiers']=[];let bytes=0
 const add=(module:string,role:string,imports:string[],body:string)=>{
  if(files.some(f=>f.module===module))throw Error('duplicate generated module')
  const source=imports.map(m=>`import ${m}`).join('\n')+`\nopen Kern Cert\nset_option maxHeartbeats ${options.heartbeats}\nset_option maxRecDepth ${options.recursionDepth}\n`+body+'\n'
  bytes+=Buffer.byteLength(source)
  if(bytes>options.maxOutputBytes||files.length>=options.maxFiles)throw Error('generated source limit exceeded')
  files.push({module,role,text:source,sha256:sha(source)})
 }
 const names=entries.map((_,i)=>`${id}_entry${i}`)
 let defs=text.slice(0,match.index)+'\n'
 defs+=entries.map((entry,i)=>`noncomputable def ${names[i]}_raw : ${entryType} := ${entry}\nnoncomputable def ${names[i]} : CEntryF := ${entryType==='CEntry'?`${names[i]}_raw.toF`:`${names[i]}_raw`}`).join('\n')
 defs+=`\nnoncomputable def ${family} : List CEntryF := ${list(names)}\n`
 add(defsModule,'definitions',['QAlpha','FamilyParts'],defs)
 const globalModule=`${id}_Global`
 add(globalModule,'global-conditions',[defsModule],`theorem ${id}_global : cGlobalOkF ${checked} ${decls} ${es} = true := by decide +kernel\n#print axioms ${id}_global`)
 const entryModules:string[]=[]
 for(let i=0;i<laws.length;i++){
  const entry=names[i]!,law=laws[i]!,checks:string[]=[],checkModules:string[]=[]
  for(const phase of ['start','step'] as const){
   const cert=proof.certs[`${law.name} @${phase}`]
   if(!cert)throw Error('missing primary certificate')
   const base=`${id}_e${i}_${phase}`,certificate=`${entry}.${phase}`,aux=`${entry}.${phase}Aux`
   const ds=`(${phase==='start'?'cStartDecls':'cStepDecls'} ${checked} ${decls})`
   const hyps=phase==='start'?`(cStartGoal ${checked} ${decls} ${entry}.e)`:`(cStepGoal ${checked} ${decls} ${es} ${entry}.e)`
   const context={machine,laws,instances:proof.instances,reads:cert.reads,insts:cert.insts,picks:cert.picks,lemmas:cert.lemmas,frames:cert.frames,monos:cert.monos,lins:cert.lins}
   const frontier=makeFrontier(cert.tree,options.weightLimit,structuralWeight(context));verifyFrontier(cert.tree,frontier)
   frontiers.push({law:law.name,phase,frontier})
   const at=(a:string)=>`FamilyParts.mcfWith ${ds} ${certificate} (fun g cs => FamilyParts.checkAt g.tab g.hyps ${certificate}.lemmas ${aux}.frames ${aux}.monos ${aux}.lins [] ${certificate}.tree ${address(a)})`
   const ready=new Map<string,{module:string,theorem:string}>()
   for(const piece of frontier.pieces){const module=`${base}_p${piece.address?sha(piece.address).slice(0,20):'root'}`,theorem=`${module}_check`;add(module,'tree-piece',[defsModule],`theorem ${theorem} : ${at(piece.address)} = true := by decide +kernel\n#print axioms ${theorem}`);ready.set(piece.address,{module,theorem})}
   const ancestors=new Set<string>();for(const p of frontier.pieces)for(let n=0;n<p.address.length;n++)ancestors.add(p.address.slice(0,n))
   for(const a of [...ancestors].sort((x,y)=>y.length-x.length||(x<y?-1:1))){
    const yes=ready.get(a+'1'),no=ready.get(a+'0');if(!yes||!no)throw Error('incomplete canonical assembly frontier')
    const module=`${base}_a${a?sha(a).slice(0,20):'root'}`,theorem=`${module}_check`
    add(module,'tree-assembly',[defsModule,yes.module,no.module],`theorem ${theorem} : ${at(a)} = true := by\n  exact FamilyParts.mcfWith_map2 ${ds} ${certificate} _ _ _\n    (by intro g cs h1 h0; exact FamilyParts.checkAt_split g.tab g.hyps ${certificate}.lemmas ${aux}.frames ${aux}.monos ${aux}.lins ${address(a)} [] ${certificate}.tree h1 h0)\n    ${yes.theorem} ${no.theorem}\n#print axioms ${theorem}`)
    ready.set(a,{module,theorem})
   }
   const root=ready.get('');if(!root)throw Error('missing root assembly')
   const preModule=`${base}_Pre`,side=`FamilyParts.mcfWith ${ds} ${certificate} (fun g cs => FamilyParts.goalPre ${certificate}.lemmas ${aux}.monos ${aux}.lins g cs && ${aux}.frames.all (frameOk g.tab cs))`
   add(preModule,'obligation-side-conditions',[defsModule],`theorem ${base}_pre : FamilyParts.mcfPre ${hyps} ${ds} ${certificate} = true := by decide +kernel\ntheorem ${base}_side : ${side} = true := by decide +kernel\n#print axioms ${base}_pre\n#print axioms ${base}_side`)
   const module=`${base}_Complete`,theorem=`${base}_check`
   add(module,'obligation-assembly',[defsModule,preModule,root.module],`theorem ${theorem} : checkMCF ${hyps} ${ds} ${certificate} ${aux}.frames ${aux}.monos ${aux}.lins = true := by\n  apply FamilyParts.checkMCF_of_parts _ _ _ _ _ _ ${base}_pre\n  exact FamilyParts.mcfWith_map2 ${ds} ${certificate} _ _ _\n    (by intro g cs hs ht; simp only [Bool.and_eq_true] at hs; exact FamilyParts.goal_of_parts g cs ${certificate}.tree ${certificate}.lemmas ${aux}.frames ${aux}.monos ${aux}.lins hs.1 hs.2 ht)\n    ${base}_side ${root.theorem}\n#print axioms ${theorem}`)
   checks.push(theorem);checkModules.push(module)
  }
  const module=`${id}_e${i}_Complete`
  add(module,'entry-assembly',[defsModule,...checkModules],`theorem ${id}_e${i}_check : cEntryCheckF ${checked} ${decls} ${es} ${entry} = true := by\n  exact FamilyParts.entry_of_both _ _ _ _ (by decide +kernel) ${checks[0]} ${checks[1]}\n#print axioms ${id}_e${i}_check`)
  entryModules.push(module)
 }
 const finalModule=`${id}_Complete`,branches=names.map((_,i)=>`  · exact ${id}_e${i}_check`).join('\n')
 const transport=checked===`${id}_machine`?`cmachineF_sound ${id}_machine ${decls} ${family} ${id}_check`:`QAlpha.cmachineF_sound ${id}_machine ${id}_renames ${decls} ${family} (by decide +kernel) ${id}_check`
 add(finalModule,'family-assembly',[defsModule,globalModule,...entryModules],`theorem ${id}_check : checkCMachineF ${checked} ${decls} ${family} = true := by\n  apply checkCMachineF_of_parts _ _ _ ${id}_global\n  intro ce hce\n  simp only [${family}, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hce\n  rcases hce with ${names.map(()=> 'rfl').join(' | ')}\n${branches}\ntheorem ${id}_laws : ∀ ρ M, CReach ${id}_machine ${decls} ρ M → ∀ ce ∈ ${family}, ce.e.Holds ρ (withCnt ${decls} ρ M) :=\n  ${transport}\n#print axioms ${id}_check\n#print axioms ${id}_laws`)
 return {status:'EMITTED_NOT_CHECKED',files,frontiers,familySize:laws.length,primaryObligations:2*laws.length,finalModule}
}
