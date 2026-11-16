import {expect,test} from 'bun:test'
import {checkLaws,checkCountedLaws} from '../../kernel/kernel.ts'
import {retainedCMachineToLean,retainedSMachineToLean} from '../emit.ts'
import {syntheticPlain,syntheticCounted} from './proof-synthetic.ts'
import {emitCountedParts,splitEntryData} from './proof-parts.ts'
import {makeFrontier,verifyFrontier,structuralWeight} from './proof-frontier.ts'
import type {Tree} from '../../kernel/kernel.ts'
import {mkdirSync,writeFileSync} from 'node:fs'
import {leanSource} from './project.ts'
import {join} from 'node:path'
import {leanProject} from '../emit.ts'
import type {FamilyBundle} from './proof-capture.ts'
import type {CountCert} from '../../kernel/kernel.ts'
test('retained usual family emits only its supplied, checked proof',()=>{
 const p=syntheticPlain();expect(checkLaws(p.machine,p.laws,p.proof)).toBe(true)
 const text=retainedSMachineToLean('control',p.machine,p.laws,p.proof);expect(text).toContain('decide +kernel');expect(text).not.toContain('native_decide')
 expect(()=>retainedSMachineToLean('bad',p.machine,p.laws,{instances:{},trees:{}})).toThrow('does not check')
})
test('no-aux and framed counted families keep distinct reviewed check paths',()=>{
 for(const framed of [false,true]){const {final:f}=syntheticCounted(framed);expect(checkCountedLaws(f.machine,f.laws,f.proof)).toBe(true);const text=retainedCMachineToLean('control',f.machine,f.laws,f.proof);expect(text).toContain(framed?'List CEntryF':'List CEntry');expect(text).toContain('decide +kernel')}
 const {final:f}=syntheticCounted(true),cert=f.proof.certs['true law @step']!;cert.frames![0]!.post='absent'
 expect(()=>retainedCMachineToLean('bad',f.machine,f.laws,f.proof)).toThrow('does not check')
})
test('weighted counted source joins both INIT and STEP child pieces into one complete family',()=>{
 const data=syntheticCounted(true),f=data.final,cert=f.proof.certs['true law @start']!
 const context={machine:f.machine,laws:f.laws,instances:f.proof.instances,reads:cert.reads,insts:cert.insts,picks:cert.picks,lemmas:cert.lemmas,frames:cert.frames,monos:cert.monos,lins:cert.lins}
 if(!('split'in cert.tree))throw Error('fixture split missing')
 const limit=structuralWeight(context)+structuralWeight(cert.tree.yes)+2n
 const out=emitCountedParts('control',data as FamilyBundle,{weightLimit:limit,maxOutputBytes:8*1024*1024,maxFiles:100,heartbeats:10000000,recursionDepth:10000})
 expect(out.primaryObligations).toBe(2);expect(out.frontiers.map(f=>f.phase)).toEqual(['start','step']);expect(out.frontiers.every(f=>f.frontier.pieces.length===2)).toBe(true)
 expect(out.files.filter(f=>f.role==='tree-piece')).toHaveLength(4);expect(out.files.filter(f=>f.role==='tree-assembly')).toHaveLength(2)
 const obligations=out.files.filter(f=>f.role==='obligation-assembly')
 expect(obligations).toHaveLength(2)
 expect(obligations.every(f=>f.text.includes('simp only [Bool.and_eq_true] at hs'))).toBe(true)
 expect(obligations.some(f=>f.text.includes('Bool.and_eq_true.mp'))).toBe(false)
 const final=out.files.find(f=>f.role==='family-assembly')!.text;expect(final).toContain('List.not_mem_nil, or_false');expect(final).toContain('checkCMachineF_of_parts');expect(final).toContain('cmachineF_sound');expect(final).not.toContain('sorry')
})

// Inspect the generated constructor data, not just a nonempty output file.
const tupleFields=(source:string)=>{const t=source.trim();if(!t.startsWith('⟨')||!t.endsWith('⟩'))throw Error('expected Lean tuple');return splitEntryData('['+t.slice(1,-1)+']')}
function twoChildLimit(data:ReturnType<typeof syntheticCounted>):bigint {
 const f=data.final
 return Object.values(f.proof.certs).reduce((max,cert)=>{
  if(!('split'in cert.tree))throw Error('fixture split missing')
  const context={machine:f.machine,laws:f.laws,instances:f.proof.instances,reads:cert.reads,insts:cert.insts,picks:cert.picks,lemmas:cert.lemmas,frames:cert.frames,monos:cert.monos,lins:cert.lins}
  const cost=structuralWeight(context)+(structuralWeight(cert.tree.yes)>structuralWeight(cert.tree.no)?structuralWeight(cert.tree.yes):structuralWeight(cert.tree.no))+2n
  return cost>max?cost:max
 },0n)
}
const options=(weightLimit:bigint)=>({weightLimit,maxOutputBytes:8*1024*1024,maxFiles:160,heartbeats:10000000,recursionDepth:10000})
for(const mode of ['mono','lin','both'] as const)test(`${mode}: full family retains each INIT/STEP auxiliary and joins both children`,()=>{
 const data=syntheticCounted(true,mode),f=data.final
 expect(f.laws).toHaveLength(2);expect(checkCountedLaws(f.machine,f.laws,f.proof)).toBe(true)
 const out=emitCountedParts('control',data as FamilyBundle,options(twoChildLimit(data)))
 expect(out.familySize).toBe(2);expect(out.primaryObligations).toBe(4)
 expect(out.frontiers.map(x=>[x.law,x.phase])).toEqual(f.laws.flatMap(l=>[[l.name,'start'],[l.name,'step']]))
 expect(out.frontiers.every(x=>x.frontier.pieces.map(p=>p.address).join(',')==='1,0')).toBe(true)
 expect(out.files.filter(x=>x.role==='tree-piece')).toHaveLength(8);expect(out.files.filter(x=>x.role==='tree-assembly')).toHaveLength(4)
 const defs=out.files.find(x=>x.role==='definitions')!.text
 expect(defs).toContain('noncomputable def control_family : List CEntryF := [control_entry0, control_entry1]')
 for(const [index,law]of f.laws.entries()){
  const begin=`noncomputable def control_entry${index}_raw : CEntryF := `,end=`\nnoncomputable def control_entry${index} : CEntryF := `
  const start=defs.indexOf(begin);expect(start).toBeGreaterThanOrEqual(0)
  const fields=tupleFields(defs.slice(start+begin.length,defs.indexOf(end,start)))
  expect(fields).toHaveLength(5)
  for(const [phase,at]of [['start',3],['step',4]] as const){
   const expected=f.proof.certs[`${law.name} @${phase}`]!,aux=tupleFields(fields[at]!)
   expect(aux).toHaveLength(3)
   expect(aux.map(x=>splitEntryData(x).length)).toEqual([expected.frames!.length,expected.monos!.length,expected.lins!.length])
   const complete=out.files.find(x=>x.module===`control_e${index}_${phase}_Complete`)!.text
   expect(complete).toContain(`control_entry${index}.${phase}Aux.monos`);expect(complete).toContain(`control_entry${index}.${phase}Aux.lins`)
  }
 }
 const final=out.files.find(x=>x.role==='family-assembly')!.text
 expect(final).toContain('import control_e0_Complete');expect(final).toContain('import control_e1_Complete')
 expect(final).toContain('checkCMachineF_of_parts');expect(final).toContain('cmachineF_sound');expect(final).not.toContain('native_decide')
})
for(const mode of ['mono','lin'] as const)for(const phase of ['start','step'] as const)for(const fault of ['reference','tree'] as const)
 test(`${mode}: corrupted ${phase} ${fault} in the second family entry is refused`,()=>{
  const data=syntheticCounted(true,mode),f=data.final,cert:CountCert=f.proof.certs[`other true law @${phase}`]!
  if(mode==='mono'){if(fault==='reference')cert.monos![0]!.post='absent';else cert.monos![0]!.tree={leaf:[]}}
  else {if(fault==='reference')cert.lins![0]!.pos[0]![1]='absent';else cert.lins![0]!.tree={leaf:[]}}
  expect(checkCountedLaws(f.machine,f.laws,f.proof)).toBe(false)
  expect(()=>retainedCMachineToLean('bad',f.machine,f.laws,f.proof)).toThrow('does not check')
  expect(()=>emitCountedParts('bad',data as FamilyBundle,options(1000000n))).toThrow('does not check')
 })

const leaf=():Tree=>({leaf:[]}),split=(yes:Tree,no:Tree):Tree=>({split:{},yes,no})
test('canonical actual-tree frontier stops at shallow real leaves',()=>{
 const tree=split(leaf(),split(leaf(),leaf())),max=structuralWeight(leaf())+5n
 const f=makeFrontier(tree,max,1n);expect(f.pieces.map(p=>p.address)).toEqual(['1','01','00']);expect(()=>verifyFrontier(tree,f)).not.toThrow()
})
test('duplicate, prefix, omitted, under-leaf and reordered addresses are refused',()=>{
 const tree=split(leaf(),split(leaf(),leaf())),f=makeFrontier(tree,structuralWeight(leaf())+5n,1n)
 const cases=[{...f,pieces:[...f.pieces,f.pieces[0]!]},{...f,pieces:f.pieces.slice(1)},{...f,pieces:f.pieces.map((p,i)=>i===0?{...p,address:'11'}:p)},{...f,pieces:[...f.pieces].reverse()},{...f,pieces:[{address:'',weight:'1'},...f.pieces]}]
 for(const bad of cases)expect(()=>verifyFrontier(tree,bad)).toThrow()
})
test('weight forgery and unnecessary subdivision are refused',()=>{
 const tree=split(leaf(),leaf()),f=makeFrontier(tree,1000000n,0n)
 expect(f.pieces.map(p=>p.address)).toEqual([''])
 expect(()=>verifyFrontier(tree,{...f,pieces:[{address:'',weight:'1'}]})).toThrow()
 expect(()=>verifyFrontier(tree,{...f,pieces:[{address:'1',weight:String(structuralWeight(leaf()))},{address:'0',weight:String(structuralWeight(leaf()))}]})).toThrow()
})
test('a leaf/context over the weight limit stops rather than resharding or dropping context',()=>{
 expect(()=>makeFrontier(leaf(),1n,1000n)).toThrow('oversized');expect(()=>makeFrontier(leaf(),0n,0n)).toThrow('positive')
})

// Optional, explicit synthetic-only Lean gate. The directory must not exist.
test('write tiny split Lean projects only when requested',()=>{
 const root=process.env.BAPA_SPLIT_TINY_DIR
 if(!root)return
 mkdirSync(root)
 const modes=['none','frame','mono','lin','both'] as const
 for(const [i,mode] of modes.entries()){
  const data=syntheticCounted(mode!=='none',mode==='frame'?'none':mode)
  const out=emitCountedParts(`tiny${i}`,data as FamilyBundle,options(twoChildLimit(data)))
  const dir=join(root,mode);mkdirSync(dir)
  // Request the current cut-aware library even for the cut-free control.
  const project=leanProject('noncomputable def __library_selector : List CEntryF := []')
  for(const [name,text] of Object.entries(project))if(name.endsWith('.lean')&&name!=='Proofs.lean'&&name!=='lakefile.lean')writeFileSync(join(dir,name),text,{flag:'wx'})
  writeFileSync(join(dir,'FamilyParts.lean'),leanSource('FamilyParts'),{flag:'wx'})
  for(const file of out.files)writeFileSync(join(dir,file.module+'.lean'),file.text,{flag:'wx'})
  writeFileSync(join(dir,'lean-toolchain'),'leanprover/lean4:v4.34.0\n',{flag:'wx'})
  const modules=[...Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='Proofs.lean'&&n!=='lakefile.lean').map(n=>n.slice(0,-5)),'FamilyParts',...out.files.map(f=>f.module)]
  writeFileSync(join(dir,'lakefile.lean'),`import Lake\nopen Lake DSL\npackage tiny\n@[default_target]\nlean_lib Tiny where\n  roots := #[${modules.map(n=>'`'+n).join(', ')}]\n`,{flag:'wx'})
  writeFileSync(join(dir,'EMITTED.json'),JSON.stringify({status:out.status,modules:out.files.map(f=>f.module),finalModule:out.finalModule,primaryObligations:out.primaryObligations})+'\n',{flag:'wx'})
 }
})
