import {describe,expect,test} from 'bun:test'
import {mkdtempSync,readFileSync,rmSync,symlinkSync,writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join,resolve} from 'node:path'
import {auditPaxosReplay,expectedReuse,verifyOriginalExports} from './paxos-release-audit.ts'
import {AXIOMS,CAPSULE,FAMILY,FRESH,SOURCE,SOURCE_AXIOMS,capsuleFiles,checkAxioms,checkedFile,hash,expectedAxioms,reachableModules,validateCoverage,type PaxosReplayReceipt} from './paxos-release.helpers.ts'
const root=process.cwd(),entries=Array.from({length:25},(_,i)=>i)
const obligations=entries.flatMap(law=>[{law,step:false},{law,step:true}])

describe('accepted Paxos release contracts',()=>{
 test('exact 25 entries and both 50 obligations; refusals are not searches',()=>{
  expect(()=>validateCoverage(entries,obligations)).not.toThrow()
  expect(()=>validateCoverage(entries.slice(1),obligations)).toThrow('incomplete entries')
  expect(()=>validateCoverage(entries,obligations.slice(1))).toThrow('incomplete obligations')
  expect(()=>validateCoverage(entries,[...obligations.slice(1),obligations[1]!])).toThrow('duplicate')
 })
 test('required names and exact ordered axiom lists, not allowlists/subsets',()=>{
  const log=`'${FAMILY}' depends on axioms: [propext, Quot.sound]\n'${SOURCE}' depends on axioms: [propext, Classical.choice, Quot.sound]\n`
  expect(checkAxioms(log,{[FAMILY]:AXIOMS,[SOURCE]:SOURCE_AXIOMS})).toEqual({[FAMILY]:AXIOMS,[SOURCE]:SOURCE_AXIOMS})
  for(const bad of [log.replace('Classical.choice, ',''),log.replace('Quot.sound','sorryAx'),log+log,log.replace(FAMILY,'wrong_name')])expect(()=>checkAxioms(bad,{[FAMILY]:AXIOMS,[SOURCE]:SOURCE_AXIOMS})).toThrow()
 })
 test('keeps exact retained helper footprints and exact final theorem axioms',()=>{
  expect(expectedAxioms('PaxosEprLiteralGlobal')).toEqual({'Bapa.PaxosEprLiteral.global_checked':['propext']})
  for(const index of entries){
   const name='Bapa.PaxosEprLiteral.entry'+index+'_checked'
   const axioms=[7,10,20].includes(index)?AXIOMS:['propext']
   expect(expectedAxioms('PaxosEprLiteralEntry'+index)).toEqual({[name]:axioms})
   expect(()=>checkAxioms(`'${name}' depends on axioms: [${axioms.join(', ')}]\n`,{[name]:axioms})).not.toThrow()
  }
  expect(expectedAxioms('PaxosEprAccepted')).toEqual({[FAMILY]:AXIOMS,[SOURCE]:SOURCE_AXIOMS})
  expect(()=>expectedAxioms('PaxosEprLiteralEntry25')).toThrow('unexpected fresh')
  expect(()=>checkAxioms("'Bapa.PaxosEprLiteral.global_checked' depends on axioms: [propext, Quot.sound]\n",expectedAxioms('PaxosEprLiteralGlobal'))).toThrow('axiom mismatch')
 })
 test('changed objects, traversal and symbolic link inputs refused',()=>{
  const dir=mkdtempSync(join(tmpdir(),'paxos-release-unit-'))
  try{
   writeFileSync(join(dir,'object.olean'),'checked bytes')
   expect(()=>checkedFile(dir,'object.olean',hash('checked bytes'))).not.toThrow()
   writeFileSync(join(dir,'object.olean'),'changed bytes')
   expect(()=>checkedFile(dir,'object.olean',hash('checked bytes'))).toThrow('changed')
   symlinkSync(join(dir,'object.olean'),join(dir,'alias.olean'))
   expect(()=>checkedFile(dir,'alias.olean',hash('changed bytes'))).toThrow('non-regular')
   expect(()=>checkedFile(dir,'../outside','0'.repeat(64))).toThrow('unsafe')
  }finally{rmSync(dir,{recursive:true,force:true})}
 })
 test('only root-reachable local imports required; orphans cannot widen the gate',()=>{
  const dir=mkdtempSync(join(tmpdir(),'paxos-release-graph-'))
  try{
   writeFileSync(join(dir,'Root.lean'),'import Leaf\nimport Lean\n')
   writeFileSync(join(dir,'Leaf.lean'),'')
   writeFileSync(join(dir,'Orphan.lean'),'import UnavailableOrphanDependency\n')
   const files={'Root.lean':hash('root'),'Leaf.lean':hash('leaf'),'Orphan.lean':hash('orphan')}
   expect(reachableModules(dir,files,'Root')).toEqual({modules:['Leaf','Root'],external:['Lean']})
   expect(()=>reachableModules(dir,{'Root.lean':files['Root.lean'],'Orphan.lean':files['Orphan.lean']},'Root')).toThrow('missing reachable import Leaf')
   writeFileSync(join(dir,'Root.lean'),'import UnapprovedExternal\n')
   expect(()=>reachableModules(dir,files,'Root')).toThrow('missing reachable import UnapprovedExternal')
  }finally{rmSync(dir,{recursive:true,force:true})}
 })
 test('capsule and complete checked/source-object dependency closure',()=>{
  const files=capsuleFiles(join(root,CAPSULE)),expected=expectedReuse(root,files)
  expect(Object.keys(files)).toHaveLength(143)
  expect(Object.keys(expected.objects)).toHaveLength(136)
  expect(expected.reused).toHaveLength(81)
  expect(expected.reachable.modules).toHaveLength(110)
  expect(expected.reachable.external).toEqual(['Lean'])
  expect(FRESH).toHaveLength(29)
 })
})

// The native job supplies its actual exported packet. No synthetic success receipt.
const packet=process.env.PAXOS_REPLAY_TEST_PACKET
if(packet)test('actual packet accepts, then tampering is refused by the pure auditor',()=>{
 const dir=resolve(packet),receiptPath=join(dir,'PAXOS-REPLAY.json'),original=readFileSync(receiptPath)
 const baseline=auditPaxosReplay(dir,root)
 expect(baseline.status).toBe('SOURCE_CHECKED')
 expect(baseline.cleanSourceBuild).toBe(false)
 function tamper(f:(r:PaxosReplayReceipt)=>void,reason:string){
  const r=JSON.parse(original.toString()) as PaxosReplayReceipt;f(r)
  try{writeFileSync(receiptPath,JSON.stringify(r));expect(()=>auditPaxosReplay(dir,root)).toThrow(reason)}finally{writeFileSync(receiptPath,original)}
 }
 tamper(r=>{r.entries.pop()},'incomplete entries')
 tamper(r=>{r.obligations.pop()},'incomplete obligations')
 tamper(r=>{r.fresh.pop()},'incomplete fresh checks')
 tamper(r=>{r.axioms[SOURCE]=AXIOMS},'recorded axioms')
 tamper(r=>{r.commands[3]!.exitCode=1},'native command failed')
 tamper(r=>{r.commands.pop()},'incomplete native commands')
 tamper(r=>{r.commands[4]=r.commands[3]!},'native command order')
 tamper(r=>{r.commands[3]!.stdout=r.commands[4]!.stdout},'unsafe log path')
 tamper(r=>{r.sourceReproductionFiles['basis.json']='0'.repeat(64)},'source reproduction inventory')
 tamper(r=>{r.implementationSha256='0'.repeat(64)},'implementation hash')
 tamper(r=>{r.reused[0]!.objectSha256='0'.repeat(64)},'reused source-object provenance')
 tamper(r=>{r.reused[0]!.dependencies={}},'reused source-object provenance')
 const source=join(dir,'project/PaxosEprAtomicDefs.lean'),object=join(dir,'project/checked',baseline.reused[0]!.module+'.olean')
 for(const file of [source,object,join(dir,'source-reproduction/basis.json'),join(dir,'runtime/Lean.olean')]){const bytes=readFileSync(file);try{writeFileSync(file,Buffer.concat([bytes,Buffer.from('\nchanged')]));expect(()=>auditPaxosReplay(dir,root)).toThrow('changed')}finally{writeFileSync(file,bytes)}}
 const exportPath=join(dir,'provenance/base-export.json'),bytes=readFileSync(exportPath)
 try{writeFileSync(exportPath,'[]');expect(()=>verifyOriginalExports(join(dir,'provenance'),root,baseline.sourceFiles)).toThrow('changed')}finally{writeFileSync(exportPath,bytes)}
 expect(auditPaxosReplay(dir,root)).toEqual(baseline)
})
