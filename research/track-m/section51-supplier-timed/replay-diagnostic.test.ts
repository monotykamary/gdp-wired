import {expect,test} from 'bun:test'
import {createHash} from 'node:crypto'
import {readFileSync,mkdtempSync,statSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {encode,save} from './io.ts'
import {countReplayDiagnostic,emitReplayDiagnostic} from '../../../core/count-replay-diagnostic.ts'
import {CountRecipePass,runCountRecipeController} from '../../../core/count-recipe-controller.ts'
import {WorkLedger} from '../../../core/work-admission.ts'
import {workAmount,zeroWork} from '../../../core/work-amount.ts'
import {type WorkKey,workKeys} from '../../../core/work-kinds.ts'
import {boundedReplayJSON,replayDiagnosticCollector,REPLAY_DIAGNOSTIC_LIMITS} from './replay-diagnostic.ts'
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
test('a complete bounded certificate has a real full serialization hash',()=>{
 const certificate={reads:[],insts:[],tree:{leaf:[{kind:'input',index:0}]},frames:[],monos:[],lins:[]}
 const result=boundedReplayJSON(certificate)
 expect(result.complete).toBe(true);expect(result.replayable).toBe(true);expect(JSON.parse(result.serialisation)).toEqual(certificate)
 expect(result.fullValueSha256).toBe(hash(JSON.stringify(certificate)))
})
test('bounded prefix cannot masquerade as a complete certificate hash or replay',()=>{
 const result=boundedReplayJSON({tree:Array.from({length:10000},(_,i)=>({i,text:'x'.repeat(1000)}))})
 expect(result.truncated).toBe(true);expect(result.complete).toBe(false);expect(result.replayable).toBe(false);expect(result.fullValueSha256).toBeNull()
 expect(result.hashScope).toBe('serialized-prefix-only');expect(result.bytes).toBeLessThanOrEqual(REPLAY_DIAGNOSTIC_LIMITS.recordBytes)
})
test('diagnostics neither call getters nor recurse through cyclic data',()=>{
 let called=false;const value:any={};Object.defineProperty(value,'getter',{enumerable:true,get(){called=true;throw Error('getter')}});value.self=value
 const result=boundedReplayJSON(value)
 expect(called).toBe(false);expect(result.complete).toBe(false);expect(result.replayable).toBe(false)
})
test('member-specific repair is joined after the first decline, never inferred from another member',()=>{
 const c=replayDiagnosticCollector({sourceCommit:'source',sealSHA256:'seal'})
 c.capture({kind:'certificate-decline',context:{passId:1,member:'A',obligation:'A @step'},certificateId:7,certificate:{tree:{leaf:[]}},cutCounts:{frames:2,monos:1,lins:1,lemmas:0},detail:{stage:'leaf-mapping'}})
 c.capture({kind:'certificate-decline',context:{passId:1,member:'B',obligation:'B @step'},certificate:{tree:{leaf:[]}}})
 c.capture({kind:'resolver-start',context:{passId:1,member:'A'}})
 c.capture({kind:'resolver-result',context:{passId:1,member:'A'},result:'repaired',premisesBefore:['old'],payloadPremisesAfter:['new'],effectivePremisesAfter:['old','new']})
 const result=c.finish();const a=result.events.find(e=>e.member==='A'),b=result.events.find(e=>e.member==='B')
 expect(a.memberRepair.ran).toBe(true);expect(a.memberRepair.supplierDelta).toEqual(['new']);expect(b.memberRepair.ran).toBe(false)
 expect(a.cutCounts).toEqual({frames:2,monos:1,lins:1,lemmas:0});expect(result.proofAuthority).toBe(false)
})
test('artifact aggregate stays bounded and incomplete histories yield unavailable, not false',()=>{
 const c=replayDiagnosticCollector({sourceCommit:'source'})
 for(let i=0;i<200;i++)c.capture({kind:'resolver-start',context:{passId:i,member:'member'+i},data:'x'.repeat(8000)})
 c.capture({kind:'certificate-decline',context:{passId:999,member:'missing'},certificate:{data:'y'.repeat(80000)},detail:{stage:'leaf-mapping',sourceRow:{lin:{a:1},src:{fact:3}}}})
 const result=c.finish();expect(result.complete).toBe(false);expect(result.droppedHistory).toBeGreaterThan(0)
 expect(result.events.at(-1).memberRepair.ran).toBeNull();expect(encode(result,REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes).length).toBeLessThanOrEqual(REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes)
 expect(JSON.parse(result.events.at(-1).details.serialisation).detail.sourceRow.src.fact).toBe(3)
 expect(result.accounting.chargedToProofUnits).toBe(false);expect(result.accounting.timingNeutralClaim).toBe(false)
})
test('undefined-only properties consume the traversal work budget',()=>{
 const value=Object.fromEntries(Array.from({length:10000},(_,i)=>['p'+i,undefined]))
 const result=boundedReplayJSON(value,{...REPLAY_DIAGNOSTIC_LIMITS,nodes:32})
 expect(result.workSteps).toBe(32);expect(result.complete).toBe(false);expect(result.replayable).toBe(false)
})
test('long member names sharing a prefix are unavailable, never falsely joined',()=>{
 const c=replayDiagnosticCollector({sourceCommit:'source'}),prefix='m'.repeat(256)
 c.capture({kind:'resolver-result',context:{passId:1,member:prefix+'A'},result:'repaired',premisesBefore:[],effectivePremisesAfter:['supplier']})
 c.capture({kind:'certificate-decline',context:{passId:1,member:prefix+'B'},certificate:{tree:{leaf:[]}}})
 const event=c.finish().events[0]
 expect(event.memberIdentityComplete).toBe(false);expect(event.memberRepair.ran).toBeNull();expect(event.memberRepair.status).toBe('unavailable-member-identity')
})
test('every section and final saved bytes stay bounded for wide supplier summaries and identity',()=>{
 const c=replayDiagnosticCollector({sourceCommit:'source'}),names=Array.from({length:64},(_,i)=>'界'.repeat(254)+String(i).padStart(2,'0'))
 for(let i=0;i<64;i++)c.capture({kind:'resolver-result',context:{passId:1,member:'member'+i},result:'repaired',premisesBefore:[],payloadPremisesAfter:names,effectivePremisesAfter:names})
 const result=c.finish(),bytes=encode(result,REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes)
 expect(result.memberRepairSummary).toHaveLength(64);expect(result.memberRepairSummary.every(x=>x.supplierDeltaStatus==='unavailable-byte-bound')).toBe(true)
 expect(result.complete).toBe(false);expect(bytes.length).toBeLessThanOrEqual(REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes);expect(bytes.at(-1)).toBe(10)
 const dir=mkdtempSync(join(tmpdir(),'cut-artifact-'))
 try{const path=join(dir,'replay-declines.json');save(path,result,REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes);expect(statSync(path).size).toBe(bytes.length)}finally{rmSync(dir,{recursive:true,force:true})}
 const huge=replayDiagnosticCollector({sourceCommit:'界'.repeat(1000000)}).finish()
 expect(huge.identity).toBeNull();expect(huge.identityCapture.replayable).toBe(false);expect(encode(huge,REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes).length).toBeLessThanOrEqual(REPLAY_DIAGNOSTIC_LIMITS.aggregateBytes)
})
test('real controller observation reports the effective union and cannot renew the repair bit',()=>{
 // Bookkeeping-only held payloads and an explicit simulated closing decline;
 // no native proof, producer search or supplier-closure result is claimed.
 const c=replayDiagnosticCollector({sourceCommit:'controller-control'}),old=countReplayDiagnostic.on
 countReplayDiagnostic.on=c.capture
 const bank=new WorkLedger(Object.fromEntries(workKeys.map(key=>[key,1])) as Record<WorkKey,number>)
 try{bank.withBudget(workAmount(1000000n),()=>{
  const pass=new CountRecipePass<string>(['old','new','target'].map((name,reference)=>({name,reference,recipes:[{id:'held',kind:'ordinary' as const,required:[]}]})),'fixed',bank)
  for(const state of pass.states){state.recipes[0]!.terminal=true;state.held={recipeId:'held',payload:'before',premises:state.member.name==='target'?['old']:[],checkedReduced:false,checkCost:zeroWork}}
  let repairs=0,closes=0
  const hooks={construct:()=>{throw Error('no search allowed')},declinedMember:()=> 'target',repairSuppliers:()=>{repairs++;return {payload:'after',premises:['new']}},close:()=>{closes++;if(closes===1){emitReplayDiagnostic({kind:'scope-decline',context:{member:'target',obligation:'bookkeeping-control'},reason:'simulated-for-observation-control'});return false}return true}}
  expect(runCountRecipeController(pass,['target'],hooks).result).toBe(true)
  expect(pass.held().get('target')!.premises).toEqual(['old','new']);expect(pass.supplierRepairUsed).toBe(true)
  runCountRecipeController(pass,['target'],hooks);expect(repairs).toBe(1)
 })}finally{countReplayDiagnostic.on=old}
 const result=c.finish(),event=result.events.find(e=>e.kind==='scope-decline')
 expect(event.memberRepair.ran).toBe(true);expect(event.memberRepair.supplierDelta).toEqual(['new'])
 const observed=result.repairHistory.map(e=>JSON.parse(e.serialisation)).find(e=>e.kind==='resolver-result')
 expect(observed.payloadPremisesAfter).toEqual(['new']);expect(observed.effectivePremisesAfter).toEqual(['old','new'])
})
test('native binder controls exercise the new required artifact',async()=>{await import('./native-binding-controls.ts')})

test('both native modes export the dedicated artifact without enabling full timed tracing',()=>{
 const source=readFileSync(new URL('./driver.ts',import.meta.url),'utf8')
 expect(source).toContain("save(join(out,'replay-declines.json')")
 expect(source).toContain("mode==='instrumented'?(await import('./observer.ts')).observer:undefined")
 expect(source).toContain('countReplayDiagnostic.on=replayDiagnostics.capture')
})
