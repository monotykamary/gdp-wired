import {expect,spyOn,test} from 'bun:test'
import {type Law,type Machine,atMost,get,n,same,x} from './machine.ts'
import {type CountCert,type Instances,checkMC,countedObligations,mcGoal} from '../kernel/kernel.ts'
import * as kernel from '../kernel/kernel.ts'
import * as transport from './count-cert-transport.ts'
import {type CountLawProof,type CountReplayDecline,scopeCountProof,replayScopedCountProof,isCheckedReducedScope} from './count-proof-scope.ts'
import {clock,grow,withDeadline,withWall} from '../kernel/prove.ts'
import {cdclStats} from '../kernel/cdcl.ts'

const bounded=<T>(run:(until:number)=>T):T=>withWall(performance.now()+10000,()=>{const until=clock()+5000;return withDeadline(until,()=>run(until))})
function fixture(until:number){
 const m:Machine={name:'required family only',params:[],inputs:[],state:{left:n(0),right:n(0)},maps:{M:0},
  facts:[{name:'background',forall:'k',holds:same(x('k'),x('k'))}],
  step:{state:{left:x('right'),right:x('left')},flags:{allZero:{op:'all',key:'k',c:same(get('M',x('k')),n(0))}}}}
 const left:Law={name:'left',holds:same(x('left'),n(0))},right:Law={name:'right',holds:same(x('right'),n(0))}
 const held:Law={name:'held indexed',forall:'k',holds:same(get('M',x('k')),n(0))}
 const outside:Law={name:'outside indexed',forall:'k',holds:atMost(get('M',x('k')),n(100))}
 const family=[outside,held,left,right],instances:Instances={[held.name]:[n(0)],[outside.name]:[n(1)],background:[n(2)],'?allZero':[n(3)]},certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,family,{[left.name]:instances},family.indexOf(left))){
  const header={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,header)!
  const result=grow(expanded,new Map(),{nodes:0,until})
  if(!('tree'in result))throw Error('small required-family fixture did not close: '+goal.name)
  const cert={...header,tree:result.tree};expect(checkMC(goal.hyps,decls,cert)).toBe(true);certs[goal.name]=cert
 }
 const proof:CountLawProof={instances,certs},scoped=scopeCountProof(m,left,family,proof,until)!
 expect(scoped).toBeDefined()
 return {m,left,right,held,outside,family,proof,scoped}
}

test('required reduction retains uncited held instances and original certificates on exact context equality',()=>bounded(until=>{
 const f=fixture(until),before=cdclStats.runs,move=spyOn(transport,'replayCountCertificate'),native=spyOn(kernel,'checkMC')
 expect(f.scoped.unused).toContain(f.held.name)
 try{
  const result=replayScopedCountProof(f.m,f.family,f.scoped,until)!
  expect(result).toBeDefined();expect(result.instances[f.held.name]).toBe(f.proof.instances[f.held.name])
  expect(result.premises).toContain(f.held.name);expect(result.premises).toContain(f.outside.name)
  for(const key of Object.keys(f.proof.certs))expect(result.certs[key]).toBe(f.proof.certs[key])
  expect(move).not.toHaveBeenCalled();expect(native).toHaveBeenCalledTimes(2);expect(cdclStats.runs).toBe(before)
 }finally{move.mockRestore();native.mockRestore()}
}))

test('required reduction drops only outside candidate instances and retains real fact and quantified-flag instances',()=>bounded(until=>{
 const f=fixture(until),family=[f.held,f.left,f.right]
 const result=replayScopedCountProof(f.m,family,f.scoped,until,{sourceFamily:f.family})!
 expect(result).toBeDefined();expect(result.instances[f.outside.name]).toBeUndefined()
 for(const name of [f.held.name,'background','?allZero'])expect(result.instances[name]).toBe(f.proof.instances[name])
 expect(result.premises).toContain(f.held.name);expect(result.premises).not.toContain(f.outside.name)
 for(const {goal,decls}of countedObligations(f.m,family,{[f.left.name]:result.instances},family.indexOf(f.left)))
  expect(checkMC(goal.hyps,decls,result.certs[goal.name]!)).toBe(true)
}))

test('identity transport shortcut requires native declarations as well as expanded goal equality',()=>bounded(until=>{
 const f=fixture(until),sourceDecls=f.scoped.sourceDecls!.map(ds=>[...ds])
 sourceDecls[0]!.push({map:'extra',j:'j',key:'k',below:n(0),body:n(0)})
 const move=spyOn(transport,'replayCountCertificate')
 try{
  expect(replayScopedCountProof(f.m,f.family,{...f.scoped,sourceDecls},until)).toBeDefined()
  expect(move).toHaveBeenCalledTimes(1)
 }finally{move.mockRestore()}
}))

test('unchanged corrupted certificate is natively rejected even with closing deferral requested',()=>bounded(until=>{
 const f=fixture(until),key=f.left.name+' @start',saved=process.env.GDP_COUNT_FINAL_DEFER_CHECKS
 process.env.GDP_COUNT_FINAL_DEFER_CHECKS='1'
 const bad={...f.scoped,proof:{...f.scoped.proof,status:'unchecked' as const,certs:{...f.proof.certs,[key]:{...f.proof.certs[key]!,tree:{leaf:[]}}}}}
 const move=spyOn(transport,'replayCountCertificate'),declines:CountReplayDecline[]=[]
 try{
  expect(replayScopedCountProof(f.m,f.family,bad,until,{deferToClosing:true,onDecline:d=>declines.push(d)})).toBeUndefined()
  expect(move).not.toHaveBeenCalled();expect(isCheckedReducedScope(bad,f.m,f.family)).toBe(false)
  expect(declines).toEqual([{case:6,reason:'native-check-failed',member:f.left.name,obligation:key}])
 }finally{move.mockRestore();if(saved===undefined)delete process.env.GDP_COUNT_FINAL_DEFER_CHECKS;else process.env.GDP_COUNT_FINAL_DEFER_CHECKS=saved}
}))

test('real missing law fact is named even if untrusted premise metadata omitted that dependency',()=>bounded(until=>{
 const f=fixture(until),declines:CountReplayDecline[]=[],repairs:string[]=[]
 const omitted={...f.scoped,premises:[],unused:f.family.filter(l=>l!==f.left).map(l=>l.name)}
 expect(replayScopedCountProof(f.m,[f.left],omitted,until,{sourceFamily:f.family,onDecline:d=>declines.push(d),onTransportDecline:name=>repairs.push(name)})).toBeUndefined()
 expect(declines.at(-1)).toMatchObject({case:5,reason:'unheld-law-dependency',member:f.left.name,premise:f.right.name,blockers:[f.right.name]})
 expect(repairs).toEqual([])
}))

test('generated, cut-validation, deadline and unattributed declines never invent a law blocker',()=>bounded(until=>{
 const f=fixture(until),family=[...f.family].reverse()
 for(const detail of [
  {stage:'leaf-mapping' as const,part:'main' as const,reason:'missing-pair-row'},
  {stage:'cut-validation' as const,part:'main' as const,reason:'invalid-native-cuts-or-counts',sourceFact:f.right.holds},
  {stage:'transport' as const,part:'main' as const,reason:'deadline',sourceFact:f.right.holds},
 ]){
  const move=spyOn(transport,'replayCountCertificate').mockImplementation((_from,_to,_cert,_until,options)=>{options?.onDecline?.(detail);return undefined})
  const declines:CountReplayDecline[]=[]
  try{
   expect(replayScopedCountProof(f.m,family,f.scoped,until,{sourceFamily:f.family,onDecline:d=>declines.push(d)})).toBeUndefined()
   expect(declines.at(-1)?.reason).toBe('certificate-transport-declined');expect(declines.at(-1)?.blockers).toBeUndefined()
  }finally{move.mockRestore()}
 }
}))
