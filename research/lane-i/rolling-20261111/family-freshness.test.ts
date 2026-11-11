// Whole-family acceptance is stronger than replaying each counted packet.
import {expect,test} from 'bun:test'
import {type Machine,n,same} from '../../../core/machine.ts'
import {type CountCert,checkCountedLaws,checkMC,countedObligations,mcGoal} from '../../../kernel/kernel.ts'
import {counted,fullRate,rowsAt} from '../../../kernel/prove.ts'
import {solve} from '../../../core/solver.ts'
test('the full family rejects a witness collision even when all packet proofs check',()=>counted(fullRate,()=>{
 const machine:Machine={name:'freshness fixture',params:['collision'],inputs:[],state:{},counts:{C:{j:'row',key:'k',below:n(1),body:n(0)}},step:{}}
 const law={name:'constant law',holds:same(n(0),n(0))},instances={[law.name]:{}},packets=countedObligations(machine,[law],instances),certs:Record<string,CountCert>={}
 for(const packet of packets){
  const request={reads:[['r',packet.decls[0]!.map,n(0)] as [string,string,ReturnType<typeof n>]],insts:[{wit:'safeWitness',below:n(1),terms:[[1,'r'] as [number,string]],unit:0}],picks:[]}
  const goal=mcGoal(packet.goal.hyps,packet.decls,request);expect(goal).toBeDefined();if(!goal)throw Error('missing counted goal')
  const result=solve(rowsAt(goal,new Map()),500);expect(result.kind).toBe('refuted');if(result.kind!=='refuted')throw Error('constant goal not refuted')
  certs[packet.goal.name]={...request,tree:{leaf:result.steps}}
 }
 expect(checkCountedLaws(machine,[law],{instances,certs})).toBe(true)
 const collided=Object.fromEntries(Object.entries(certs).map(([name,cert])=>[name,{...cert,insts:cert.insts.map(inst=>({...inst,wit:'collision'}))}]))
 expect(packets.every(packet=>checkMC(packet.goal.hyps,packet.decls,collided[packet.goal.name]!))).toBe(true)
 expect(checkCountedLaws(machine,[law],{instances,certs:collided})).toBe(false)
},true))
