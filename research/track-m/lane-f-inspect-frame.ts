// Read-only description of the exact frozen write-frame candidates.
import {readFileSync} from 'node:fs'
import {unpack} from './section18-codec.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {mcGoal,termColumn} from '../../kernel/kernel.ts'
const {p}=unpack(readFileSync('context.json','utf8'))
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
const cert=focusCountCert(p.m,p.packet.decls,certFor(p.packet.goal,p.packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.packet.goal.hyps.at(-1)})
console.log(JSON.stringify({kind:'machine',inputs:p.m.inputs,params:p.m.params,flags:Object.keys(p.m.step.flags??{}),writes:p.m.step.maps,state:p.m.step.state}))
for(const read of cert.reads){
 const pre:[string,string,any]=[read[0],read[1].replace(/#$/,''),read[2]],c=countsForReads(p.packet.decls,[pre])?.[0]
 console.log(JSON.stringify({kind:'read',read,count:c}))
}
for(const [index,inst]of cert.insts.entries())if(index<40||inst.terms.length===2&&inst.terms.some((t:any)=>t[1]==='r$0'))console.log(JSON.stringify({kind:'instance',index,inst}))
console.log(JSON.stringify({kind:'laws',at:p.at,laws:p.laws?.map((l:any)=>({name:l.name,holds:l.holds})),keys:Object.keys(p)}))
const g=mcGoal(p.packet.goal.hyps,p.packet.decls,cert)!
console.log(JSON.stringify({kind:'source-zero',clause:g.hyps[g.hyps.length-cert.insts.length]}))
