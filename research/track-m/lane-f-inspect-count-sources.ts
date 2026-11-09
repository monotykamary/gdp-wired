// Read-only identity audit of generated source candidates; no proof or new premise.
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {walkOnce} from '../../core/machine.ts'
import {termColumn} from '../../kernel/kernel.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {unpack} from './section18-codec.ts'
const [file,list]=process.argv.slice(2)
if(!file||!list)throw Error('CONTEXT INDICES')
const text=readFileSync(file,'utf8'),{p}=unpack(text)
for(const[i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
const cert=focusCountCert(p.m,p.packet.decls,certFor(p.packet.goal,p.packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.packet.goal.hyps.at(-1)})
const counts=new Map((countsForReads(p.packet.decls,cert.reads)??[]).map(c=>[c.v,c]))
const selected=list.split(',').map(Number)
if(selected.some(i=>!Number.isSafeInteger(i)||i<0||i>=cert.insts.length))throw Error('invalid source index')
const rows=selected.map(index=>{
 const inst=cert.insts[index]!
 const reads=inst.terms.map(([coefficient,id])=>{
  const read=cert.reads.find(r=>r[0]===id),count=counts.get(id),maps=new Set<string>(),variables=new Set<string>()
  if(count)walkOnce(count.body,(o:any)=>{if(o.op==='get')maps.add(o.map);if(o.op==='var')variables.add(o.name)})
  return {coefficient,id,read,below:count?.below,key:count?.key,body:count?{op:count.body.op,sha256:createHash('sha256').update(JSON.stringify(count.body)).digest('hex'),maps:[...maps],variables:[...variables]}:undefined}
 })
 return {index,inst,reads}
})
console.log(JSON.stringify({contextSha256:createHash('sha256').update(text).digest('hex'),instances:cert.insts.length,rows}))
