// Research-only proposal ordering: every selected fact still needs its ordinary proof.
import {type C,type E} from '../../core/machine.ts'
import {type Count,type Path,substE,truth} from '../../kernel/kernel.ts'
import {checkWall} from '../../core/wall.ts'
export type DeriveClass={index:number,frame:boolean,monotone:boolean,member:boolean,alias:boolean,partition:boolean,zero:boolean}
export function deriveClassOrder(items:DeriveClass[]):number[]{
 const rank=(c:DeriveClass)=>c.zero?undefined:c.frame?0:c.monotone?1:c.member?2:c.alias?3:c.partition?4:undefined
 const seen=new Set<number>()
 return items.flatMap((c,order)=>{const r=rank(c);return r===undefined?[]:[{index:c.index,rank:r,order}]}).sort((a,b)=>a.rank-b.rank||a.order-b.order).filter(c=>{if(seen.has(c.index))return false;seen.add(c.index);return true}).slice(0,24).map(c=>c.index)
}
// Conservative syntactic equality after path-decided ifs; this only selects a
// proof attempt, never supplies a frame as a trusted equality.
export function sameCountBody(a:Count|undefined,b:Count|undefined,path:Path):boolean{
 if(!a||!b)return false
 let visits=0
 const normalize=(value:any):any=>{
  if(++visits%128===0)checkWall('derive frame classification')
  if(visits>100000)throw Error('frame classification cap')
  if(!value||typeof value!=='object')return value
  if(value.op==='if'){const t=truth(value.c as C,path);if(t!==undefined)return normalize(t?value.then:value.else)}
  return Array.isArray(value)?value.map(normalize):Object.fromEntries(Object.entries(value).map(([k,v])=>[k,normalize(v)]))
 }
 const body=(c:Count):E=>substE(c.body,{vars:{[c.key]:{op:'var',name:'derive$class$key'}},maps:{},flags:{}})
 try{return JSON.stringify(normalize([a.below,body(a)]))===JSON.stringify(normalize([b.below,body(b)]))}catch(e){if(visits<=100000)throw e;return false}
}
