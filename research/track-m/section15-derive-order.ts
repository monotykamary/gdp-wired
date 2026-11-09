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
// One classifier per synchronous ranking pass. Snapshot the branch so cached
// body keys cannot be reused under newly added or changed assumptions.
export function frameClassifier(path:Path):(a:Count|undefined,b:Count|undefined)=>boolean{
 const scope:Path=new Map([...path].map(([id,a])=>[id,{lin:{...a.lin},holds:a.holds}])),keys=new Map<Count,string|undefined>()
 const key=(c:Count):string|undefined=>{
  if(keys.has(c))return keys.get(c)
  let visits=0
  const normalize=(value:any):any=>{
   if(++visits%128===0)checkWall('derive frame classification')
   if(visits>100000)throw Error('frame classification cap')
   if(!value||typeof value!=='object')return value
   if(value.op==='if'){const t=truth(value.c as C,scope);if(t!==undefined)return normalize(t?value.then:value.else)}
   return Array.isArray(value)?value.map(normalize):Object.fromEntries(Object.entries(value).map(([k,v])=>[k,normalize(v)]))
  }
  let out:string|undefined
  try{const body:E=substE(c.body,{vars:{[c.key]:{op:'var',name:'derive$class$key'}},maps:{},flags:{}});out=JSON.stringify(normalize([c.below,body]))}catch(error){if(visits<=100000)throw error}
  keys.set(c,out);return out
 }
 return(a,b)=>{if(!a||!b)return false;const left=key(a),right=key(b);return left!==undefined&&right!==undefined&&left===right}
}
// Syntactic equality only selects an attempt; it never admits a trusted frame.
export const sameCountBody=(a:Count|undefined,b:Count|undefined,path:Path):boolean=>frameClassifier(path)(a,b)
