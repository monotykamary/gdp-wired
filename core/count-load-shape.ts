// Untrusted discovery of a marked row loaded from a plain-key map.
// The existing family supplies every premise; names never select a law.
import {type C,type E,type Law,type Machine,n,walkOnce,x} from './machine.ts'
import {type LiftedCountGuardShape} from './count-lifted-shape.ts'
const json=(v:unknown)=>JSON.stringify(v)
const atoms=(c:C):C[]=>c.op==='and'?c.xs.flatMap(atoms):[c]
const variable=(e:E,name:string)=>e.op==='var'&&e.name===name
const has=(root:unknown,predicate:(node:any)=>boolean)=>{let found=false;walkOnce(root,(node:any)=>{if(predicate(node))found=true});return found}
export type CountRowLoad={law:Law,source:string,written:string,guard:string,marker:{map:string,value:number},phaseLaws:Law[]}
export function discoverCountRowLoad(m:Machine,shape:LiftedCountGuardShape,family:readonly Law[],choice:{name:string,value:number}):CountRowLoad|undefined{
 const results:CountRowLoad[]=[]
 for(const law of family){
  if(!law.forall||law.keys?.length!==1||law.holds.op!=='or')continue
  const equality=law.holds.xs.find(c=>c.op==='='),negated=law.holds.xs.find(c=>c.op==='not')
  if(equality?.op!=='='||negated?.op!=='not')continue
  const [row,source]=equality.a.op==='get'&&equality.a.map===shape.origin.membershipMap?[equality.a,equality.b]:[equality.b,equality.a]
  if(row.op!=='get'||source.op!=='get'||row.map!==shape.origin.membershipMap||source.map===row.map||!Object.hasOwn(m.maps??{},source.map)||!variable(source.key,law.keys[0]!))continue
  const key=row.key
  if(key.op!=='add'||key.a.op!=='mul'||key.a.k!==shape.origin.width||!variable(key.a.a,law.forall)||!variable(key.b,law.keys[0]!))continue
  const conditions=atoms(negated.x),markers=conditions.flatMap(c=>{
   if(c.op!=='=')return []
   const [cell,value]=c.a.op==='get'?[c.a,c.b]:[c.b,c.a]
   return cell.op==='get'&&variable(cell.key,law.forall!)&&value.op==='const'&&value.value>=1&&Object.hasOwn(m.maps??{},cell.map)?[{map:cell.map,value:value.value}]:[]
  })
  for(const marker of markers){
   const write=m.step.maps?.[marker.map],rowWrite=m.step.maps?.[row.map]
   if(!write||'each'in write||write.key.op!=='var'||!m.inputs.includes(write.key.name)||write.value.op!=='if'||json(write.value.then)!==json(n(marker.value))||!rowWrite||!('each'in rowWrite))continue
   const written=write.key.name,flags:string[]=[]
   walkOnce(write.value.c,(node:any)=>{if(node.op==='flag')flags.push(node.name)})
   for(const guard of flags){
    const definition=m.step.flags?.[guard]
    if(!definition||!has(definition,node=>node.op==='='&&(json(node.a)===json(x(choice.name))&&json(node.b)===json(n(choice.value))||json(node.b)===json(x(choice.name))&&json(node.a)===json(n(choice.value)))))continue
    if(!has(rowWrite.value,node=>node.op==='flag'&&node.name===guard)||!has(rowWrite.value,node=>node.op==='get'&&node.map===source.map&&node.key.op==='sub'&&variable(node.key.a,rowWrite.each)&&node.key.b.op==='mul'&&node.key.b.k===shape.origin.width&&variable(node.key.b.a,written)))continue
    const phaseLaws=family.filter(candidate=>{
     if(!candidate.forall||candidate.keys?.length)return false
     const maps=new Set<string>();walkOnce(candidate.holds,(node:any)=>{if(node.op==='get')maps.add(node.map)})
     if(maps.size===1&&maps.has(marker.map))return has(candidate.holds,node=>(node.op==='<='||node.op==='<')&&node.a.op==='get'&&node.a.map===marker.map&&node.b.op==='const'&&node.b.value<=(node.op==='<'?marker.value+1:marker.value))
     return maps.size===2&&maps.has(marker.map)&&maps.has(shape.origin.rowCount)&&has(candidate.holds,node=>node.op==='='&&((node.a.op==='get'&&node.a.map===marker.map&&json(node.b)===json(n(0)))||(node.b.op==='get'&&node.b.map===marker.map&&json(node.a)===json(n(0)))))
    })
    if(!phaseLaws.some(candidate=>has(candidate.holds,node=>node.op==='get'&&node.map===shape.origin.rowCount)))continue
    results.push({law,source:source.map,written,guard,marker,phaseLaws})
   }
  }
 }
 // Prefer the unphased load law; an extra scalar guard is not silently dropped.
 const size=(value:unknown)=>{let count=0;walkOnce(value,()=>{count++});return count}
 results.sort((a,b)=>size(a.law.holds)-size(b.law.holds))
 if(!results.length)return
 const first=results[0]!
 if(results.some(result=>json([result.source,result.written,result.guard,result.marker])!==json([first.source,first.written,first.guard,first.marker])))return
 return first
}
