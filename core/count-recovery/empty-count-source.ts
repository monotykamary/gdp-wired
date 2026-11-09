// A bounded search hint only: an empty indicator needs no field premises.
// Its ordinary witness clause and reconstructed tree still go through admission.
import {type C,type E} from '../machine.ts'
export function emptyCountSource(body:E,aliases:Record<string,E>={}):boolean{
 let work=16384
 const same=(a:any,b:any,depth=0):boolean=>{
  if(--work<0||depth>128)return false
  if(a?.op==='var'&&aliases[a.name])a=aliases[a.name]
  if(b?.op==='var'&&aliases[b.name])b=aliases[b.name]
  if(a===b)return true
  if(!a||!b||typeof a!=='object'||typeof b!=='object')return false
  const keys=Object.keys(a);return keys.length===Object.keys(b).length&&keys.every(k=>Object.hasOwn(b,k)&&same(a[k],b[k],depth+1))
 }
 const impossible=(c:C,depth=0):boolean=>{
  if(--work<0||depth>128)return false
  if(c.op==='or')return c.xs.every(x=>impossible(x,depth+1))
  if(c.op!=='and')return false
  const xs:C[]=[],flatten=(x:C,d:number):void=>{if(--work<0||d>128)return;if(x.op==='and')x.xs.forEach(y=>flatten(y,d+1));else xs.push(x)}
  flatten(c,depth)
  return work>=0&&(xs.some(x=>x.op==='or'&&impossible(x,depth+1))||xs.some(x=>x.op==='not'&&xs.some(y=>same(x.x,y,depth+1))))
 }
 const zero=(e:E,depth=0):boolean=>{
  if(--work<0||depth>128)return false
  if(e.op==='const')return e.value===0
  return e.op==='if'&&(impossible(e.c,depth+1)?zero(e.else,depth+1):zero(e.then,depth+1)&&zero(e.else,depth+1))
 }
 return zero(body)
}
