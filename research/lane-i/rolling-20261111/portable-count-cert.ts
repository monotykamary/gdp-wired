// Process-local term-column numbers are not a wire format. Keep their ordinary
// expressions and rebind every occurrence before the existing checker runs.
import {type E} from '../../../core/machine.ts'
import {type CountCert,columnTerm,termColumn} from '../../../kernel/kernel.ts'
export type PortableCountCert={cert:CountCert,termColumns:Record<string,E>}
const pattern=/⟦[0-9]+⟧/g
function references(value:unknown,out=new Set<string>()):Set<string>{
 if(typeof value==='string')for(const name of value.match(pattern)??[])out.add(name)
 else if(Array.isArray(value))for(const v of value)references(v,out)
 else if(value&&typeof value==='object')for(const [key,v]of Object.entries(value)){references(key,out);references(v,out)}
 return out
}
function expression(t:any,depth=0):boolean{
 if(!t||typeof t!=='object'||depth>256)return false
 const e=(x:any)=>expression(x,depth+1),c=(x:any):boolean=>{
  if(!x||typeof x!=='object')return false
  if(x.op==='not')return c(x.x)
  if(x.op==='and'||x.op==='or')return Array.isArray(x.xs)&&x.xs.every(c)
  return ['=','<','<='].includes(x.op)&&e(x.a)&&e(x.b)
 }
 switch(t.op){
  case 'const':return Number.isSafeInteger(t.value)&&t.value>=0
  case 'var':return typeof t.name==='string'&&t.name!=='1'&&!/[*[\],:⟦⟧⟨⟩|]/.test(t.name)
  case 'get':return typeof t.map==='string'&&e(t.key)
  case 'mul':return Number.isSafeInteger(t.k)&&t.k>=0&&e(t.a)
  case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':return e(t.a)&&e(t.b)
  case 'proj':return (t.k===0||t.k===1)&&e(t.a)
  case 'if':return c(t.c)&&e(t.then)&&e(t.else)
  default:return false
 }
}
export function captureCountCert(cert:CountCert):PortableCountCert{
 const terms:Record<string,E>=Object.create(null)
 for(const name of references(cert)){const term=columnTerm(name);if(!term||!expression(term))throw Error('cannot serialize term column '+name);terms[name]=term}
 return {cert,termColumns:terms}
}
export function restoreCountCert(packet:PortableCountCert):CountCert{
 const names=references(packet.cert),replacement=new Map<string,string>()
 for(const name of names){const term=Object.hasOwn(packet.termColumns??{},name)?packet.termColumns[name]:undefined;if(!term||!expression(term))throw Error('missing/invalid term column '+name);replacement.set(name,termColumn(term))}
 const text=(s:string)=>s.replace(pattern,name=>{const value=replacement.get(name);if(!value)throw Error('unbound term column');return value})
 const visit=(v:any):any=>{
  if(typeof v==='string')return text(v)
  if(Array.isArray(v))return v.map(visit)
  if(!v||typeof v!=='object')return v
  const out:Record<string,any>=Object.create(null)
  for(const [key,value]of Object.entries(v)){const name=text(key),next=visit(value);if(Object.hasOwn(out,name)){if(typeof out[name]!=='number'||typeof next!=='number')throw Error('column collision');out[name]+=next}else out[name]=next}
  return out
 }
 return visit(packet.cert) as CountCert
}
