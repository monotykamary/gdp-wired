// Untrusted path specialization plus original-term correspondence. The caller
// transports and checks a resulting proof; no folded fact is trusted.
import {type C,type E} from '../../core/machine.ts'
import {type Goal,type Path,canon,linear,truth} from '../../kernel/kernel.ts'
const expressions=new Set(['var','const','mul','prod','add','sub','min','max','if','get','tup','proj'])
const conditions=new Set(['not','and','or','<','<=','='])
export function foldPath(g:Goal,path:Path):{goal:Goal,opaque:Record<string,E>}{
 const seen=new WeakMap<object,any>(),opaque:Record<string,E>={}
 const yes:C={op:'and',xs:[]},no:C={op:'or',xs:[]}
 const f=(o:any):any=>{
  if(!o||typeof o!=='object')return o
  if(seen.has(o))return seen.get(o)
  let out:any
  if(Array.isArray(o))out=o.map(f)
  else if(conditions.has(o.op)&&truth(o as C,path)!==undefined)out=truth(o as C,path)?yes:no
  else if(o.op==='if'&&truth(o.c,path)!==undefined)out=f(truth(o.c,path)?o.then:o.else)
  else{
   out=Object.fromEntries(Object.entries(o).map(([k,v])=>[k,f(v)]))
   if(out.op==='and'||out.op==='or'){
    const neutral=out.op==='and'?'and':'or',xs=out.xs.filter((c:C)=>!((c.op==='and'||c.op==='or')&&c.op===neutral&&c.xs.length===0))
    out=xs.length===1?xs[0]:{...out,xs}
   }
  }
  seen.set(o,out)
  if(expressions.has(o.op)){
   const a=linear(out,path),b=linear(o,path),entry=a&&Object.entries(a)
   if(a&&b&&entry?.length===1&&entry[0]![0]!=='1'&&entry[0]![1]===1&&canon(a)!==canon(b))opaque[entry[0]![0]]=o
  }
  return out
 }
 return {goal:{...g,hyps:g.hyps.map(f)},opaque}
}
