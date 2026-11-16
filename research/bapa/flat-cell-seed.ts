// Expand a universal over raw cell addresses only when that binder is used
// exclusively as whole keys of maps with one compatible explicit layout.
// Otherwise leave it untouched so the ordinary restater fails closed.
import type {E,Law} from '../../core/machine.ts'
import type {SeedBindings} from './candidate-seed-restatement.ts'
export function expandFlatCellBinders(law:Law,config:SeedBindings):{law:Law,bindings:Record<string,string[]>} {
 const original=[law.forall,...(law.keys??[])].filter((x):x is string=>!!x),bindings:Record<string,string[]>={}
 let holds=law.holds;const reserved=new Set(original), names:string[]=[]
 for(const name of original){
  const layouts:{sorts:string[],radix:number}[]=[];let outside=false
  const inspect=(x:unknown):void=>{
   if(Array.isArray(x)){x.forEach(inspect);return}if(!x||typeof x!=='object')return
   const o=x as Record<string,unknown>,key=o.key as E|undefined
   if(o.op==='get'&&key?.op==='var'&&key.name===name){const l=config.maps[String(o.map)];if(l)layouts.push(l);else outside=true;return}
   if(o.op==='var'&&o.name===name)outside=true
   Object.values(o).forEach(inspect)
  };inspect(holds)
  const layout=layouts[0]
  if(outside||!layout||layout.sorts.length<2||layouts.some(l=>JSON.stringify(l.sorts)!==JSON.stringify(layout.sorts)||l.radix!==layout.radix)){names.push(name);continue}
  const coords=layout.sorts.map((_,i)=>{let n=`${name}$cell${i}`;while(reserved.has(n))n+='$';reserved.add(n);return n})
  const terms=coords.map(name=>({op:'var',name} as E)),packed=terms.slice(1).reduce<E>((a,b)=>({op:'add',a:{op:'mul',k:layout.radix,a},b}),terms[0]!)
  const rewrite=(x:unknown):unknown=>{if(Array.isArray(x))return x.map(rewrite);if(!x||typeof x!=='object')return x;const o=x as Record<string,unknown>,key=o.key as E|undefined;if(o.op==='get'&&key?.op==='var'&&key.name===name)return {...o,key:packed};return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,rewrite(v)]))}
  holds=rewrite(holds) as Law['holds'];bindings[name]=coords;names.push(...coords)
 }
 return {law:Object.keys(bindings).length?{...law,forall:names[0],keys:names.slice(1),holds}:law,bindings}
}
