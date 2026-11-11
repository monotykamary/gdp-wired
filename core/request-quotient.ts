// Untrusted sampling optimization. A class is used only AFTER one member has
// produced a state. Refusals are never generalized; the original request order,
// logical trial allowance and first successful witness remain unchanged.
import {type C,type E,type Machine,type Request,walk} from './machine.ts'
import {coreMeter} from './meter.ts'
import {completeWorkProfile} from './work-profile.ts'
import {checkWall} from './wall.ts'

class UnsupportedQuotient extends Error {}
type Fixed=Readonly<Record<string,number>>
type Bound=ReadonlySet<string>
export type RequestQuotient={classes:Uint32Array,count:number,selector?:string,reads:ReadonlyMap<number|undefined,readonly string[]>}

export function requestQuotient(m:Machine,requests:readonly Request[]):RequestQuotient|undefined{
 if(requests.length<2||Object.keys(m.fns??{}).length||m.history||m.leasts||Object.keys(m.sums??{}).length)return undefined
 const names=[...m.inputs,...m.inputMaps??[]],inputs=new Set(m.inputs),maps=new Set(m.inputMaps??[])
 // Ambiguous namespaces and non-topological flags use the unmodified sampler.
 if(new Set(names).size!==names.length||names.some(n=>n.startsWith('?')||m.params.includes(n)||Object.hasOwn(m.state,n))||[...maps].some(n=>Object.hasOwn(m.maps??{},n)||Object.hasOwn(m.counts??{},n)))return undefined
 let work=0
 const tick=()=>{if(completeWorkProfile.enabled)coreMeter.ticks++;if((++work&255)===0)checkWall('request quotient')}
 const flags=m.step.flags??{},known=new Set<string>(),tags=new Map<string,Set<number>>()
 let supported=true
 walk([m.step,m.counts],o=>{
  tick();if(o.op==='var'&&String(o.name).startsWith('?'))supported=false
  if(o.op==='all'&&[o.key,...(o.keys as string[]|undefined)??[]].some(name=>String(name).startsWith('?')))supported=false
 })
 for(const count of Object.values(m.counts??{}))walk(count,o=>{tick();if(o.op==='flag')supported=false})
 if(Object.values(m.step.maps??{}).some(w=>'each'in w&&w.each.startsWith('?')))supported=false
 for(const[name,c]of Object.entries(flags)){
  walk(c,o=>{tick();if(o.op==='flag'&&!known.has(String(o.name)))supported=false})
  known.add(name)
 }
 if(!supported)return undefined
 walk(m.step,o=>{
  tick();if(o.op!=='=')return
  const a=o.a as E,b=o.b as E,v=a.op==='var'?a:b,k=a.op==='var'?b:a
  if(v.op==='var'&&k.op==='const'&&inputs.has(v.name)&&Number.isSafeInteger(k.value)){
   let values=tags.get(v.name);if(!values)tags.set(v.name,(values=new Set()));values.add(k.value)
  }
 })
 const selector=[...tags].filter(([,values])=>values.size>1).sort((a,b)=>b[1].size-a[1].size||m.inputs.indexOf(a[0])-m.inputs.indexOf(b[0]))[0]?.[0]
 const empty:Bound=new Set(),reads=new Map<number|undefined,readonly string[]>()
 const number=(e:E,fixed:Fixed,bound:Bound):number|undefined=>{
  tick();let out:number|undefined
  switch(e.op){
   case'const':out=e.value;break
   case'var':out=bound.has(e.name)?undefined:fixed[e.name];break
   case'if':{const c=boolean(e.c,fixed,bound,new Set());return c===undefined?undefined:number(c?e.then:e.else,fixed,bound)}
   case'get':case'tup':case'proj':return undefined
   case'mul':{const a=number(e.a,fixed,bound);out=a===undefined?undefined:e.k*a;break}
   case'add':case'sub':case'min':case'max':case'prod':{const a=number(e.a,fixed,bound),b=number(e.b,fixed,bound);if(a===undefined||b===undefined)return undefined
    out=e.op==='add'?a+b:e.op==='sub'?Math.max(0,a-b):e.op==='min'?Math.min(a,b):e.op==='max'?Math.max(a,b):a*b
   }
  }
  return out!==undefined&&Number.isSafeInteger(out)&&out>=0?out:undefined
 }
 const boolean=(c:C,fixed:Fixed,bound:Bound,visiting:Set<string>):boolean|undefined=>{
  tick()
  switch(c.op){
   case'flag':{if(visiting.has(c.name)||!flags[c.name])throw new UnsupportedQuotient('flag');const next=new Set(visiting);next.add(c.name);return boolean(flags[c.name]!,fixed,empty,next)}
   case'all':return undefined
   case'not':{const a=boolean(c.x,fixed,bound,visiting);return a===undefined?undefined:!a}
   case'and':case'or':{let unknown=false;for(const x of c.xs){const a=boolean(x,fixed,bound,visiting);if(a===(c.op==='or'))return a;if(a===undefined)unknown=true}return unknown?undefined:c.op==='and'}
   case'=':case'<':case'<=':{const a=number(c.a,fixed,bound),b=number(c.b,fixed,bound);return a===undefined||b===undefined?undefined:c.op==='='?a===b:c.op==='<'?a<b:a<=b}
  }
 }
 const projection=(value:number|undefined):readonly string[]=>{
  const cached=reads.get(value);if(cached)return cached
  const fixed:Fixed=selector?{[selector]:value!}:{},out=new Set<string>(),visiting=new Set<string>()
  const expr=(e:E,bound:Bound):void=>{
   tick()
   switch(e.op){
    case'const':return
    case'var':if(!bound.has(e.name)&&inputs.has(e.name)&&!Object.hasOwn(fixed,e.name))out.add(e.name);return
    case'if':{const c=boolean(e.c,fixed,bound,new Set());if(c!==undefined){expr(c?e.then:e.else,bound);return}cond(e.c,bound);expr(e.then,bound);expr(e.else,bound);return}
    case'get':{
     expr(e.key,bound);if(maps.has(e.map))out.add(e.map)
     const count=m.counts?.[e.map]
     // A derived count has memoized, not complete, enumerable support in
     // the runtime. Never quotient its reads under a quantified/bulk binder.
     if(count&&bound.size)throw new UnsupportedQuotient('count under binder')
     if(count){const tag='count:'+e.map;if(visiting.has(tag))throw new UnsupportedQuotient('count cycle');visiting.add(tag)
      const inner=new Set([count.j,count.key,...count.lo?[count.lo]:[]]);expr(count.below,new Set([count.j,...count.lo?[count.lo]:[]]));expr(count.body,inner);visiting.delete(tag)}
     return
    }
    case'mul':case'proj':expr(e.a,bound);return
    case'add':case'sub':case'min':case'max':case'prod':case'tup':expr(e.a,bound);expr(e.b,bound)
   }
  }
  const cond=(c:C,bound:Bound):void=>{
   tick();if(boolean(c,fixed,bound,new Set())!==undefined)return
   switch(c.op){
    case'flag':{const tag='flag:'+c.name;if(visiting.has(tag)||!flags[c.name])throw new UnsupportedQuotient('flag');visiting.add(tag);cond(flags[c.name]!,empty);visiting.delete(tag);return}
    case'all':
     // For one plain key, any past-the-support key has the same observations:
     // every bound-key read is a map's default (opaque/count maps are excluded).
     // Keep the conservative full support for cross-key quantifiers.
     if(c.keys?.length)for(const name of maps)out.add(name)
     cond(c.c,new Set([...bound,c.key,...c.keys??[]]));return
    case'not':cond(c.x,bound);return
    case'and':case'or':for(const x of c.xs)cond(x,bound);return
    case'=':case'<':case'<=':expr(c.a,bound);expr(c.b,bound)
   }
  }
  for(const e of Object.values(m.step.state??{}))expr(e,empty)
  for(const w of Object.values(m.step.maps??{})){
   if('each'in w)expr(w.value,new Set([w.each]))
   else{expr(w.key,empty);expr(w.value,empty)}
  }
  // The slice tag is part of the class even if the selected arm is a no-op.
  const ordered=names.filter(name=>out.has(name));reads.set(value,ordered);return ordered
 }
 const tokens=new WeakMap<object,string>()
 const mapToken=(value:Request[string]):string=>{
  if(!(value instanceof Map))throw new UnsupportedQuotient('non-map request')
  const cached=tokens.get(value);if(cached!==undefined)return cached
  const entries=[...value] as [number,number][]
  for(const[k,v]of entries){tick();if(!Number.isSafeInteger(k)||k<0||!Number.isSafeInteger(v)||v<0)throw new UnsupportedQuotient('non-natural request map')}
  entries.sort((a,b)=>a[0]-b[0]);const token=JSON.stringify(entries);tokens.set(value,token);return token
 }
 try{
  const ids=new Map<string,number>(),classes=new Uint32Array(requests.length)
  for(let i=0;i<requests.length;i++){
   tick();const request=requests[i]!,value=selector?request[selector]:undefined
   if(selector&&(typeof value!=='number'||!Number.isSafeInteger(value)||value<0))return undefined
   const fields=projection(value as number|undefined),parts:(number|string|undefined)[]=[value as number|undefined]
   for(const name of fields){tick();const v=request[name];if(maps.has(name))parts.push(mapToken(v!));else{if(typeof v!=='number'||!Number.isSafeInteger(v)||v<0)return undefined;parts.push(v)}}
   const key=JSON.stringify(parts);let id=ids.get(key);if(id===undefined){id=ids.size;ids.set(key,id)}classes[i]=id
  }
  checkWall('request quotient complete')
  return ids.size<requests.length?{classes,count:ids.size,selector,reads}:undefined
 }catch(error){if(error instanceof UnsupportedQuotient)return undefined;throw error}
}
