// Native tuple ghosts are untrusted proposals; the complete native family must check.
import type {C,E,Law,Machine,SomeWitness} from '../../core/machine.ts'
import type {Ghosted} from '../../kernel/kernel.ts'
import type {SeedBindings,SeedLayout} from './candidate-seed-restatement.ts'
import type {RetainedWitnessContext,WitnessSeedProposal} from './candidate-seed-witness.ts'
import {abstractWitnessValues} from './witness-value-proxies.ts'
export type NativeGhostBinding={sorts:string[],valueSort:string}
const same=(a:unknown,b:unknown)=>JSON.stringify(a)===JSON.stringify(b)
const parts=(e:E):E[]=>e.op==='tup'?[e.a,...parts(e.b)]:[e]
const tuple=(es:E[]):E=>es.length===1?es[0]!:{op:'tup',a:es[0]!,b:tuple(es.slice(1))}
export function adaptNativeGhostSeeds(source:RetainedWitnessContext,target:Machine,publicLaws:Law[],config:SeedBindings,specs:Record<string,NativeGhostBinding>):WitnessSeedProposal {
 if(!source?.G||!same(source.original,source.G.orig)||Object.keys(source.G.vars).length)throw Error('unsupported native ghost producer')
 if(!same(Object.keys(source.G.maps).sort(),Object.keys(specs).sort()))throw Error('native ghost bindings must cover the complete producer')
 const radices=new Set(Object.values(config.maps).map(m=>m.radix)),radix=[...radices][0]
 if(radices.size!==1||!Number.isSafeInteger(radix)||radix!<2)throw Error('ambiguous native ghost source radix')
 const reserved=new Set([...target.params,...target.inputs,...Object.keys(target.state),...Object.keys(target.maps??{}),...(target.inputMaps??[]),...Object.keys(target.step.flags??{}),...Object.keys(target.counts??{}),...Object.keys(target.fns??{})])
 for(const l of publicLaws)for(const n of [l.forall,...(l.keys??[]),...(l.some??[])])if(n)reserved.add(n)
 const aliases:Record<string,string>=Object.create(null),valueSorts:Record<string,string>=Object.create(null),layouts:Record<string,SeedLayout>={...config.maps}
 for(const [name,spec] of Object.entries(specs)){
  if(!Array.isArray(spec.sorts)||!spec.sorts.length||[...spec.sorts,spec.valueSort].some(s=>!config.domains[s]||!target.params.includes(config.domains[s]!)))throw Error('invalid native ghost sort')
  let alias=`seed$witness$${name}`;while(reserved.has(alias))alias+='$';reserved.add(alias);aliases[name]=alias
  valueSorts[name]=spec.valueSort;layouts[name]={target:alias,sorts:spec.sorts,radix:radix!}
 }
 for(const l of Object.values(config.maps))if(!Object.hasOwn(target.maps??{},l.target)||target.relations?.[l.target]&&!same(target.relations[l.target],l.sorts))throw Error('native ghost target layout mismatch')
 const inputSorts:Record<string,string>=Object.create(null)
 for(const [name,w] of Object.entries(target.step.maps??{})){
  const l=Object.values(config.maps).find(l=>l.target===name);if(!l||!('key'in w))continue
  const ps=parts(w.key);if(ps.length!==l.sorts.length)throw Error('native input tuple arity mismatch')
  ps.forEach((p,i)=>{if(p.op==='var'&&target.inputs.includes(p.name)){const s=l.sorts[i]!;if(inputSorts[p.name]&&inputSorts[p.name]!==s)throw Error('conflicting native input role');inputSorts[p.name]=s}})
 }
 const allowed=new Set([...target.params,...target.inputs,...Object.keys(target.state)])
 const term=(e:E,rename:Record<string,string>={}):E=>{
  switch(e.op){
   case 'var':{const name=rename[e.name]??e.name;if(!rename[e.name]&&!allowed.has(name))throw Error(`unmapped native ghost variable ${name}`);return{op:'var',name}}
   case 'const':if(!Number.isSafeInteger(e.value)||e.value<0)throw Error('invalid native ghost constant');return e
   case 'get':{const l=layouts[e.map];if(!l)throw Error(`unmapped native ghost map ${e.map}`);const ps=parts(e.key);if(ps.length!==l.sorts.length||ps.some(p=>p.op==='tup'))throw Error('native ghost key arity/association mismatch');return{op:'get',map:l.target,key:tuple(ps.map(p=>term(p,rename)))}}
   case 'if':return{...e,c:cond(e.c,rename),then:term(e.then,rename),else:term(e.else,rename)}
   case 'mul':if(!Number.isSafeInteger(e.k)||e.k<0)throw Error('invalid native ghost multiplier');return{...e,a:term(e.a,rename)}
   case 'proj':throw Error('unsupported native ghost projection')
   case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':return{...e,a:term(e.a,rename),b:term(e.b,rename)}
  }
 }
 const cond=(c:C,rename:Record<string,string>={}):C=>{
  switch(c.op){
   case 'flag':if(!Object.hasOwn(target.step.flags??{},c.name))throw Error(`unmapped native ghost flag ${c.name}`);return c
   case 'all':throw Error('quantified native ghost update unsupported')
   case 'not':return{...c,x:cond(c.x,rename)}
   case 'and':case 'or':return{...c,xs:c.xs.map(x=>cond(x,rename))}
   case '<':case '<=':case '=':{const s=c.a.op==='var'?inputSorts[c.a.name]:undefined;return{...c,a:term(c.a,rename),b:c.op==='<'&&c.b.op==='const'&&c.b.value===radix&&s?{op:'var',name:config.domains[s]!}:term(c.b,rename)}}
  }
 }
 const maps:Ghosted['maps']=Object.create(null)
 for(const [name,g] of Object.entries(source.G.maps)){
  if(g.start!==0||!('key'in g.write))throw Error('native ghost requires a zero-start point update')
  const ps=parts(g.write.key),spec=specs[name]!
  if(ps.length!==spec.sorts.length||ps.some((p,i)=>p.op!=='var'||inputSorts[p.name]!==spec.sorts[i]))throw Error('native ghost point key roles mismatch')
  maps[aliases[name]!]={start:0,write:{key:tuple(ps.map(p=>term(p))),value:term(g.write.value)}}
 }
 const roles=(law:Law,native:boolean)=>{
  const found=new Map<string,Set<string>>()
  const visit=(x:unknown):void=>{if(Array.isArray(x)){x.forEach(visit);return}if(!x||typeof x!=='object')return;const o=x as any
   if(o.op==='get'){const l=native?Object.values(config.maps).find(l=>l.target===o.map):config.maps[o.map];if(l){const ps=parts(o.key);if(ps.length!==l.sorts.length)throw Error('public native tuple layout mismatch');ps.forEach((p,i)=>{if(p.op==='var'){const set=found.get(p.name)??new Set<string>();set.add(`${l.target}:${i}`);found.set(p.name,set)}})}}
   Object.values(o).forEach(visit)
  };visit(law.holds)
  return (name:string)=>[...(found.get(name)??[])].sort().join('|')
 }
 const witnesses:Record<string,SomeWitness>=Object.create(null),audit:WitnessSeedProposal['audit']=[]
 for(const to of publicLaws){
  const froms=source.laws.filter(l=>l.name===to.name),from=froms[0]
  if(froms.length!==1||!from?.some?.length||from.some.length!==to.some?.length)throw Error('native public existential mismatch')
  const oldKeys=[from.forall,...(from.keys??[])].filter((n):n is string=>!!n),newKeys=[to.forall,...(to.keys??[])].filter((n):n is string=>!!n)
  if(oldKeys.length!==newKeys.length)throw Error('native public key scope mismatch')
  const fr=roles(from,false),tr=roles(to,true),rename:Record<string,string>=Object.create(null)
  const match=(olds:string[],news:string[])=>olds.map(old=>{const role=fr(old),hits=news.filter(n=>role&&tr(n)===role);if(hits.length!==1)throw Error('ambiguous native existential coordinate role');return[old,hits[0]!] as const})
  for(const [old,next]of match(oldKeys,newKeys))rename[old]=next
  const sub=source.plains[to.name]?.sub;if(!sub||Object.keys(sub).length!==from.some.length)throw Error('native witness terms absent')
  const terms:Record<string,E>=Object.create(null)
  for(const [old,next]of match(from.some,to.some!)){if(!sub[old])throw Error('native witness coordinate absent');terms[next]=term(sub[old]!,rename)}
  witnesses[to.name]={terms};audit.push({status:'proposed',name:to.name,sourceVariables:from.some.length,targetVariables:to.some!.length,ghostMaps:aliases,helperMode:'guarded-equality',trusted:false})
 }
 const augmented:SeedBindings={...config,maps:layouts,fields:Object.fromEntries(Object.entries(config.fields??{}).filter(([n])=>!Object.hasOwn(specs,n)))}
 const out=abstractWitnessValues(source.family,augmented,valueSorts)
 return{witnesses,ghosts:{vars:{},maps},bindings:out.bindings,laws:out.laws,audit}
}
