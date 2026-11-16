import type {C,E,Law,Machine} from '../../core/machine.ts'
import {boundOf,witnessesOf} from '../../kernel/kernel.ts'
import type {GenericLiftSource} from '../lift/source.ts'
import {associativeShape} from './shape.ts'

export type Roles={sizes:string[],bound:number,base:Record<string,string>,scopes:Record<string,string>[],publicScopes:Record<string,string>[],values:Record<string,string>,coordinates:Record<string,string[]>}
const upper=(x:any)=>x&&(x.op==='<'||x.op==='<=')
const scan=(x:any,f:(x:any)=>void):void=>{if(!x||typeof x!=='object')return;f(x);for(const v of Object.values(x))if(Array.isArray(v))v.forEach(y=>scan(y,f));else scan(v,f)}
const tuple=(e:E):E[]=>e.op==='tup'?[e.a,...tuple(e.b)]:[e]

/** Parameter roles come ONLY from matching bounded source comparisons and
 * coordinate/value constraints. Relations metadata and spelling are ignored. */
export function deriveTypedRoles(source:GenericLiftSource,original:{machine:Machine,laws:Law[]},machine:Machine,laws:Law[]):Roles|null {
 const parameters=new Set(source.machine.params),sizes:string[]=[],bounds=new Set<number>()
 // Pair structurally corresponding comparisons, allowing alpha binder names.
 const paired=(a:any,b:any):void=>{
  if(!a||!b||typeof a!=='object'||typeof b!=='object')return
  if(upper(a)&&upper(b)&&a.op===b.op&&a.b?.op==='var'&&parameters.has(a.b.name)&&b.b?.op==='const'){
   if(!sizes.includes(a.b.name))sizes.push(a.b.name);bounds.add(b.b.value)
  }
  if(Array.isArray(a)&&Array.isArray(b)){a.forEach((x,i)=>paired(x,b[i]));return}
  for(const k of Object.keys(a))if(k!=='params'&&k!=='relations')paired(a[k],b[k])
 }
 paired(associativeShape(source.machine),associativeShape(original.machine));paired(associativeShape(source.laws),associativeShape(original.laws))
 if(!sizes.length)return null
 if(bounds.size!==1)throw Error('typed-bound candidate has mixed finite bounds')
 const bound=[...bounds][0]!
 if(!Number.isSafeInteger(bound)||bound<2)throw Error('unsupported typed finite bound')
 if(source.machine.params.some(p=>!sizes.includes(p))||original.machine.params.length)throw Error('unsupported independent non-bound parameters in typed candidate')
 const parent=new Map<string,string>(),labels=new Map<string,string>()
 const root=(x:string):string=>{const p=parent.get(x);if(!p){parent.set(x,x);return x}if(p===x)return x;const r=root(p);parent.set(x,r);return r}
 const join=(a:string|undefined,b:string|undefined):void=>{if(!a||!b)return;const x=root(a),y=root(b);if(x===y)return;const p=labels.get(x),q=labels.get(y);if(p&&q&&p!==q)throw Error(`ambiguous/mixed typed roles: ${p} versus ${q}`);parent.set(y,x);if(q)labels.set(x,q)}
 const seed=(x:string|undefined,p:string)=>{if(!x)throw Error('unsupported bounded expression');const r=root(x),q=labels.get(r);if(q&&q!==p)throw Error(`ambiguous/mixed typed roles: ${q} versus ${p}`);labels.set(r,p)}
 const globals=new Set([...machine.params,...machine.inputs,...Object.keys(machine.state)])
 const vars=new Map<string,Map<string,string>>(),coords=new Map<string,number>()
 const env=(s:string,boundNames:string[]=[])=>{const locals=new Set(boundNames);const table=new Map<string,string>();vars.set(s,table);return (n:string)=>{const k=locals.has(n)||!globals.has(n)?s+':'+n:'global:'+n;table.set(n,k);root(k);return k}}
 const base=env('machine')
 const expr=(e:E,v:(n:string)=>string):string|undefined=>{
  if(e.op==='var')return v(e.name)
  if(e.op==='get'){keys(e.map,e.key,v);return 'value:'+e.map}
  if(e.op==='if'){condition(e.c,v);const a=expr(e.then,v),b=expr(e.else,v);join(a,b);return a??b}
  if((e.op==='add'||e.op==='sub')&&e.b.op==='const')return expr(e.a,v)
  if(e.op==='const')return undefined
  throw Error('unsupported arithmetic in typed role coordinate: '+e.op)
 }
 const keys=(map:string,key:E,v:(n:string)=>string)=>{const ks=tuple(key),old=coords.get(map);if(old!==undefined&&old!==ks.length)throw Error('mixed tuple arity: '+map);coords.set(map,ks.length);ks.forEach((e,i)=>join('key:'+map+':'+i,expr(e,v)))}
 const condition=(c:C,v:(n:string)=>string):void=>{
  if(c.op==='all'){const q=env('quantified:'+vars.size,boundOf(c));condition(c.c,q);return}
  if(c.op==='and'||c.op==='or'){c.xs.forEach(x=>condition(x,v));return}
  if(c.op==='not'){condition(c.x,v);return}
  if(c.op==='flag')return
  const a=expr(c.a,v),b=c.b.op==='var'&&parameters.has(c.b.name)?undefined:expr(c.b,v)
  if(upper(c)&&c.b.op==='var'&&sizes.includes(c.b.name))seed(a,c.b.name)
  // Equality of identifiers/witness values constrains their sort. A numeric
  // literal carries no sort; it can be a valid default for any domain.
  else if(c.op==='=')join(a,b)
 }
 const walkMachine=(m:Machine)=>{
  if(m.pre)condition(m.pre,base);if(m.assume)condition(m.assume,base)
  Object.values(m.state).forEach(e=>expr(e,base))
  for(const [n,e]of Object.entries(m.step.state??{}))join(base(n),expr(e,base))
  for(const [n,w]of Object.entries(m.step.maps??{})){
   if('each'in w)throw Error('typed row-update mixing unsupported')
   keys(n,w.key,base);join('value:'+n,expr(w.value,base))
  }
  for(const [f,q]of Object.entries(m.step.flags??{})){
   if(q.op==='all'){
    const v=env('flag:'+f,boundOf(q));condition(q.c,v)
    witnessesOf(f,q).forEach((w,i)=>join(base(w),v(boundOf(q)[i]!)))
   }else condition(q,base)
  }
  if(m.facts?.length)throw Error('typed facts require a separate correspondence proof')
 }
 walkMachine(source.machine);walkMachine(machine)
 const sourceEnvs=source.laws.map((l,i)=>{const v=env('sourceLaw:'+i,[l.forall,...(l.keys??[]),...(l.some??[])].filter((x):x is string=>!!x));condition(l.holds,v);return v})
 const lawEnvs=laws.map((l,i)=>{const v=env('law:'+i,[l.forall,...(l.keys??[])].filter((x):x is string=>!!x));condition(l.holds,v);if(l.forall)join(v(l.forall),v(l.forall+'#'));for(const k of l.keys??[])join(v(k),v(k+'#'));return v})
 // Reading/writing the same map ties every coordinate to a single domain,
 // independent of bound-variable names and the order of the family entries.
 const label=(x:string)=>labels.get(root(x))
 const result=(table:Map<string,string>)=>Object.fromEntries([...table].flatMap(([n,x])=>label(x)?[[n,label(x)!]]:[]))
 const baseRoles=result(vars.get('machine')!)
 for(const [scope,t]of vars)if(scope.startsWith('flag:')||scope.startsWith('quantified:'))for(const [n,p]of Object.entries(result(t))){if(baseRoles[n]&&baseRoles[n]!==p)throw Error('ambiguous machine-local binder role: '+n);baseRoles[n]=p}
 const scopes=laws.map((_,i)=>({...baseRoles,...result(vars.get('law:'+i)!)}))
 const values=Object.fromEntries([...coords.keys()].flatMap(m=>label('value:'+m)?[[m,label('value:'+m)!]]:[]))
 const coordinates=Object.fromEntries([...coords].map(([m,n])=>[m,Array.from({length:n},(_,i)=>{const p=label('key:'+m+':'+i);if(!p)throw Error('unclassified tuple coordinate '+m+':'+i);return p})]))
 // Every old finite upper bound needs a unique role; do not silently leave a
 // finite remnant in a candidate whose public statement is unbounded.
 const check=(x:any,roles:Record<string,string>)=>scan(x,c=>{if(upper(c)&&c.b?.op==='const'&&c.b.value===bound){const p=c.a.op==='var'?roles[c.a.name]:c.a.op==='get'?values[c.a.map]:undefined;if(!p)throw Error('unclassified retained finite-bound expression')}})
 check(machine,baseRoles);laws.forEach((l,i)=>check(l.holds,scopes[i]!))
 // Guard against parameters inferred only from advisory metadata/unrelated laws.
 for(const p of sizes)if(!Object.values(baseRoles).includes(p)&&!scopes.some(s=>Object.values(s).includes(p)))throw Error('unused bound parameter '+p)
 void sourceEnvs;void lawEnvs
 return {sizes,bound,base:baseRoles,scopes,publicScopes:source.laws.map((_,i)=>({...baseRoles,...result(vars.get('sourceLaw:'+i)!)})),values,coordinates}
}
