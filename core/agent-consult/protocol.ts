import {createHash} from 'node:crypto'
import type {Machine, E, C, Law} from '../../core/machine.ts'

export type Tool = 'prove' | 'why_not' | 'suggest' | 'check_change' | 'status' | 'check'
export type Unit = {unit:string, rule:Machine}
export type Budget = {work:number, apiCalls:number, depth:number, bound:number, candidates:number}
export type Request = {tool:Tool, file?:string, unit?:string, revision?:string, subject?:Unit, before?:Unit, after?:Unit, laws?:Law[], nearMisses?:Law[], budget:Budget}
export type Json = null | boolean | number | string | Json[] | {[key:string]:Json}
export class Refusal extends Error {
  constructor(readonly code:string, readonly fix:string, message:string) { super(message); this.name='Refusal' }
}
export function refuse(code:string,fix:string,message:string):never{throw new Refusal(code,fix,message)}
export const canonical=(x:unknown):string=>JSON.stringify(x,(_k,v)=>typeof v==='bigint'?v.toString():v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v)
export const digest=(x:unknown):string=>createHash('sha256').update(canonical(x)).digest('hex')
export const revision=(u:Unit,laws:Law[])=>digest({rule:u.rule,laws})
function object(v:unknown,path:string,keys:string[]):Record<string,unknown>{
  if(!v||typeof v!=='object'||Array.isArray(v))return refuse('invalid-input',`Supply an object at ${path}.`,`${path} must be an object`)
  for(const k of Object.keys(v))if(!keys.includes(k))refuse('unsupported-field',`Remove ${path}.${k}; supported fields: ${keys.join(', ')}.`,`Unsupported field ${path}.${k}`)
  return v as Record<string,unknown>
}
function name(v:unknown,path:string):string {
  if(typeof v!=='string'||!/^[A-Za-z_][A-Za-z0-9_]{0,63}$/.test(v)||v in Object.prototype||v.startsWith('a_')||v.startsWith('b_'))return refuse('unsupported-name',`Use a unique ordinary identifier at ${path}, without a_/b_ prefixes or prototype names.`,`Unsupported identifier at ${path}`)
  return v
}
function integer(v:unknown,path:string,min=0,max=1_000_000):number {if(typeof v!=='number'||!Number.isSafeInteger(v)||v<min||v>max)return refuse('invalid-bound',`Use an integer ${min}..${max} at ${path}.`,`Invalid numeric bound at ${path}`);return v}
function names(v:unknown,path:string):string[]{if(!Array.isArray(v)||v.length>6)refuse('unsupported-shape',`Supply at most six names at ${path}.`,`${path} is not a supported scalar name list`);return (v as unknown[]).map((x,i)=>name(x,`${path}[${i}]`))}
function text(v:unknown,path:string):string{if(typeof v!=='string'||!v.length||v.length>160||v.split('').some(c=>c.charCodeAt(0)<32))refuse('invalid-input',`Supply 1..160 printable characters at ${path}.`,`Invalid text at ${path}`);return v as string}
function expression(v:unknown,allowed:Set<string>,path:string,depth=0,nodes={n:0}):E {
  if(depth>16||++nodes.n>256)refuse('input-budget-exceeded','Reduce expression depth to16 and nodes to256.','Expression exceeds the structural budget')
  const p=v as Record<string,unknown>, op=p?.op
  const child=(x:unknown,k:string)=>expression(x,allowed,`${path}.${k}`,depth+1,nodes)
  if(op==='var'){object(v,path,['op','name']);const n=name(p.name,path+'.name');if(!allowed.has(n))refuse('unbound-name',`Declare ${n} in the relevant state/parameter/input scope.`,`Unbound name ${n}`);return {op,name:n}}
  if(op==='const'){object(v,path,['op','value']);return {op,value:integer(p.value,path+'.value',0,Number.MAX_SAFE_INTEGER)}}
  if(op==='add'||op==='sub'||op==='min'||op==='max'){object(v,path,['op','a','b']);return {op,a:child(p.a,'a'),b:child(p.b,'b')}}
  if(op==='mul'){object(v,path,['op','k','a']);return {op,k:integer(p.k,path+'.k',0,1000),a:child(p.a,'a')}}
  if(op==='if'){object(v,path,['op','c','then','else']);return {op,c:condition(p.c,allowed,path+'.c',depth+1,nodes),then:child(p.then,'then'),else:child(p.else,'else')}}
  return refuse('unsupported-expression','Use scalar natural var/const/add/sub/min/max/mul/if AST. Functions, maps, code and external calls are not supported by this prototype.',`Unsupported expression at ${path}`)
}
function condition(v:unknown,allowed:Set<string>,path:string,depth=0,nodes={n:0}):C {
  if(depth>16||++nodes.n>256)refuse('input-budget-exceeded','Reduce condition depth to16 and nodes to256.','Condition exceeds the structural budget')
  const p=v as Record<string,unknown>,op=p?.op
  if(op==='<'||op==='<='||op==='='){object(v,path,['op','a','b']);return {op,a:expression(p.a,allowed,path+'.a',depth+1,nodes),b:expression(p.b,allowed,path+'.b',depth+1,nodes)}}
  if(op==='and'||op==='or'){object(v,path,['op','xs']);if(!Array.isArray(p.xs)||p.xs.length>16)refuse('unsupported-shape','Use at most16 conditions in xs.','Invalid condition list');return {op,xs:(p.xs as unknown[]).map((x,i)=>condition(x,allowed,`${path}.xs[${i}]`,depth+1,nodes))}}
  if(op==='not'){object(v,path,['op','x']);return {op,x:condition(p.x,allowed,path+'.x',depth+1,nodes)}}
  return refuse('unsupported-condition','Use scalar comparisons, and/or/not; quantified/maps/functions need a later validated surface.',`Unsupported condition at ${path}`)
}
function unit(v:unknown,path:string):Unit {
  const u=object(v,path,['unit','rule']), id=name(u.unit,path+'.unit'),r=object(u.rule,path+'.rule',['name','params','inputs','state','step','pre','assume'])
  const params=names(r.params,path+'.rule.params'), inputs=names(r.inputs,path+'.rule.inputs'),state=object(r.state,path+'.rule.state',Object.keys((r.state??{}) as object)), stateNames=Object.keys(state).map(k=>name(k,path+'.rule.state'))
  if(!stateNames.length||stateNames.length>6||params.length>3||inputs.length>3)refuse('unsupported-shape','Use1..6 scalar state fields and at most3 params/inputs.','Prototype scalar size exceeded')
  const all=[...params,...inputs,...stateNames];if(new Set(all).size!==all.length)refuse('ambiguous-name','Give each state, parameter and input a distinct name.','Variable names overlap')
  const step=object(r.step,path+'.rule.step',['state']),changes=object(step.state,path+'.rule.step.state',stateNames)
  const initial=Object.fromEntries(stateNames.map(k=>[k,expression(state[k],new Set(params),`${path}.rule.state.${k}`)]))
  const update=Object.fromEntries(Object.entries(changes).map(([k,x])=>[k,expression(x,new Set(all),`${path}.rule.step.state.${k}`)]))
  return {unit:id,rule:{name:text(r.name,path+'.rule.name'),params,inputs,state:initial,step:{state:update},...(r.pre===undefined?{}:{pre:condition(r.pre,new Set(params),path+'.rule.pre')}),...(r.assume===undefined?{}:{assume:condition(r.assume,new Set(all),path+'.rule.assume')})}}
}
function laws(v:unknown,u:Unit,path:string):Law[]{if(!Array.isArray(v)||v.length<1||v.length>8)refuse('invalid-laws',`Supply1..8 named laws at ${path}.`,'Empty or oversized law list');const seen=new Set<string>();return (v as unknown[]).map((x,i)=>{const p=object(x,`${path}[${i}]`,['name','holds']),n=text(p.name,`${path}[${i}].name`);if(seen.has(n))refuse('duplicate-law','Use a unique name for each law.',`Repeated law ${n}`);seen.add(n);return {name:n,holds:condition(p.holds,new Set([...u.rule.params,...Object.keys(u.rule.state)]),`${path}[${i}].holds`)}})}
export function parseRequest(tool:unknown,value:unknown):Request {
  if(!['prove','why_not','suggest','check_change','status','check'].includes(tool as string))refuse('unknown-tool','Choose prove, why_not, suggest, check_change, status or check.','Unknown tool')
  const t=tool as Tool, p=object(value,'arguments',t==='check'?['file','budget']:t==='status'?['unit','revision']:t==='check_change'?['before','after','laws','budget']:['subject','laws','nearMisses','budget'])
  const b=object(p.budget??{},'budget',['work','apiCalls','depth','bound','candidates'])
  const budget={work:integer(b.work??500_000,'budget.work',0,5_000_000),apiCalls:integer(b.apiCalls??24,'budget.apiCalls',0,64),depth:integer(b.depth??3,'budget.depth',0,4),bound:integer(b.bound??2,'budget.bound',0,3),candidates:integer(b.candidates??64,'budget.candidates',1,256)}
  if(t==='check'){if(typeof p.file!=='string'||!p.file.length||p.file.length>4096||Array.from(p.file).some(c=>c.charCodeAt(0)<32))refuse('invalid-file','Supply an absolute local regular-file path under a server-configured root.','Invalid workspace file');return {tool:t,file:p.file as string,budget}}
  if(t==='status'){const rev=p.revision;if(typeof rev!=='string'||!/^[a-f0-9]{64}$/.test(rev))refuse('missing-revision','Pass the revision digest returned by prove/check_change.','Status requires an exact revision');return {tool:t,unit:name(p.unit,'unit'),revision:rev as string,budget}}
  if(t==='check_change'){const before=unit(p.before,'before'),after=unit(p.after,'after');if(before.unit!==after.unit||canonical(before.rule.params)!==canonical(after.rule.params)||canonical(before.rule.inputs)!==canonical(after.rule.inputs)||canonical(Object.keys(before.rule.state).sort())!==canonical(Object.keys(after.rule.state).sort()))refuse('unsupported-correspondence','Use matching unit/state/parameter/input names; explicit renaming relations are not supported in the prototype.','Cannot infer revision correspondence');const ls=laws(p.laws,before,'laws');return {tool:t,before,after,laws:ls,budget}}
  const subject=unit(p.subject,'subject'),ls=laws(p.laws,subject,'laws')
  if(t!=='suggest'&&p.nearMisses!==undefined)refuse('unsupported-field','Pass nearMisses only to suggest.','nearMisses is not valid for this tool')
  return {tool:t,subject,laws:ls,budget,...(p.nearMisses===undefined?{}:{nearMisses:laws(p.nearMisses,subject,'nearMisses')})}
}
export const toolNames:Tool[]=['prove','why_not','suggest','check_change','status','check']
export const toolDescriptions:Record<Tool,string>={check:'Execute the CLI engine on Python/plain TypeScript in server-configured trusted roots. Executes project code, not an OS sandbox. No roots means refused.',prove:'Check scalar natural rule laws with existing kernel proofs; only checked proofs are proven.',why_not:'Find an existing interpreter-checked shortest counterexample within explicit finite depth/value bounds.',suggest:'Call inferLaws and check supplied near-miss candidates; return pasteable source and real bounded counterexamples.',check_change:'Compare two revisions against the same laws and existing compose refinement; distinguish lost proof from a real counterexample.',status:'Read evidence observed by this process for an exact unit/revision; never trust a caller-supplied label.'}
// Never silently turn a diagnostic Infinity/NaN into JSON null. Exact integer
// diagnostics are tagged; inputs still accept only validated natural literals.
export function wireJSON(value:unknown):string {
  const encoded=JSON.stringify(value,(_key,v:unknown)=>{
    if(typeof v==='number'&&!Number.isFinite(v))refuse('nonfinite-output','Reduce/split the numeric example or use a separately validated exact-number surface.','An engine result contains a nonfinite number; no JSON result was published.')
    return typeof v==='bigint'?{type:'bigint',decimal:v.toString()}:v
  })
  if(encoded===undefined)refuse('unsupported-output','Request a supported data result.','The result is not JSON serializable.')
  return encoded
}

const idSchema={type:'string',pattern:'^[A-Za-z_][A-Za-z0-9_]{0,63}$'}
const obj=(properties:Record<string,unknown>,required=Object.keys(properties))=>({type:'object',additionalProperties:false,properties,required})
const ref=(name:string)=>({$ref:`#/$defs/${name}`})
const defs={
  term:{oneOf:[obj({op:{const:'var'},name:idSchema}),obj({op:{const:'const'},value:{type:'integer',minimum:0,maximum:Number.MAX_SAFE_INTEGER}}),obj({op:{enum:['add','sub','min','max']},a:ref('term'),b:ref('term')}),obj({op:{const:'mul'},k:{type:'integer',minimum:0,maximum:1000},a:ref('term')}),obj({op:{const:'if'},c:ref('condition'),then:ref('term'),else:ref('term')})]},
  condition:{oneOf:[obj({op:{enum:['<','<=','=']},a:ref('term'),b:ref('term')}),obj({op:{enum:['and','or']},xs:{type:'array',maxItems:16,items:ref('condition')}}),obj({op:{const:'not'},x:ref('condition')})]},
  unit:obj({unit:idSchema,rule:obj({name:{type:'string',minLength:1,maxLength:160},params:{type:'array',maxItems:3,uniqueItems:true,items:idSchema},inputs:{type:'array',maxItems:3,uniqueItems:true,items:idSchema},state:{type:'object',minProperties:1,maxProperties:6,additionalProperties:ref('term')},step:obj({state:{type:'object',maxProperties:6,additionalProperties:ref('term')}}),pre:ref('condition'),assume:ref('condition')},['name','params','inputs','state','step'])}),
  laws:{type:'array',minItems:1,maxItems:8,items:obj({name:{type:'string',minLength:1,maxLength:160},holds:ref('condition')})},
  budget:obj({work:{type:'integer',minimum:0,maximum:5000000,default:500000},apiCalls:{type:'integer',minimum:0,maximum:64,default:24},depth:{type:'integer',minimum:0,maximum:4,default:3},bound:{type:'integer',minimum:0,maximum:3,default:2},candidates:{type:'integer',minimum:1,maximum:256,default:64}},[]),
}
export const inputSchema=(tool:Tool)=>tool==='check'?{$defs:defs,...obj({file:{type:'string',minLength:1,maxLength:4096},budget:ref('budget')},['file'])}:tool==='status'?obj({unit:idSchema,revision:{type:'string',pattern:'^[a-f0-9]{64}$'}}):{$defs:defs,...obj(tool==='check_change'?{before:ref('unit'),after:ref('unit'),laws:ref('laws'),budget:ref('budget')}:{subject:ref('unit'),laws:ref('laws'),...(tool==='suggest'?{nearMisses:ref('laws')}:{}),budget:ref('budget')},tool==='check_change'?['before','after','laws']:['subject','laws'])}
