// Generation-only replay of the original admission path. No proof query runs.
import {readFileSync} from 'node:fs'
import {protocols} from '../protocols/ic3syn/models.ts'
import {candidates,guardLaws,cprof} from '../../core/counts.ts'
import {smallOf,trueSmall} from '../../core/exists.ts'
import {counted,clock,fullRate,withWall,queryHook} from '../../kernel/prove.ts'
import type {Law} from '../../core/machine.ts'
const t0=performance.now(),phases:Record<string,number>={}
const time=<T>(key:string,f:()=>T)=>{const t=performance.now();try{return f()}finally{phases[key]=performance.now()-t}}
let queries=0;queryHook.on=()=>{queries++}
const protocol=protocols.find(p=>p.id==='paxos_epr')!
const r=time('model',()=>protocol.make()),caller=time('callerLaws',()=>[...r.kindLaws(),...protocol.laws(r)])
const g=time('guardLaws',()=>guardLaws(r.machine)),m={...r.machine,counts:{...r.machine.counts,...g.counts}}
time('smallWarmup',()=>smallOf(m))
const actual=withWall(performance.now()+60000,()=>counted(fullRate,()=>{
 time('callerSmallFilter',()=>{if(!caller.every(l=>trueSmall(m,[l])))throw Error('caller small filter failed')})
 return [...caller,...time('candidateGenerationAndSmallFiltering',()=>candidates(r.machine,m,caller,caller,g.laws,60000,clock()+60000))]
},true))
const generationWallMs=performance.now()-t0
const reference=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {laws:Law[]}
const canonical=(l:Law)=>{const ns=[l.forall,...(l.keys??[])].filter((n):n is string=>!!n),ks=new Map(ns.map((n,i)=>[n,'B'+i]));const walk=(v:unknown):unknown=>Array.isArray(v)?v.map(walk):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,x])=>[k,k==='name'&&typeof x==='string'?ks.get(x)??x:walk(x)])):v;return JSON.stringify(walk(l.holds))}
const family=[2,3,4,7,9,10,11,13,14,17,33,45,61,64,66,70,71,73,74].map(index=>({index,matched:actual.some(l=>canonical(l)===canonical(reference.laws[index]!))}))
console.log(JSON.stringify({generationWallMs,phases,cprof,rootQueries:queries,candidates:actual.length,family19:family.filter(x=>x.matched).length,family,scope:'isolated current-source generation path, not a retrospective timing of the 89.328s capture'}))
if(queries||family.some(x=>!x.matched))throw Error('generation-only contract failed')
