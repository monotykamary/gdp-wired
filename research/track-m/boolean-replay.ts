// Direct diagnostic of one captured Boolean core; every ordering keeps the
// eight-candidate and 250-counted-ms caps and checks its tree at the source.
import {readFileSync} from 'node:fs'
import {type C,type E,walkOnce} from '../../core/machine.ts'
import {type Goal,type Path,type Tree,canon,check,linear,termColumn,truth} from '../../kernel/kernel.ts'
import {atPoint,clock,counted,fullRate,grow,rowsAt,withDeadline,withWall} from '../../kernel/prove.ts'
import {refuteFast,sub} from '../../core/solver.ts'
import {booleanCandidates,booleanCore} from './boolean-core.ts'
const fixture=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {goal:Goal,root:[string,Path extends Map<string,infer V>?V:never][],wits:string[],terms?:Record<string,E>,candidates:{c:C,score:number}[]}
if(!fixture.terms)throw new Error('Fixture lacks semantic term definitions; recapture with LAB_BOOLEAN_DUMP=1')
const names=Object.fromEntries(Object.entries(fixture.terms).map(([name,e])=>[name,termColumn(e)]))
const root:Path=new Map(fixture.root.map(([,row])=>{const lin=Object.fromEntries(Object.entries(row.lin).map(([key,value])=>[key.replace(/⟦\d+⟧/g,m=>{if(!names[m])throw new Error(`Missing term definition ${m}`);return names[m]!}),value]));return [canon(lin),{...row,lin}]})),g=fixture.goal,wits=new Set(fixture.wits)
const member=(c:C):string|undefined=>c.op==='='&&c.a.op==='get'&&c.b.op==='const'&&c.b.value===1?c.a.map:c.op==='<='&&c.a.op==='const'&&c.a.value===1&&c.b.op==='get'?c.b.map:undefined
const shared=(c:C)=>{if(c.op!=='=')return false;const a=new Set<string>(),b=new Set<string>();walkOnce(c.a,(o:any)=>{if(o.op==='var'&&wits.has(o.name))a.add(o.name)});walkOnce(c.b,(o:any)=>{if(o.op==='var'&&wits.has(o.name))b.add(o.name)});return [...a].some(w=>b.has(w))}
for(const mode of ['guided','score','members','keys']){
 const selected=[...(fixture.candidates??booleanCandidates(g,root,wits))].sort((a,b)=>{
  const rank=(c:C)=>mode==='score'?0:member(c)!==undefined?(mode==='members'?0:1):shared(c)?(mode==='keys'?0:1):2
  return rank(a.c)-rank(b.c)||b.score-a.score
 }).slice(0,8),cs=selected.flatMap(({c})=>c.op==='='?[{op:'<=' as const,a:c.a,b:c.b},{op:'<=' as const,a:c.b,b:c.a}]:[c])
 const wall=performance.now()
 const result=withWall(wall+10000,()=>counted(fullRate,()=>{
  const begin=clock(),until=begin+250;let nodes=0,last:unknown
  return withDeadline(until,()=>{
   atPoint.on=false
   if(mode==='guided'){const trace:object[]=[],tree=booleanCore(g,root,wits,until,trace);return {mode,source:!!tree,checked:!!tree&&check(g,tree,root),ms:Math.round(clock()-begin),nodes:0,choices:[],trace}}
   const go=(i:number,path:Path):Tree|undefined=>{
    if(clock()>=until)return undefined
    nodes++;const out=refuteFast(rowsAt(g,path),1000);if(out?.kind==='refuted')return {leaf:out.steps}
    if(i===cs.length){const found=grow(g,path,{nodes:0,until,units:true});if(!('tree'in found))last??={outcome:found.stuck,why:found.why,path:[...path]};return 'tree'in found?found.tree:undefined}
    const c=cs[i]!,known=truth(c,path);if(known!==undefined)return go(i+1,path)
    if(c.op!=='<'&&c.op!=='<=')return undefined
    const a=linear(c.a,path),b=linear(c.b,path);if(!a||!b)return undefined
    const split=sub(a,b);if(c.op==='<')split['1']=(split['1']??0)+1
    const id=canon(split),yes=go(i+1,new Map(path).set(id,{lin:split,holds:true})),no=yes&&go(i+1,new Map(path).set(id,{lin:split,holds:false}))
    return yes&&no?{split,yes,no}:undefined
   }
   const tree=go(0,root)
   return {mode,source:!!tree,checked:!!tree&&check(g,tree,root),last,ms:Math.round(clock()-begin),nodes,choices:cs}
  })
 },true))
 console.log(JSON.stringify({...result,wall:Math.round(performance.now()-wall)}))
}
