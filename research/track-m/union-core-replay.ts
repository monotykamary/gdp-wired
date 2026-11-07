import {readFileSync} from 'node:fs'
import {type Goal,type Path,check} from '../../kernel/kernel.ts'
import {atPoint,clock,counted,fullRate,grow,widen,withDeadline,withWall} from '../../kernel/prove.ts'
import {foldPath} from './fold-path.ts'
import {carriedCase} from './carried-case.ts'
const {goal,path}=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {goal:Goal,path:[string,Path extends Map<string,infer V>?V:never][]},root:Path=new Map(path)
const results=[]
for(const folded of [false,true])for(const carried of [false,true])for(const units of [false,true]){
 const trace:object[]=[],wall=performance.now()
 const result=withWall(wall+10000,()=>counted(fullRate,()=>{
  const start=clock(),until=start+250
  return withDeadline(until,()=>{
   atPoint.on=false
   const input=folded?foldPath(goal,root):{goal,opaque:{}},tree=carried?carriedCase(input.goal,root,['S'],new Set(['w$33']),until,trace):undefined
   const out=tree?{tree}:grow(input.goal,root,{nodes:0,until,units}),lifted='tree'in out?(folded?widen(input.goal,goal,out.tree,input.opaque,root,root):out.tree):undefined
   return {folded,carried,units,ms:Math.round(clock()-start),source:'tree'in out,checked:!!lifted&&check(goal,lifted,root),trace}
  })
 }))
 results.push({...result,wall:Math.round(performance.now()-wall)})
}
console.log(JSON.stringify(results))
