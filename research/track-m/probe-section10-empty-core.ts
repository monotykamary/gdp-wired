// Standalone diagnostic only; no change to the production empty-core branch.
import {readFileSync} from 'node:fs'
import {termColumn,check} from '../../kernel/kernel.ts'
import {counted,fullRate,fullWork,clock} from '../../kernel/prove.ts'
import {refuteFast,rowsAt,grow,widen} from '../../core/count-recovery/ops.ts'
const r=JSON.parse(readFileSync(process.argv[2]!,'utf8'))
for(const [i,e]of r.columns.entries())if(termColumn(e)!==`⟦${i}⟧`)throw new Error('column identity mismatch')
const c=r.production.captures.find((c:any)=>c.id===r.captureId),path=new Map(c.path) as any,small={name:c.numeric.name,hyps:[]},before=fullWork()
const answer=counted(fullRate,()=>{const q=refuteFast(rowsAt(small,path),256),direct=q?.kind==='refuted'?{leaf:q.steps}:undefined,out=direct?undefined:grow(small,path,{nodes:0,until:clock()+100,units:false}),tree=direct??(out&&'tree'in out?out.tree:undefined),lifted=tree&&widen(small,c.numeric,tree,{},path,path);return {method:direct?'refuteFast':'grow',tree:!!tree,smallChecked:!!tree&&check(small,tree,path),numericChecked:!!lifted&&check(c.numeric,lifted,path)}} ,true)
console.log(JSON.stringify({diagnostic:'empty-core-only',productionUnchanged:true,originalWhy:c.query.why,originalCore:c.query.core,units:(fullWork()-before)/fullRate,...answer}))
