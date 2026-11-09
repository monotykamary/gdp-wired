// Fast-loop entry: one captured goal, normal counted budget, no whole-law run.
import {readFileSync} from 'node:fs'
import {type Path,termColumn,check} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withWall} from '../../kernel/prove.ts'
const [file,budgetText='1000']=process.argv.slice(2);if(!file)throw new Error('LEAF_PACKET [UNITS] required')
const input=JSON.parse(readFileSync(file,'utf8')),packet=input.packet??input,units=Number(budgetText)
for(let i=0;i<(input.columns??[]).length;i++)if(termColumn(input.columns[i])!==`⟦${i}⟧`)throw new Error('column mismatch')
const path:Path=new Map(packet.path??[]),start=performance.now(),before=fullWork()
const result=withWall(start+30000,()=>counted(fullRate,()=>grow(packet.goal,path,{nodes:0,until:clock()+units}),true)),checked='tree'in result&&check(packet.goal,result.tree,path)
console.log(JSON.stringify({researchOnly:true,kind:packet.kind,units:(fullWork()-before)/fullRate,wallMs:performance.now()-start,checked,outcome:'tree'in result?'tree':result.stuck,why:'tree'in result?undefined:result.why,model:'tree'in result?undefined:result.witness}))
