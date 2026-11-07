import {readFileSync} from 'node:fs'
import {type Machine,type Law} from '../../core/machine.ts'
import {prepareSupport} from '../../core/count-support.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../../kernel/prove.ts'
const dir=process.argv[2]!,data=JSON.parse(readFileSync(dir+'/production.json','utf8')) as {machine:Machine,laws:Law[]},header=JSON.parse(readFileSync(dir+'/core-header.json','utf8')) as {coreNames:string[]},m=data.machine
for(const label of ['core','all']){
 const laws=label==='core'?data.laws.filter(l=>header.coreNames.includes(l.name)):data.laws,law=laws.find(l=>l.name.includes('a < c, b ≠ d'))!
 for(const pass of [0,1] as const){const start=performance.now(),p=withWall(start+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>prepareSupport(m,laws,law,{},pass)),true));console.log(JSON.stringify({label,pass,seedCount:p.seedCount,ms:performance.now()-start,work:p.generationWork.work,at:Object.fromEntries(Object.entries(p.at).map(([n,ts])=>[n,ts])),phases:p.generationWork.phases}))}
}
