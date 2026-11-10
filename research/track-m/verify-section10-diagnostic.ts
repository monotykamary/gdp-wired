// Fresh-process validation of retained models, scope atoms and violated sets.
import {readFileSync} from 'node:fs'
import {termColumn} from '../../kernel/kernel.ts'
import {brokenOf} from '../../kernel/prove.ts'
const file=process.argv[2];if(!file)throw new Error('FILE required')
const r=JSON.parse(readFileSync(file,'utf8'))
for(const [i,e]of r.columns.entries())if(termColumn(e)!==`⟦${i}⟧`)throw new Error('column identity mismatch')
const valid=(g:any,path:any[],point:Record<string,number>)=>Object.values(point).every(Number.isSafeInteger)&&!brokenOf(g)(point).length&&path.every(([,a])=>{const v=Object.entries(a.lin).reduce((s,[k,z])=>s+Number(z)*(k==='1'?1:point[k]!),0);return Number.isFinite(v)&&(a.holds?v<=0:v>0)})
const c=r.production.captures.find((c:any)=>c.id===r.captureId);if(!c)throw new Error('missing selected capture')
let numericModels=0,sourceModels=0,checkedSourceReceipts=0
if(r.freshDiagnosticNumeric.valid){if(!valid(c.numeric,c.path,r.freshDiagnosticNumeric.model))throw new Error('invalid numeric model');numericModels++}
const context=r.sourceContext,ids=new Set(r.sources.map((s:any)=>s.index));if(context&&ids.size!==context.violated.length)throw new Error('source result missing')
if(context){const origin=r.production.captures.find((c:any)=>c.id===context.captureId);if(!origin||!valid(origin.numeric,context.path,context.model))throw new Error('invalid source selection model')}
for(const s of r.sources){if(!context||!context.violated.includes(s.index))throw new Error('unexpected source');const good=s.part.hyps.at(-2)?.xs?.[0];if(!good||!brokenOf({name:'candidate',hyps:[good]})(context.model).length)throw new Error('not violated');if(!Number.isFinite(s.units)||s.units<0)throw new Error('invalid units');if(s.outcome==='sat-validated'){if(!s.model||!valid(s.part,context.path,s.model))throw new Error('invalid source model');sourceModels++}else if(s.outcome==='refuted-checked'){if(s.checked!==true)throw new Error('unchecked refutation receipt');checkedSourceReceipts++}}
console.log(JSON.stringify({file,revision:r.revision,numericModels,sourceModels,checkedSourceReceipts,violated:context?.violated.length??0,sourceProofReceiptsNotReplayed:true}))
