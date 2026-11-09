// Run after install-section18, only in the disposable frozen checkout.
import {readFileSync,writeFileSync} from 'node:fs'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw Error('disposable Linux required')
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw Error('nonunique anchor: '+a);return s.replace(a,b)}
const update=(p:string,run:(s:string)=>string)=>writeFileSync(p,run(readFileSync(p,'utf8')))
const pre="import {citations as __c} from '../../research/track-m/section19-recorder.ts'\n"
update('research/track-m/section18-recorder.ts',s=>{
 s="import {citations as __c} from './section19-recorder.ts'\n"+s
 s=replace(s,'this.marks.set(tree,context)','{this.marks.set(tree,context);__c.marked(tree,context.goal,context.lemmas)}')
 s=replace(s,'if(f)f.data={...data,sourcePath:copyPath(data.sourcePath),targetPath:copyPath(data.targetPath)}','if(f){f.data={...data,sourcePath:copyPath(data.sourcePath),targetPath:copyPath(data.targetPath)};__c.emission(f,data)}')
 return replace(s,'try{return run()}finally{this.end(f)}}','try{return __c.call(name+\'-helper-return\',g,root??new Map(),run)}finally{this.end(f)}}')
})
for(const p of ['core/count-recovery/field-bound-lemmas.ts','core/count-recovery/frame-lemmas.ts'])update(p,s=>s.replaceAll('__l.mark(__lemma,{source:','__l.mark(__lemma,{cut:split,source:'))
update('core/count-recovery/derivability-closure.ts',s=>{
 s=replace(s,'__l.mark(__lemma,{source:part','__l.mark(__lemma,{cut:atom,source:part')
 s=replace(s,'export function deriveCountClosure(','function deriveCountClosureImpl(')
 s=replace(s,'function deriveCountClosureImpl(',"export const deriveCountClosure:typeof deriveCountClosureImpl=(...a)=>__c.call('closure-return',a[2],a[4],()=>deriveCountClosureImpl(...a))\nfunction deriveCountClosureImpl(")
 s=replace(s,'const atLeaf=(path:Path,end:number):Tree|undefined=>{',"const atLeaf=(path:Path,end:number):Tree|undefined=>__c.call('closure-leaf',g,path,()=>{")
 return replace(s,'\n }\n const rowTrace=','\n })\n const rowTrace=')
})
update('core/count-recovery/guard-cases.ts',s=>{
 s=pre+s
 s=replace(s,"(...args)=>wallTree('guard-case-reconstruction',()=>guardCasesImpl(...args))","(...args)=>__c.call('guard-return',args[2],args[8]??new Map(),()=>wallTree('guard-case-reconstruction',()=>guardCasesImpl(...args)))")
 s=replace(s,' const leaf=(hyps:C[],path:Path,active:boolean):Tree|undefined=>{',' const leafImpl=(hyps:C[],path:Path,active:boolean):Tree|undefined=>{')
 return replace(s,' const visit=(i:number,hyps:C[],path:Path):Tree|undefined=>{'," const leaf:typeof leafImpl=(...a)=>__c.call('guard-leaf',g,a[1],()=>leafImpl(...a))\n const visit=(i:number,hyps:C[],path:Path):Tree|undefined=>{")
})
for(const p of ['core/count-recovery/field-bound-lemmas.ts','core/count-recovery/frame-lemmas.ts','core/count-recovery/derivability-closure.ts'])update(p,s=>{
 s=pre+s;const ast=ts.createSourceFile(p,s,ts.ScriptTarget.Latest,true),edits:{a:number,b:number,text:string}[]=[]
 const visit=(n:ts.Node)=>{if(ts.isCallExpression(n)&&ts.isIdentifier(n.expression)&&['substC','piecesAt','truth','decide'].includes(n.expression.text)){edits.push({a:n.expression.getStart(ast),b:n.expression.end+1,text:`__c.transform('${n.expression.text}',${n.expression.text},[`},{a:n.end-1,b:n.end,text:'])'})}ts.forEachChild(n,visit)};visit(ast)
 for(const e of edits.sort((a,b)=>b.a-a.a))s=s.slice(0,e.a)+e.text+s.slice(e.b);return s
})
update('core/count-select.ts',s=>replace(s,"import {modelSequence} from '../kernel/model-sequence.ts'","import {modelSequence} from './count-recovery/ops.ts'"))
writeFileSync('core/count-recovery/ops.ts',pre+`import {check} from '../../kernel/kernel.ts'
import {grow as grow0,widen as widen0,rowsAt as rows0} from '../../kernel/prove.ts'
import {modelSequence as sequence0} from '../../kernel/model-sequence.ts'
import {solve as solve0,refuteFast as fast0} from '../solver.ts'
export {check}
export const grow:typeof grow0=(...a)=>__c.call('grow',a[0],a[1]??new Map(),()=>grow0(...a))
export const widen:typeof widen0=(...a)=>__c.call('transport',a[1],a[5]??a[4]??new Map(),()=>widen0(...a))
export const rowsAt:typeof rows0=(...a)=>__c.bindRows(a[0],a[1]??new Map(),()=>rows0(...a))
export const modelSequence:typeof sequence0=(...a)=>{const ask=sequence0(...a);return (...q)=>__c.call('query',q[0],a[0]??new Map(),()=>ask(...q))}
export const solve:typeof solve0=(...a)=>__c.rows('solve',a[0],()=>solve0(...a))
export const refuteFast:typeof fast0=(...a)=>__c.rows('refute-fast',a[0],()=>fast0(...a))
export const wallSpan=<T>(_phase:string,run:()=>T):T=>run()
export const wallTree=wallSpan
`)
console.log(JSON.stringify({researchOnly:true,citationTrace:true,kernelChanged:false}))
