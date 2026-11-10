// Observation-only changes, restricted to a disposable frozen Linux checkout.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw Error('disposable Linux required')
const manifest:any[]=[],hash=(s:string)=>createHash('sha256').update(s).digest('hex')
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw Error('nonunique anchor: '+a);return s.replace(a,b)}
const save=(file:string,f:(s:string)=>string)=>{const a=readFileSync(file,'utf8'),b=f(a);writeFileSync(file,b);manifest.push({file,before:hash(a),after:hash(b)})}
const prefix="import {lemmaRecorder as __l} from '../../research/track-m/section18-recorder.ts'\n"
const wrap=(s:string,needle:string,start:string,label:string,good:string)=>{
 const ast=ts.createSourceFile('file.ts',s,ts.ScriptTarget.Latest,true),blocks:ts.Block[]=[]
 const go=(n:ts.Node)=>{if(ts.isBlock(n)&&n.getText(ast).includes(needle)&&n.getText(ast).includes(start))blocks.push(n);ts.forEachChild(n,go)};go(ast)
 const b=blocks.sort((a,b)=>(a.end-a.pos)-(b.end-b.pos))[0];if(!b)throw Error('missing attempt '+label)
 const body=b.getText(ast),at=b.getStart(ast)+body.indexOf(start)
 return s.slice(0,at)+`const __lemma=__l.attempt('${label}',${good});try{\n`+s.slice(at,b.end-1)+`\n}finally{__l.end(__lemma)}\n`+s.slice(b.end-1)
}
const mark=(s:string,needle:string,expression:string)=>replace(s,needle,expression+'\n'+needle)
save('core/count-cases.ts',s=>{
 s="import {shardControl as __s} from '../research/track-m/section13-control.ts'\nimport {lemmaRecorder as __l} from '../research/track-m/section18-recorder.ts'\n"+s
 s=replace(s,'  let goal:Goal={...root,name:packet.goal.name}',`  let goal:Goal={...root,name:packet.goal.name}\n  __l.root(goal);__l.phase='initial'`)
 s=replace(s,'      branches.push({prefix,path:new Map(path),root,tails})',`      branches.push({prefix,path:new Map(path),root,tails})
      if(__s.mode==='run'&&value!==__s.op){records.push(undefined);for(const v of tails)path.delete(canon(splitAt(v)));if(split){path.set(canon(split),{lin:split,holds:false});conditions.push({op:'not',x:cut!})}continue}`)
 s=replace(s,'      records.push(tree&&source?{goal:source,tree,path:new Map(path),indices,...(from?{from}:{})}:undefined)',"      records.push(tree&&source?{goal:source,tree,path:new Map(path),indices,...(from?{from}:{})}:undefined)\n      if(records.at(-1))__s.finish(records.at(-1),{})")
 s=replace(s,'    for(const [j,i] of missing.entries()){',"    for(const [j,i] of missing.entries()){\n      if(__s.mode==='run'&&cuts[i]!==__s.op)continue\n      __l.phase='retry'")
 return replace(s,'    if(records.some(r=>!r))return undefined',"    __s.finish(records[cuts.indexOf(__s.op)],{})\n    if(records.some(r=>!r))return undefined")
})
save('core/count-recovery/field-bound-lemmas.ts',s=>{
 s=prefix+s;s=replace(s,"(...args)=>wallTree('proposal-control',()=>{","(...args)=>__l.helper('field',args,()=>wallTree('proposal-control',()=>{");s=replace(s,'})\nfunction fieldBoundLemmasImpl','}))\nfunction fieldBoundLemmasImpl')
 s=replace(s,"const no=fieldCase(m,g,cert,options.fieldClaim,negative,Math.min(until,clock()+50),e=>trace.push(e),0,options.memo)","const no=__l.probe('field-column-domain',domain,g,negative,()=>fieldCase(m,g,cert,options.fieldClaim,negative,Math.min(until,clock()+50),e=>trace.push(e),0,options.memo))")
 s=wrap(s,"stage:'read-alias',",'trace.push({stage:\'read-alias-start\'','read-alias',"{op:'<=',a:{op:'var',name:left},b:{op:'var',name:right}}")
 s=mark(s,"   trace.push({stage:'read-alias',",'   __l.mark(__lemma,{source:small,sourceTree:local,sourcePath:noPath,target:g,tree:accepted?no:undefined,targetPath:noPath,productionChecked:!options.deferCheck&&accepted})')
 s=wrap(s,"stage:'field-domain',",'const noPath=new Map(path)','field-domain','domain')
 s=mark(s,"  trace.push({stage:'field-domain',",'  __l.mark(__lemma,{source:part,sourceTree:proof,sourcePath:root,target:g,tree:no,targetPath:noPath,productionChecked:!options.deferCheck&&!!no})')
 s=wrap(s,"stage:'field-bound',",'const facts=narrow(good)','field-bound','good')
 s=mark(s,"  trace.push({stage:'field-bound',",'  __l.mark(__lemma,{source:part,sourceTree:proof,sourcePath:root,target:g,tree:no,targetPath:noPath,productionChecked:!options.deferCheck&&!!no})')
 s=wrap(s,"stage:'count-lemma',",'const relevant=raw.flatMap','field-count','good')
 return mark(s,"   trace.push({stage:'count-lemma',",'   __l.mark(__lemma,{source:part,sourceTree:proof,sourcePath:root,target:g,tree:no,targetPath:noPath,productionChecked:!options.deferCheck&&!!no})')
})
save('core/count-recovery/frame-lemmas.ts',s=>{
 s=prefix+s;s=replace(s,"(...args)=>wallTree('proposal-control',()=>frameLemmasImpl(...args))","(...args)=>__l.helper('frame',args,()=>wallTree('proposal-control',()=>frameLemmasImpl(...args)))")
 s=wrap(s,"stage:'frame-lemma',",'const relevant=base.flatMap','frame','good')
 return mark(s,"  trace.push({stage:'frame-lemma',",'  __l.mark(__lemma,{source:part,sourceTree:tree,sourcePath:root,target:g,tree:no,targetPath:noPath,productionChecked:false})')
})
save('core/count-recovery/derivability-closure.ts',s=>{
 s=prefix+s
 s=wrap(s,'pins.push({split:atom,no})','const noPath=put(base','closure-pin','__l.conditions(atom)')
 s=mark(s,'  if(!no)return false',"  __l.mark(__lemma,{source:part,sourceTree:tree,sourcePath:noPath,target:g,tree:no,targetPath:noPath})")
 s=wrap(s,"stage:'closure-scalar',",'const before=clock(),traceStart','closure-scalar','good')
 s=wrap(s,"stage:'closure-source',scope:scopes.indexOf(scope),index,core:",'const part:Goal=','closure-count','good')
 s=mark(s,"  saved.push({lemma,good,",'  __l.admitted({good,part,tree,from,scope,lemma,g,cert})')
 // Failed attempts still retain their source query/returned tree for accounting.
 return mark(s,"  trace.push({stage:'closure-source',scope:scopes.indexOf(scope),index,core:",'  if(!accepted)__l.mark(__lemma,{source:proofSource,sourceTree:tree,sourcePath:path,target:g})')
})
save('core/count-recovery/conditional-proof.ts',s=>prefix+replace(s,'  marked.set(tree, {goal, lemmas})','  marked.set(tree, {goal, lemmas});__l.noteMark(tree,{goal,lemmas})'))
// Instrument operations inside the helpers, including nested closure work.
for(const file of ['core/count-recovery/field-bound-lemmas.ts','core/count-recovery/frame-lemmas.ts','core/count-recovery/derivability-closure.ts'])save(file,s=>{
 const ast=ts.createSourceFile(file,s,ts.ScriptTarget.Latest,true),edits:{a:number,b:number,text:string}[]=[],names=new Set(['seq','grow','booleanCore','refuteFast','fieldCase','proveNaturalCases','widen','liftCountProxies','admitConditionalCut','inlineConditionalCuts','transportConditionalProof','check','checkConditionalProof','rowsAt'])
 const go=(n:ts.Node)=>{if(ts.isCallExpression(n)){
  if(ts.isIdentifier(n.expression)&&names.has(n.expression.text)){edits.push({a:n.expression.getStart(ast),b:n.expression.end+1,text:`__l.invoke('${n.expression.text}',${n.expression.text},[`},{a:n.end-1,b:n.end,text:'])'})}
  else if(ts.isCallExpression(n.expression)&&ts.isIdentifier(n.expression.expression)&&n.expression.expression.text==='modelSequence'){edits.push({a:n.getStart(ast),b:n.expression.end+1,text:`__l.invoke('query',${n.expression.getText(ast)},[`},{a:n.end-1,b:n.end,text:'])'});for(const a of n.arguments)go(a);return}
 }ts.forEachChild(n,go)};go(ast)
 for(const e of edits.sort((a,b)=>b.a-a.a))s=s.slice(0,e.a)+e.text+s.slice(e.b);return s
})
console.log(JSON.stringify({researchOnly:true,policyChanged:false,manifest}))
