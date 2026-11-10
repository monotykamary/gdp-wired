// Trace-only modifications in disposable Linux copies; no production edits.
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {dirname,relative} from 'node:path'
import {createHash} from 'node:crypto'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux copy required')
const mode=process.argv[2],manifest:any[]=[]
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
const save=(file:string,old:string,text:string)=>{writeFileSync(file,text);manifest.push({file,before:hash(old),after:hash(text)})}
if(mode==='leaf'||mode==='family'){
 const file='core/count-recovery/derivability-closure.ts',old=readFileSync(file,'utf8');let text=old
 const edit=(a:string,b:string)=>{if(text.split(a).length!==2)throw new Error('nonunique anchor '+a.slice(0,80));text=text.replace(a,b)}
 edit(' const started=clock(),reserve='," const __closure=__d.begin('closure',{main:!__d.goal||g===__d.goal,name:g.name,insts:cert.insts.length,path:[...root],until});try{\n const started=clock(),reserve=")
 edit(' return checked?tree:undefined\n}'," return checked?tree:undefined\n }finally{__d.end(__closure)}\n}")
 edit(" const attempt=(index:number,scope:Path,end:number):'checked'|'sat'|'unknown'=>{"," const attempt=(index:number,scope:Path,end:number):'checked'|'sat'|'unknown'=>{\n  const __attempt=__d.begin('source-attempt',{closure:__closure.id,index,path:[...scope],end});try{")
 edit('  if(had?.version===version)return had.outcome',"  if(had?.version===version){__d.event('source-cached',{index,path:[...scope],outcome:had.outcome});return had.outcome}")
 edit("  if(reused){attempted.set(key,{version,outcome:'sat'});", "  if(reused){__d.event('source-result',{index,path:[...scope],part,outcome:'reused-model',models:[...models]});attempted.set(key,{version,outcome:'sat'});")
 edit('q=modelSequence(path)(part,queryLimit)',"q=__d.run('source-query',{index,limit:queryLimit},()=>modelSequence(path)(part,queryLimit))\n  __d.event('source-query-result',{index,path:[...scope],part,query:q,queryLimit})")
 edit('  return outcome\n }',"  __d.event('source-result',{index,path:[...scope],part,proofSource,outcome,accepted,query:q})\n  return outcome\n  }finally{__d.end(__attempt)}\n }")
 edit(' const finish=(scope:Path,end:number,depth=0):Tree|undefined=>{'," const finish=(scope:Path,end:number,depth=0):Tree|undefined=>{\n  const __leaf=__d.begin('leaf',{closure:__closure.id,path:[...scope],end,depth});try{")
 edit('  }finally{leafEnd=previousEnd}\n }',"  }finally{leafEnd=previousEnd}\n  }finally{__d.end(__leaf)}\n }")
 edit("  const stop=(reason:string)=>{trace.push(","  const stop=(reason:string)=>{__d.event('stop',{closure:__closure.id,reason,path:[...scope],end});trace.push(")
 edit('natural=proveNaturalCases(numeric,scope,end,trace,{deferCheck:true}),q=natural?{tree:natural}:modelSequence(scope)(numeric,end)',"natural=__d.run('natural-query',{},()=>proveNaturalCases(numeric,scope,end,trace,{deferCheck:true})),q=natural?{tree:natural}:__d.run('numeric-query',{},()=>modelSequence(scope)(numeric,end))\n    __d.capture({closure:__closure.id,path:[...scope],depth,round:round+1,end,numeric,query:q,cert,pool:[...pool],available:available.map(s=>({index:s.index,good:s.good,lemma:s.lemma}))},(index:number)=>{const inst=cert.insts[index]!,h=g.hyps[raw.length+index]!,good=(h as Extract<C,{op:'or'}>).xs[0]!;return {inst,part:{name:g.name,hyps:[...source(scope,inst.wit),...available.map(s=>s.good),h,{op:'not',x:good}]}}})")
 edit("    trace.push({stage:'closure-model-round'", "    __d.model({closure:__closure.id,path:[...scope],model,violated})\n    trace.push({stage:'closure-model-round'")
 edit('selection=modelSequence(scope)(assumed,end)',"selection=__d.run('batch-query',{indices},()=>modelSequence(scope)(assumed,end))")
 edit('  return scalar(path,stop)',"  const __row=__d.begin('row',{closure:__closure.id,path:[...path],remaining,leavesLeft,draw,granted:stop-before,end:stop});try{return scalar(path,stop)}finally{__d.end(__row)}")
 save(file,old,"import {diagnostic as __d} from '../../research/track-m/section10-diagnostic.ts'\n"+text)
 const probe='research/track-m/active-source-probe.ts',p=readFileSync(probe,'utf8'),anchor='for(const [branch,path]of paths.entries()){'
 if(p.split(anchor).length!==2)throw new Error('probe anchor')
 save(probe,p,"import {diagnostic as __d} from './section10-diagnostic.ts'\n"+p.replace(anchor,'__d.setGoal(goal)\n'+anchor))
 if(mode==='family'){
 const cf='core/count-cases.ts',co=readFileSync(cf,'utf8'),marker='    if(records.some(r=>!r))return undefined';if(co.split(marker).length!==2)throw new Error('case-result anchor');const startMarker='for(const [i,value] of [...cuts,undefined].entries()){\n      if(clock()>=until||pastWall())return undefined';if(co.split(startMarker).length!==2)throw new Error('case loop anchor');const traced=co.replace(startMarker,"for(const [i,value] of [...cuts,undefined].entries()){\n      if(clock()>=until||pastWall()){__d.event('case-final-results',{selector:name,unresolved:[...records.flatMap((r,j)=>r?[]:[cuts[j]??'else']),...cuts.slice(i)]});return undefined}");save(cf,co,"import {diagnostic as __d} from '../research/track-m/section10-diagnostic.ts'\n"+traced.replace(marker,"    __d.event('case-final-results',{selector:name,unresolved:records.flatMap((r,i)=>r?[]:[cuts[i]??'else'])})\n"+marker));
 const f='research/track-m/profile-family.ts',a=readFileSync(f,'utf8');save(f,a,"import {diagnostic as __d} from './section10-diagnostic.ts'\n"+a.replace('  costMeter.phases.clear();',"  __d.reset(law.name)\n  costMeter.phases.clear();").replace('  const wallMs=performance.now()-t,',"  if(!process.env.DIAG_OUTPUT)console.log(JSON.stringify({fullDiagnostic:__d.dump()}))\n  const wallMs=performance.now()-t,"))}
}else if(mode==='cost'){
 const specs:Record<string,string[]>={
 'core/count-focused.ts':['focusCountCert','demandCountCert'],
 'core/count-witness-flags.ts':['seedCountWitnessFlags'],
 'core/count-focus-proof.ts':['proveFocusedCounts'],
 'core/counts.ts':['certFor'],
 'kernel/kernel.ts':['countedObligations','mcGoal','checkMC'],
 'kernel/prove.ts':['grow'],
 'kernel/model-sequence.ts':['modelSequence'],
 'core/count-cases.ts':['proveCountCases'],
 'core/count-recovery/field-bound-lemmas.ts':['fieldBoundLemmasImpl'],
 }
 if(existsSync('core/count-recovery/member-inclusions.ts'))specs['core/count-recovery/member-inclusions.ts']=['memberInclusions']
 for(const [file,names]of Object.entries(specs)){
  const old=readFileSync(file,'utf8'),ast=ts.createSourceFile(file,old,ts.ScriptTarget.Latest,true),edits:{at:number,end:number,text:string}[]=[]
  for(const name of names){
   const fn=ast.statements.find((s):s is ts.FunctionDeclaration=>ts.isFunctionDeclaration(s)&&s.name?.text===name)
   if(!fn?.body||!fn.name)throw new Error('missing function '+file+':'+name)
   const renamed='__diagnostic_'+name;edits.push({at:fn.name.getStart(ast),end:fn.name.end,text:renamed})
   const walk=(node:ts.Node)=>{if(ts.isCallExpression(node)&&ts.isIdentifier(node.expression)&&node.expression.text===name)edits.push({at:node.expression.getStart(ast),end:node.expression.end,text:renamed});ts.forEachChild(node,walk)};walk(fn.body)
   const exported=fn.modifiers?.some(m=>m.kind===ts.SyntaxKind.ExportKeyword)?'export ':''
   const wrapper=name==='modelSequence'?`\n${exported}const ${name}:typeof ${renamed}=(...args)=>{const query=${renamed}(...args);return (...input)=>__d.call('${file}:${name}.query',input,()=>query(...input))}\n`:`\n${exported}const ${name}:typeof ${renamed}=(...args)=>__d.call('${file}:${name}',args,()=>${renamed}(...args))\n`
   edits.push({at:fn.end,end:fn.end,text:wrapper})
  }
  let text=old;for(const e of edits.sort((a,b)=>b.at-a.at))text=text.slice(0,e.at)+e.text+text.slice(e.end)
  let module=relative(dirname(file),'research/track-m/section10-diagnostic.ts');if(!module.startsWith('.'))module='./'+module
  save(file,old,`import {diagnostic as __d} from '${module}'\n`+text)
 }
 const file='research/track-m/profile-family.ts',old=readFileSync(file,'utf8');let text=old
 text=text.replace("  if(!['one primary','Inv3915','Inv1758','Inv2973','Inv*']", "  if(!['one primary','Inv3915','Inv1758']")
 text=text.replace('  costMeter.phases.clear();',"  __d.reset(law.name)\n  costMeter.phases.clear();")
 text=text.replace('  const wallMs=performance.now()-t,',"  console.log(JSON.stringify({diagnosticCosts:__d.dump()}))\n  const wallMs=performance.now()-t,")
 save(file,old,"import {diagnostic as __d} from './section10-diagnostic.ts'\n"+text)
}else throw new Error('mode leaf or cost required')
console.log(JSON.stringify({diagnosticInstall:mode,manifest}))
