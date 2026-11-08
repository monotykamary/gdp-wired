// T1 only. Run after install-phase-census.ts in a disposable Linux snapshot.
import {readFileSync,writeFileSync} from 'node:fs'
import {relative,dirname} from 'node:path'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const targets:Record<string,[string,string][]>= {
 'core/count-recovery/conditional-cuts.ts':[['admitConditionalCut','admission'],['admitCut','admission'],['dependencies','admission'],['relevantHypotheses','admission'],['inline','transport'],['transport','transport'],['checked','check'],['inlineConditionalCuts','transport']],
 'core/count-recovery/conditional-proof.ts':[['independent','check'],['checked','check'],['retarget','transport'],['ordinary','transport'],['leaf','transport'],['transportConditionalProof','transport'],['collectConditionalCertificate','transport']],
 'core/count-recovery/lift-count-proxies.ts':[['liftCountProxies','transport']],
 'core/count-cert-transport.ts':[['transportCountCertificate','transport']],
 'kernel/prove.ts':[['widen','transport']],
 'kernel/kernel.ts':[['check','kernel']],
 'core/count-recovery/scalar-guards.ts':[['countScalarGuards','scalar-proposal']],
 'core/count-recovery/derivability-closure.ts':[],
}
const followup=process.argv.includes('--followup')
if(followup){
 targets['kernel/kernel.ts']!.push(['mcGoal','count-goal-build'],['countedObligations','obligation-build'])
 targets['kernel/prove.ts']!.push(['rowsAt','row-materialization'])
 targets['core/count-focused.ts']=[['focusCountCert','focused-pool'],['countLawSeeds','instance-seeds'],['countRowBridges','instance-seeds'],['fieldLawBridges','instance-seeds'],['independentCountInstances','instance-validation']]
 targets['core/count-cases.ts']=[['selectedCase','case-control'],['proveCountCases','case-control'],['withoutCountWitnesses','witness-filter']]
 targets['core/count-witness-flags.ts']=[['seedCountWitnessFlags','witness-flags']]
 targets['core/count-write-frames.ts']=[['proposeWriteCountFrames','write-frame-proposal']]
 targets['core/count-recovery/pre-state-source.ts']=[['preStateCountSource','source-transform']]
 targets['core/count-recovery/fold-path.ts']=[['foldPath','source-transform']]
 targets['core/count-recovery/field-case.ts']=[['fieldCase','field-control']]
}
for(const [file,specs]of Object.entries(targets)){
 let source=readFileSync(file,'utf8')
 const replace=(a:string,b:string)=>{if(source.split(a).length!==2)throw new Error('nonunique T1 marker: '+a);source=source.replace(a,b)}
 if(followup&&file==='core/count-recovery/conditional-proof.ts')replace("if ('leaf' in t) return check(goal, t, lemmaPath(context.lemmas, p)) && alive(until)","if ('leaf' in t) return __s7Detail.withLeafContext(goal,t,p,context.lemmas,()=>check(goal, t, lemmaPath(context.lemmas, p))) && alive(until)")
 if(file==='core/count-recovery/conditional-cuts.ts'){
  replace('  if (less.length < when.length) {',"  __s7Detail.run('admitCut.trace-reduction','admission',()=>{\n  if (less.length < when.length) {")
  replace('    const next = proofPath(less, cut), reduced = transport(small, small, proof, base, next, until)', '    const next = proofPath(less, cut), reduced = transport(small, small, proof!, base, next, until)')
  replace('  // Lookup traces are conservative;',"  })\n  // Lookup traces are conservative;")
  replace('  for (let i = when.length - 1; i >= 0; i--) {',"  const __s7Loop=__s7Detail.begin('admitCut.per-atom','admission')\n  for (let i = when.length - 1; i >= 0; i--) {")
  replace('  return checked(small, proof, base, until) ? {when, cut, tree: proof, slice} : undefined',"  __s7Detail.end(__s7Loop)\n  return __s7Detail.run('admitCut.final-check','check',()=>checked(small, proof!, base, until)) ? {when, cut, tree: proof, slice} : undefined")
 }
 const ast=ts.createSourceFile(file,source,ts.ScriptTarget.Latest,true),edits:{start:number,end:number,text:string}[]=[]
 for(const [name,kind]of specs){
  const fn=ast.statements.find((s):s is ts.FunctionDeclaration=>ts.isFunctionDeclaration(s)&&s.name?.text===name)
  if(fn?.body&&fn.name){
   const renamed=`__s7Original_${name}`;edits.push({start:fn.name.getStart(ast),end:fn.name.end,text:renamed})
   const walk=(n:ts.Node)=>{if(ts.isCallExpression(n)&&ts.isIdentifier(n.expression)&&n.expression.text===name)edits.push({start:n.expression.getStart(ast),end:n.expression.end,text:renamed});ts.forEachChild(n,walk)};walk(fn.body)
   const exported=fn.modifiers?.some(m=>m.kind===ts.SyntaxKind.ExportKeyword)?'export ':''
   const timed=kind==='kernel'?`__s7Detail.kernel('${file}:${name}',args,()=>${renamed}(...args))`:`__s7Detail.run('${file}:${name}','${kind}',()=>${renamed}(...args))`
   const call=followup&&name==='mcGoal'?`__s7Followup.noteGoal(args,${timed})`:timed
   edits.push({start:fn.end,end:fn.end,text:`\n${exported}const ${name}:typeof ${renamed}=(...args)=>${call}\n`})
  }else{
   let found=false
   const walk=(n:ts.Node)=>{if(ts.isVariableDeclaration(n)&&ts.isIdentifier(n.name)&&n.name.text===name&&n.initializer&&ts.isArrowFunction(n.initializer)){
    const body=n.initializer.body;if(!ts.isCallExpression(body))throw new Error('unsupported variable body '+name)
    const text=body.getText(ast),call=kind==='kernel'?`__s7Detail.kernel('${file}:${name}',args,()=>(${text}))`:`__s7Detail.run('${file}:${name}','${kind}',()=>(${text}))`
    edits.push({start:body.getStart(ast),end:body.end,text:call});found=true
   }ts.forEachChild(n,walk)};walk(ast)
   if(!found)throw new Error('missing T1 function '+file+':'+name)
  }
 }
 if(file==='core/count-recovery/derivability-closure.ts'){
  const walk=(n:ts.Node)=>{if(ts.isVariableDeclaration(n)&&ts.isIdentifier(n.name)&&['source','finish'].includes(n.name.text)&&n.initializer&&ts.isArrowFunction(n.initializer)&&ts.isBlock(n.initializer.body)){
   const body=n.initializer.body;edits.push({start:body.getStart(ast)+1,end:body.getStart(ast)+1,text:`return __s7Detail.run('closure.${n.name.text}','${n.name.text}',()=>{`},{start:body.end-1,end:body.end-1,text:'})'})
  }ts.forEachChild(n,walk)};walk(ast)
 }
 for(const edit of edits.sort((a,b)=>b.start-a.start))source=source.slice(0,edit.start)+edit.text+source.slice(edit.end)
 let module=relative(dirname(file),'research/track-m/section7-cost-meter.ts');if(!module.startsWith('.'))module='./'+module
 writeFileSync(file,`import {detail as __s7Detail${followup&&file==='kernel/kernel.ts'?',followup as __s7Followup':''}} from '${module}'\n`+source)
}
const file='research/track-m/active-source-probe.ts';let source=readFileSync(file,'utf8')
source=source.replace('import {fieldBoundLemmas,fieldBounds}', 'import {fieldBoundLemmas as __s7FieldBoundLemmas,fieldBounds}')
source="import {census as __s7Census} from './phase-census-meter.ts'\n"+source
source=source.replace("const [file,prefix=", "const fieldBoundLemmas:typeof __s7FieldBoundLemmas=(...args)=>__s7Census.run('other','active-source',()=>__s7FieldBoundLemmas(...args))\nconst [file,prefix=")
source=source.replace("detail?.reset(`${law.name}:${process.env.LAB_ROW_MODE??'active'}`)","if(detail){__s7Census.reset();detail.reset(`${law.name}:${process.env.LAB_ROW_MODE??'active'}`)}")
source=source.replace('const detailResult=detail?.capture()', 'const detailResult=detail?{...detail.capture(),phases:__s7Census.snapshot().exclusiveMs}:undefined')
writeFileSync(file,source)
console.log(JSON.stringify({installed:'section7-cost',files:Object.keys(targets)}))
