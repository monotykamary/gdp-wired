// Measurement-only wrappers for a disposable Linux snapshot. No search knobs change.
import {existsSync,mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {dirname,join,relative} from 'node:path'
import {createHash} from 'node:crypto'
import ts from 'typescript'

type Spec={name:string,phase:string,query?:boolean}
const specs:Record<string,Spec[]>={
 'kernel/kernel.ts':['check','checkMC','checkCountedLaws','checkGoalLemmas'].map(name=>({name,phase:'kernel'})),
 'core/check.ts':[{name:'checkRefutation',phase:'kernel'}],
 'kernel/prove.ts':['grow','growWide'].map(name=>({name,phase:'search'})),
 'kernel/model-sequence.ts':[{name:'modelSequence',phase:'search',query:true}],
 'core/solver.ts':['solve','refuteFast'].map(name=>({name,phase:'search'})),
 'core/counts.ts':[{name:'certFor',phase:'proposals'}],
 'core/count-focused.ts':[{name:'demandCountCert',phase:'demand'}],
 'core/count-recovery/conditional-proof.ts':[{name:'checkConditionalProof',phase:'kernel'}],
}
const restoring=process.argv[2]==='--restore',backup=process.argv[restoring?3:2]
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1'||!backup)throw new Error('disposable Linux snapshot and backup path required')
const hash=(s:string)=>createHash('sha256').update(s).digest('hex'),manifest:any[]=[]
if(restoring){
 const prior=JSON.parse(readFileSync(join(backup,'manifest.json'),'utf8')) as {file:string,before:string,after:string}[]
 for(const row of prior){
  if(hash(readFileSync(row.file,'utf8'))!==row.after)throw new Error(`modified after instrumentation: ${row.file}`)
  const original=readFileSync(join(backup,row.file),'utf8');if(hash(original)!==row.before)throw new Error('backup hash mismatch')
  writeFileSync(row.file,original)
 }
 console.log(JSON.stringify({mode:'phase-census-restored',files:prior.length}));process.exit(0)
}
const files=new Set([...Object.keys(specs),'core/count-recovery/derivability-closure.ts'])
for(const file of files){
 if(!existsSync(file))continue
 const original=readFileSync(file,'utf8');let source=original
 if(source.includes('__phaseCensus'))throw new Error(`already instrumented: ${file}`)
 const replace=(a:string,b:string)=>{if(source.split(a).length!==2)throw new Error(`non-unique instrumentation anchor: ${file}: ${a}`);source=source.replace(a,b)}
 if(file==='core/count-recovery/derivability-closure.ts'){
  replace(' // Phase A, once:'," __phaseCensus.phase('A')\n // Phase A, once:")
  replace(' // Conditional source scopes are data'," __phaseCensus.phase('B')\n // Conditional source scopes are data")
  replace(' // Phase C only:'," __phaseCensus.phase('other')\n // Phase C only:")
  replace("saved.push({lemma,good,...(index===undefined?{}:{index})});trace.push", "saved.push({lemma,good,...(index===undefined?{}:{index})});__phaseCensus.cut(saved.at(-1)!,g,cert);trace.push")
  replace('  const version=saved.length;', '  __phaseCensus.beginRound()\n  const version=saved.length;')
  replace("  trace.push({stage:'closure-round',round:rounds,added,unresolved,cuts:saved.length,models:models.length,scopes:scopes.length})", "  __phaseCensus.endRound({round:rounds,added,unresolved,cuts:saved.length})\n  trace.push({stage:'closure-round',round:rounds,added,unresolved,cuts:saved.length,models:models.length,scopes:scopes.length})")
  replace('  const numeric:Goal=', '  const __censusLeaf=__phaseCensus.beginLeaf(scope,available)\n  const numeric:Goal=')
  replace('  const extended=lemmaPath(available.map(s=>s.lemma),scope)', '  __phaseCensus.endLeaf(__censusLeaf,numeric,proof,q)\n  const extended=lemmaPath(available.map(s=>s.lemma),scope)')
  replace("  trace.push({stage:'closure-final'", "  __phaseCensus.finishLeaf(__censusLeaf,!!tree)\n  trace.push({stage:'closure-final'")
 }
 const ast=ts.createSourceFile(file,source,ts.ScriptTarget.Latest,true),edits:{start:number,end:number,text:string}[]=[]
 const installed:string[]=[]
 for(const spec of specs[file]??[]){
  const fn=ast.statements.find((s):s is ts.FunctionDeclaration=>ts.isFunctionDeclaration(s)&&s.name?.text===spec.name)
  if(!fn?.body||!fn.name)throw new Error(`missing function ${file}:${spec.name}`)
  const renamed=`__phaseOriginal_${spec.name}`
  edits.push({start:fn.name.getStart(ast),end:fn.name.end,text:renamed})
  const visit=(node:ts.Node)=>{if(ts.isCallExpression(node)&&ts.isIdentifier(node.expression)&&node.expression.text===spec.name)edits.push({start:node.expression.getStart(ast),end:node.expression.end,text:renamed});ts.forEachChild(node,visit)};visit(fn.body)
  const exported=fn.modifiers?.some(m=>m.kind===ts.SyntaxKind.ExportKeyword)?'export ':''
  const call=`__phaseCensus.run('${spec.phase}','${file}:${spec.name}',()=>${renamed}(...args))`
  const text=spec.query?`\n${exported}const ${spec.name}:typeof ${renamed}=(...args)=>{const query=${renamed}(...args);return (...input)=>__phaseCensus.run('search','${file}:${spec.name}.query',()=>query(...input))}\n`:`\n${exported}const ${spec.name}:typeof ${renamed}=(...args)=>${call}\n`
  edits.push({start:fn.end,end:fn.end,text});installed.push(spec.name)
 }
 if(file==='core/count-recovery/derivability-closure.ts'){
  const fn=ast.statements.find((s):s is ts.FunctionDeclaration=>ts.isFunctionDeclaration(s)&&s.name?.text==='deriveCountClosure')
  if(!fn?.body)throw new Error('missing closure body')
  edits.push({start:fn.body.getStart(ast)+1,end:fn.body.getStart(ast)+1,text:'\n return __phaseCensus.closure(g,cert,root,()=>{\n'})
  edits.push({start:fn.body.end-1,end:fn.body.end-1,text:'\n })\n'});installed.push('closure phases and deferred cut-use capture')
 }
 for(const e of edits.sort((a,b)=>b.start-a.start))source=source.slice(0,e.start)+e.text+source.slice(e.end)
 let module=relative(dirname(file),'research/track-m/phase-census-meter.ts');if(!module.startsWith('.'))module='./'+module
 source=`import {census as __phaseCensus} from '${module}'\n`+source
 const saved=join(backup,file);mkdirSync(dirname(saved),{recursive:true});writeFileSync(saved,original);writeFileSync(file,source)
 manifest.push({file,before:hash(original),after:hash(source),installed})
}
writeFileSync(join(backup,'manifest.json'),JSON.stringify(manifest,null,2)+'\n')
console.log(JSON.stringify({mode:'phase-census-install',manifest}))
