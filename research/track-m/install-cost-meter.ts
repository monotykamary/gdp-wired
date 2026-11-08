// Run only in a disposable remote snapshot. Save originals and hash every change.
// Wrappers preserve arguments/results; recursive self calls retain their original body.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {relative,dirname,join} from 'node:path'
import {createHash} from 'node:crypto'
import ts from 'typescript'
import type {CostPhase} from './cost-meter.ts'
type Spec={name:string,phase:CostPhase,lock?:boolean,query?:boolean}
const specs:Record<string,Spec[]>={
 'kernel/kernel.ts':[{name:'check',phase:'kernel',lock:true},{name:'checkMC',phase:'kernel',lock:true},{name:'checkCountedLaws',phase:'kernel',lock:true},{name:'mcGoal',phase:'construction'},{name:'countedObligations',phase:'construction'}],
 'kernel/prove.ts':[{name:'grow',phase:'search'},{name:'growWide',phase:'search'},{name:'widen',phase:'construction'},{name:'rowsAt',phase:'construction'},{name:'modelInstances',phase:'generation',lock:true}],
 'kernel/cdcl.ts':[{name:'growCdcl',phase:'search'},{name:'unfold',phase:'construction',lock:true}],
 'kernel/model-sequence.ts':[{name:'modelSequence',phase:'search',query:true}],
 'core/solver.ts':[{name:'solve',phase:'search'},{name:'refuteFast',phase:'search'}],
 'core/check.ts':[{name:'checkRefutation',phase:'kernel',lock:true}],
 'core/counts.ts':[{name:'certFor',phase:'generation',lock:true},{name:'guardLaws',phase:'generation',lock:true},{name:'candidates',phase:'generation',lock:true}],
 'core/exists.ts':[{name:'smallOf',phase:'generation',lock:true},{name:'trueSmall',phase:'generation',lock:true}],
 'core/infer.ts':[{name:'inferLaws',phase:'generation'}],
 'core/count-witness-flags.ts':[{name:'seedCountWitnessFlags',phase:'generation',lock:true}],
 'core/count-focused.ts':[{name:'countLawSeeds',phase:'generation',lock:true},{name:'fieldLawBridges',phase:'generation',lock:true},{name:'countRowBridges',phase:'generation',lock:true}],
}
const backup=process.argv[2]
if(!backup||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('set TRACK_M_DISPOSABLE_PROFILE=1 and supply a backup directory; disposable remote snapshot only')
const hash=(s:string)=>createHash('sha256').update(s).digest('hex'),manifest=[]
for(const [file,targets]of Object.entries(specs)){
 const source=readFileSync(file,'utf8'),ast=ts.createSourceFile(file,source,ts.ScriptTarget.Latest,true),edits:{start:number,end:number,text:string}[]=[]
 if(source.includes('__trackMCostSpan'))throw new Error(`already instrumented: ${file}`)
 for(const spec of targets){
  const fn=ast.statements.find((s):s is ts.FunctionDeclaration=>ts.isFunctionDeclaration(s)&&s.name?.text===spec.name)
  if(!fn?.body||!fn.name)throw new Error(`function not found: ${file}:${spec.name}`)
  const renamed=`__trackMCost_${spec.name}`
  edits.push({start:fn.name.getStart(ast),end:fn.name.end,text:renamed})
  const visit=(node:ts.Node)=>{if(ts.isCallExpression(node)&&ts.isIdentifier(node.expression)&&node.expression.text===spec.name)edits.push({start:node.expression.getStart(ast),end:node.expression.end,text:renamed});ts.forEachChild(node,visit)}
  visit(fn.body)
  const exported=fn.modifiers?.some(m=>m.kind===ts.SyntaxKind.ExportKeyword)?'export ':''
  const span=`__trackMCostSpan('${spec.phase}','${file}:${spec.name}',()=>${renamed}(...args),${!!spec.lock})`
  const text=spec.query?`\n${exported}const ${spec.name}:typeof ${renamed}=(...args)=>{const query=${renamed}(...args);return (...input)=>__trackMCostSpan('search','${file}:${spec.name}.query',()=>query(...input))}\n`:`\n${exported}const ${spec.name}:typeof ${renamed}=(...args)=>${span}\n`
  edits.push({start:fn.end,end:fn.end,text})
 }
 let output=source
 for(const e of edits.sort((a,b)=>b.start-a.start))output=output.slice(0,e.start)+e.text+output.slice(e.end)
 let module=relative(dirname(file),'research/track-m/cost-meter.ts');if(!module.startsWith('.'))module=`./${module}`
 output=`import {costSpan as __trackMCostSpan} from '${module}'\n${output}`
 const saved=join(backup,file);mkdirSync(dirname(saved),{recursive:true});writeFileSync(saved,source);writeFileSync(file,output)
 manifest.push({file,before:hash(source),after:hash(output),functions:targets})
}
writeFileSync(join(backup,'manifest.json'),JSON.stringify(manifest,null,2))
console.log(JSON.stringify({instrumented:manifest.length,manifest}))
