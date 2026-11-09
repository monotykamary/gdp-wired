import {readFileSync,writeFileSync} from 'node:fs'
import {relative,dirname} from 'node:path'
import {createHash} from 'node:crypto'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux copy required')
const specs:Record<string,string[]>={
 'core/count-cases.ts':['proveCountCases','finiteCountChoice','selectedCase'],
 'core/count-recovery/guard-cases.ts':['guardCasesImpl','visit','leaf'],
 'core/count-recovery/field-case.ts':['fieldCaseImpl'],
 'core/count-recovery/field-bound-lemmas.ts':['fieldBounds','fieldBoundLemmasImpl'],
 'core/count-recovery/derivability-closure.ts':['deriveCountClosure','fast','source','pin','scopesFor','scalar','finish','atLeaf','accept'],
 'core/count-recovery/row-cases.ts':['proveRowCasesImpl','visit','leaf'],
 'core/count-recovery/natural-cases.ts':['naturalSplits','proveNaturalCases'],
 'core/count-select.ts':['selectCountBounds'],
 'core/count-facts.ts':['countsForReads']
}
const hash=(s:string)=>createHash('sha256').update(s).digest('hex'),manifest:any[]=[]
for(const [file,names]of Object.entries(specs)){
 const old=readFileSync(file,'utf8'),ast=ts.createSourceFile(file,old,ts.ScriptTarget.Latest,true),edits:{start:number,end:number,text:string}[]=[],found:string[]=[]
 const module=(target:string)=>{const p=relative(dirname(file),target);return p.startsWith('.')?p:'./'+p}
 const walk=(node:ts.Node)=>{
  let name:string|undefined,body:ts.ConciseBody|undefined,params:ts.NodeArray<ts.ParameterDeclaration>|undefined
  if(ts.isFunctionDeclaration(node)&&node.name){name=node.name.text;body=node.body;params=node.parameters}
  else if(ts.isArrowFunction(node)&&ts.isVariableDeclaration(node.parent)&&ts.isIdentifier(node.parent.name)){name=node.parent.name.text;body=node.body;params=node.parameters}
  if(name&&names.includes(name)&&body&&ts.isBlock(body)&&params){
   const args=params.map(x=>ts.isIdentifier(x.name)?x.name.text:'undefined').join(',');edits.push({start:body.getStart(ast)+1,end:body.getStart(ast)+1,text:`return __entryProfile.run(${JSON.stringify(file+':'+name)},[${args}],()=>{`},{start:body.end-1,end:body.end-1,text:'})'});found.push(name)
  }
  if(ts.isImportDeclaration(node)&&ts.isStringLiteral(node.moduleSpecifier)&&node.importClause?.namedBindings&&ts.isNamedImports(node.importClause.namedBindings)){
   const path=node.moduleSpecifier.text,wanted=path.endsWith('/kernel/prove.ts')?['grow','widen','rowsAt']:path.endsWith('/kernel/model-sequence.ts')?['modelSequence']:path.endsWith('/solver.ts')?['solve','refuteFast']:[],parts=node.importClause.namedBindings.elements,taken=parts.filter(x=>wanted.includes((x.propertyName??x.name).text)),kept=parts.filter(x=>!taken.includes(x))
   if(taken.length)edits.push({start:node.getStart(ast),end:node.end,text:(kept.length?`import {${kept.map(x=>x.getText(ast)).join(',')}} from ${JSON.stringify(path)}\n`:'')+`import {${taken.map(x=>x.getText(ast)).join(',')}} from ${JSON.stringify(module('research/track-m/entry-profile-ops.ts'))}`})
  }
  ts.forEachChild(node,walk)
 };walk(ast)
 let text=old;for(const e of edits.sort((a,b)=>b.start-a.start))text=text.slice(0,e.start)+e.text+text.slice(e.end)
 text=`import {entryProfile as __entryProfile} from ${JSON.stringify(module('research/track-m/entry-profile.ts'))}\n`+text;writeFileSync(file,text);manifest.push({file,found,before:hash(old),after:hash(text)})
}
const ops='core/count-recovery/ops.ts',old=readFileSync(ops,'utf8'),text="export {check,grow,widen,rowsAt,modelSequence,solve,refuteFast,wallSpan,wallTree} from '../../research/track-m/entry-profile-ops.ts'\n";writeFileSync(ops,text);manifest.push({file:ops,before:hash(old),after:hash(text)})
console.log(JSON.stringify({profileInstall:'entry-function-boundaries',kernelModified:false,manifest}))
