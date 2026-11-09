// Run after install-section10-diagnostic.ts family, only in a disposable copy.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux copy required')
const hash=(s:string)=>createHash('sha256').update(s).digest('hex'),manifest:any[]=[]
const file='core/count-cases.ts',old=readFileSync(file,'utf8'),ast=ts.createSourceFile(file,old,ts.ScriptTarget.Latest,true),edits:{at:number,text:string}[]=[]
let initial=0,fallback=0
const walk=(node:ts.Node)=>{
 if(ts.isForOfStatement(node)&&ts.isBlock(node.statement)){
  const expression=node.expression.getText(ast),body=node.statement
  const phase=expression==='[...cuts,undefined].entries()'?'initial':expression==='missing.entries()'?'fallback':undefined
  if(phase){if(phase==='initial')initial++;else fallback++
   const value=phase==='initial'?'value':'cuts[i]'
   edits.push({at:body.getStart(ast)+1,text:`\n const __action=__d.begin('action',{selector:name,value:${value}??null,index:i,cuts,phase:'${phase}'});try{\n`})
   edits.push({at:body.end-1,text:`\n }finally{__d.event('action-result',{selector:name,value:${value}??null,index:i,phase:'${phase}',closed:!!records[i]});__d.end(__action)}\n`})
  }
 }
 ts.forEachChild(node,walk)
};walk(ast)
if(initial!==1||fallback!==1)throw new Error('action loop anchors changed')
let text=old;for(const e of edits.sort((a,b)=>b.at-a.at))text=text.slice(0,e.at)+e.text+text.slice(e.at)
writeFileSync(file,text);manifest.push({file,before:hash(old),after:hash(text)})
const cf='core/count-recovery/derivability-closure.ts',co=readFileSync(cf,'utf8'),anchor='saved.push({lemma,good,...(index===undefined?{}:{index})});trace.push('
if(co.split(anchor).length!==2)throw new Error('cut anchor changed')
const ct=co.replace(anchor,"saved.push({lemma,good,...(index===undefined?{}:{index})});__d.event('cut',{index,cut:lemma.cut,when:lemma.when});trace.push(")
const finish="trace.push({stage:'closure-final',mode:'model-driven',fixedPoint"
if(ct.split(finish).length!==2)throw new Error('leaf outcome anchor changed')
const traced=ct.replace(finish,"__d.event('leaf-outcome',{outcome:tree?'checked':'untransported',path:[...scope]});"+finish)
writeFileSync(cf,traced);manifest.push({file:cf,before:hash(co),after:hash(traced)})
console.log(JSON.stringify({diagnosticInstall:'section12-unlimited-ledger',manifest}))
