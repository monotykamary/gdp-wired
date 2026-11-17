#!/usr/bin/env bun
/** Audit elapsed-budget candidates without blindly rewriting source. */
import ts from 'typescript'

type Grant = {path:string, expression:string, literal?:number}
type Row = {file:string, callLine:string, callee:string, budgetMs:string, clockDomain:string, quickShard:string, suiteJobs:string, profileClock:string, profileConflict:string, certainty:string, testName:string, importSource:string, budgetGrants:string}
type Ast = {resolved:boolean, line:number, properties:{path:string,expression:string}[], reason?:string}
export type Classification = 'converted'|'already-counted'|'watchdog-only'|'needs-reviewed-support'
export type Entry = {id:string,file:string,line:number,callee:string,grants:Grant[],classification:Classification,reason:string,clockDomain:string,certainty:string,testName:string,ast:Ast}

const columns = ['file','callLine','callee','budgetMs','clockDomain','quickShard','suiteJobs','profileClock','profileConflict','certainty','testName','importSource','budgetGrants'] as const
const processCallees = new Set(['spawnSync','execSync','execFileSync'])
const workCallees = new Set(['proveRule','proveSteps','inferLaws','check','withLemmas','provePool'])
const nameOf = (n:ts.PropertyName) => ts.isIdentifier(n)||ts.isStringLiteral(n)||ts.isNumericLiteral(n) ? n.text : n.getText()
const callName = (n:ts.Expression) => ts.isIdentifier(n) ? n.text : ts.isPropertyAccessExpression(n) ? n.name.text : n.getText()

export function parseInventory(text:string):Row[] {
  const lines=text.trimEnd().split(/\r?\n/), header=lines.shift()?.split('\t')
  if (!header || header.join('\t')!==columns.join('\t')) throw Error('unexpected inventory TSV header')
  return lines.filter(Boolean).map((line,i) => {
    const fields=line.split('\t')
    if(fields.length!==columns.length) throw Error(`inventory line ${i+2}: expected ${columns.length} columns, got ${fields.length}`)
    return Object.fromEntries(columns.map((k,j)=>[k,fields[j]!])) as Row
  })
}
const grants = (row:Row):Grant[] => {
  try { const x=JSON.parse(row.budgetGrants) as Grant[]; if(Array.isArray(x)) return x } catch {}
  throw Error(`${row.file}:${row.callLine}: invalid budgetGrants JSON`)
}
function astFor(source:string,line:number,callee:string,testName:string,ordinal:number,groupSize:number):Ast {
  const sf=ts.createSourceFile('candidate.ts',source,ts.ScriptTarget.Latest,true,ts.ScriptKind.TS)
  let selected:ts.CallExpression|undefined, distance=Infinity
  const inTest=(n:ts.Node):boolean => {
    if(testName==='<file-helper>') return true
    for(let parent=n.parent;parent;parent=parent.parent) if(ts.isCallExpression(parent)){
      const name=parent.arguments[0]
      if(name&&(ts.isStringLiteral(name)||ts.isNoSubstitutionTemplateLiteral(name))&&name.text===testName) return true
    }
    return false
  }
  const zeroWork=(call:ts.CallExpression):boolean => {
    const zero=(node:ts.Node):boolean=>{
      if(!ts.isObjectLiteralExpression(node))return false
      return node.properties.some(p=>ts.isPropertyAssignment(p)&&(nameOf(p.name)==='work'&&ts.isNumericLiteral(p.initializer)&&Number(p.initializer.text)===0||nameOf(p.name)==='search'&&zero(p.initializer)))
    }
    return call.arguments.some(zero)
  }
  const matches:ts.CallExpression[]=[]
  const visit=(n:ts.Node):void => { if(ts.isCallExpression(n)&&callName(n.expression)===callee&&inTest(n))matches.push(n); ts.forEachChild(n,visit) }
  visit(sf)
  // Additional zero-work exhaustion controls are not the historical positive
  // grants. Match moved multi-call tests by ordinal only when cardinality agrees.
  const candidates=testName==='<file-helper>'?matches:matches.filter(n=>!zeroWork(n))
  const anchored=testName!=='<file-helper>'&&candidates.length===groupSize?candidates[ordinal]:undefined
  for(const n of candidates){const at=sf.getLineAndCharacterOfPosition(n.getStart(sf)).line+1,d=Math.abs(at-line);if(d<distance){distance=d;selected=n}}
  if(anchored){selected=anchored;distance=0}
  const scopedCalls=candidates.length
  if(!selected) return {resolved:false,line,properties:[],reason:'no matching CallExpression at inventory callee'}
  const at=sf.getLineAndCharacterOfPosition(selected.getStart(sf)).line+1
  if(distance>6&&(testName==='<file-helper>'||scopedCalls!==1)) return {resolved:false,line:at,properties:[],reason:`nearest matching call is ${distance} lines from inventory location; test anchor is absent or ambiguous`}
  const properties:{path:string,expression:string}[]=[]
  // Only direct option records: a callback's nested proof call is not this
  // call's grant, and must not authenticate an unrelated conversion.
  const walk=(n:ts.Node,path:string):void => {
    if(!ts.isObjectLiteralExpression(n)) return
    for(const property of n.properties) if(ts.isPropertyAssignment(property)){
      const key=nameOf(property.name), next=path?`${path}.${key}`:key
      properties.push({path:next,expression:property.initializer.getText(sf)})
      walk(property.initializer,next)
    }
  }
  selected.arguments.forEach(arg=>walk(arg,''))
  return {resolved:true,line:at,properties}
}
function classify(row:Row,grants:Grant[],ast:Ast):Pick<Entry,'classification'|'reason'> {
  if(!ast.resolved) return {classification:'needs-reviewed-support',reason:`source AST unresolved: ${ast.reason}`}
  // Empty numeric-grant lists are NOT evidence of a watchdog: withWall's
  // positional deadline was absent from the old property-only inventory.
  if(row.callee==='withWall') return {classification:'needs-reviewed-support',reason:'internal wall helper can delimit semantic search; positional deadline and clock domain need review even when budgetGrants is empty'}
  let imported: {module?:string} = {}
  try { imported=JSON.parse(row.importSource) as {module?:string} } catch { /* unresolved imports are never watchdog evidence */ }
  if(processCallees.has(row.callee) && (imported.module==='node:child_process'||imported.module==='child_process') && ast.properties.some(p=>p.path==='timeout')) return {classification:'watchdog-only',reason:'AST timeout on imported native child process is an interruption watchdog; preserved unchanged, never mapped to work'}
  const hasWork=ast.properties.some(p=>p.path==='work'||p.path==='search.work')
  const mixed=ast.properties.some(p=>p.path==='ms'||p.path==='search.ms'||p.path==='wall'||p.path==='timed'||p.path==='runsMs')
  if(workCallees.has(row.callee)&&hasWork&&!mixed) return {classification:'converted',reason:'direct AST option grants explicit work through a reviewed work-capable API; no coexisting semantic time option'}
  if(!grants.length) return {classification:'needs-reviewed-support',reason:'no recorded numeric property is not proof of safety: inspect positional/helper budget authority'}
  if(/counted/.test(row.clockDomain)&&!/conditional|legacy|wall via/.test(row.clockDomain)) return {classification:'already-counted',reason:'inventory identifies a counted work scope; compatibility input remains under review'}
  if(/CLI|conditional|unknown|wall via|inWorkScope/.test(row.clockDomain)) return {classification:'needs-reviewed-support',reason:'callee forwards or conditionally selects a search budget; verify public work support before conversion'}
  return {classification:'needs-reviewed-support',reason:'elapsed semantic budget needs a measured work baseline and reviewed API support'}
}
export async function audit(root:string,rows:Row[]):Promise<Entry[]> {
  const sources=new Map<string,string>()
  for(const row of rows){const f=`${root}/${row.file}`;if(!sources.has(f)&&await Bun.file(f).exists())sources.set(f,await Bun.file(f).text())}
  return rows.map((row,rowIndex)=>{const ast=sources.has(`${root}/${row.file}`)?astFor(sources.get(`${root}/${row.file}`)!,Number(row.callLine),row.callee,row.testName,rows.slice(0,rowIndex).filter(other=>other.file===row.file&&other.callee===row.callee&&other.testName===row.testName).length,rows.filter(other=>other.file===row.file&&other.callee===row.callee&&other.testName===row.testName).length):{resolved:false,line:Number(row.callLine),properties:[],reason:'source file absent'};const xs=grants(row),c=classify(row,xs,ast);return {id:String(rowIndex+1),file:row.file,line:Number(row.callLine),callee:row.callee,grants:xs,clockDomain:row.clockDomain,certainty:row.certainty,testName:row.testName,ast,...c}})
}
async function main(){const [inventory,root,output]=Bun.argv.slice(2);if(!inventory||!root||!output)throw Error('usage: bun tools/counted-budget-audit/audit.ts INVENTORY.tsv SOURCE_ROOT MANIFEST.json');const candidates=await audit(root,parseInventory(await Bun.file(inventory).text()));if(!candidates.length)throw Error('inventory produced no audit candidates');const classes=['converted','already-counted','watchdog-only','needs-reviewed-support'] as Classification[];const summary=Object.fromEntries(classes.map(k=>[k,candidates.filter(x=>x.classification===k).length]));await Bun.write(output,JSON.stringify({schema:1,inventory,root,summary,candidates},null,2)+'\n');console.log(JSON.stringify({candidates:candidates.length,...summary}))}
if(import.meta.main) await main()
