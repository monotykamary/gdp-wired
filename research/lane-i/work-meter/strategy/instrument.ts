import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,existsSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import ts from 'typescript'

const targets: Record<string, Record<string,string>> = {
 'count-strategies.ts': {prepareCountStrategyMachine:'strategy.prepare',proveCountStrategies:'strategy.attempt'},
 'count-guard-composition.ts': {proveFixedCountOperations:'strategy.operations',proveCountGuardComposition:'strategy.guard'},
 'count-row-composition.ts': {proveCountRowComposition:'strategy.row'},
 'count-case-compose.ts': {composeCountOperationProofs:'strategy.compose'},
 'count-strategy.ts': {finishCountStrategy:'strategy.final-check'},
 'count-lifted-strategy.ts': {proveLiftedCountFrame:'strategy.lifted.frame',proveLiftedCountInitial:'strategy.lifted.initial',proveLiftedCountComposition:'strategy.lifted.compose'},
}
// Discarded raw increments, inert phase observations, and trace-only clock reads.
// Does not change a proposal, checker, deadline, order, allowance, or weight.
export function instrumentStrategies(root: string) {
 const records=[]
 for(const [name,functions] of Object.entries(targets)){
  const path=join(root,'core',name)
  if(!existsSync(path)){assert.equal(name,'count-lifted-strategy.ts');continue}
  const before=readFileSync(path,'utf8'),file=ts.createSourceFile(path,before,ts.ScriptTarget.Latest,true)
  assert(!before.includes('strategyMeter'), 'instrument only a fresh source')
  const edits: {start:number,end:number,text:string}[]=[],found:string[]=[]
  let loops=0,traceReads=0
  const add=(start:number,text:string)=>edits.push({start,end:start,text})
  const visit=(node:ts.Node)=>{
   if(ts.isFunctionDeclaration(node)&&node.name&&functions[node.name.text]){
    assert(node.body);found.push(node.name.text)
    add(node.body.getStart(file)+1,`\nreturn workPhase('${functions[node.name.text]}', () => {\n`)
    add(node.body.end-1,'\n})\n')
   }
   if(ts.isForStatement(node)||ts.isForOfStatement(node)||ts.isForInStatement(node)||ts.isWhileStatement(node)||ts.isDoStatement(node)){
    loops++
    if(ts.isBlock(node.statement))add(node.statement.getStart(file)+1,' strategyMeter.ticks++; ')
    else{add(node.statement.getStart(file),'{ strategyMeter.ticks++; ');add(node.statement.end,' }')}
   }
   if(ts.isCallExpression(node)&&ts.isIdentifier(node.expression)){
    const phase:Record<string,string>={checkMC:'strategy.check',countedObligations:'strategy.goal-build',mcGoal:'strategy.goal-build',grow:'strategy.search',growCdcl:'strategy.search'}
    const name=phase[node.expression.text]
    if(name){add(node.getStart(file),`workPhase('${name}', () => `);add(node.end,')')}
   }
   if(ts.isCallExpression(node)&&node.expression.getText(file)==='performance.now'){
    traceReads++;edits.push({start:node.getStart(file),end:node.end,text:'traceNow()'})
   }
   ts.forEachChild(node,visit)
  }
  visit(file)
  assert.deepEqual(found.sort((a,b)=>a<b?-1:a>b?1:0),Object.keys(functions).sort((a,b)=>a<b?-1:a>b?1:0),'all strategy boundaries must exist')
  add(0,"import {coreMeter as strategyMeter} from './meter.ts'\nimport {workPhase} from './work-ledger.ts'\n"+(traceReads?"import {traceNow} from './trace-clock.ts'\n":''))
  let after=before
  for(const edit of edits.sort((a,b)=>b.start-a.start||b.end-a.end))after=after.slice(0,edit.start)+edit.text+after.slice(edit.end)
  writeFileSync(path,after)
  records.push({path:'core/'+name,functions,loops,traceReads,before:createHash('sha256').update(before).digest('hex'),after:createHash('sha256').update(after).digest('hex')})
 }
 return records
}
