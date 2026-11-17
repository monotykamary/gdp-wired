import {spawn} from 'node:child_process'
import {createInterface} from 'node:readline'
import {fileURLToPath} from 'node:url'
import {writeFileSync} from 'node:fs'
import {strict as assert} from 'node:assert'
import {budget,budgetLaws,budgetNearMiss,permits,permitLaws,permitNearMiss,permitAccounting,permitAccountingLaws} from './examples.ts'
import {canonical} from './protocol.ts'

// Deterministic agent-style MCP conversation. No model/network call or generated shell.
export async function scriptedSession(){
  const child=spawn(process.execPath,[fileURLToPath(new URL('./stdio.ts',import.meta.url))],{stdio:['pipe','pipe','pipe']})
  const lines=createInterface({input:child.stdout})[Symbol.asyncIterator]();let id=0,errors=''
  child.stderr.on('data',(b:Buffer)=>{errors+=b.toString().slice(0,8192-errors.length)})
  const transcript:unknown[]=[]
  async function rpc(method:string,params:unknown={}){
    const request={jsonrpc:'2.0',id:++id,method,params},started=performance.now();child.stdin.write(JSON.stringify(request)+'\n')
    const next=await lines.next();assert(!next.done,`MCP server closed: ${errors}`)
    const response=JSON.parse(next.value);assert.equal(response.id,id);assert(!response.error,JSON.stringify(response.error));transcript.push({request,response,observedWallMs:performance.now()-started});return response.result
  }
  const tool=async(name:string,args:unknown)=>(await rpc('tools/call',{name,arguments:args})).structuredContent
  try{
    const hello=await rpc('initialize',{protocolVersion:'2024-11-05',capabilities:{},clientInfo:{name:'scripted-coding-agent',version:'1'}})
    assert.equal(hello.serverInfo.name,'gdp-wired-agent-consult')
    const listed=await rpc('tools/list');assert.deepEqual(listed.tools.map((x:{name:string})=>x.name),['prove','why_not','suggest','check_change','status','check'])
    const disabled=await tool('check',{file:'/tmp/not-authorized.py'});assert.equal(disabled.ok,false);assert.equal(disabled.refusal.code,'workspace-unconfigured')
    for(const fixture of [{make:budget,laws:budgetLaws,near:budgetNearMiss},{make:permits,laws:permitLaws,near:permitNearMiss}]){
      const good=fixture.make(),bad=fixture.make(true),limits={work:2_000_000,apiCalls:32,depth:3,bound:2,candidates:32}
      const proved=await tool('prove',{subject:good,laws:fixture.laws,budget:limits})
      assert(proved.ok,JSON.stringify(proved));assert.equal(proved.label,'proven');assert(proved.result.verdicts.every((v:{proven:boolean,checked:boolean})=>v.proven&&v.checked))
      const status=await tool('status',{unit:good.unit,revision:proved.subject.revision});assert.equal(status.label,'proven');assert.equal(status.result.nativeLabel,null)
      const why=await tool('why_not',{subject:bad,laws:fixture.laws,budget:limits});assert(why.ok,JSON.stringify(why));assert(why.result.cases[0].counterexample.steps.length>0)
      const changed=await tool('check_change',{before:good,after:bad,laws:fixture.laws,budget:limits});assert(changed.ok,JSON.stringify(changed));assert.equal(changed.result.newlyBroken.length,1);assert.equal(changed.result.behaviour.status,'bounded-difference')
      const suggestion=await tool('suggest',{subject:good,laws:fixture.laws,nearMisses:fixture.near,budget:limits});assert(suggestion.ok,JSON.stringify(suggestion));assert(suggestion.result.satisfied.length>0);assert(suggestion.result.nearMisses.length>0)
      const repeat=await tool('prove',{subject:good,laws:fixture.laws,budget:limits});assert.equal(canonical(repeat),canonical(proved),'fresh worker replay must be deterministic')
      const exhausted=await tool('prove',{subject:bad,laws:fixture.laws,budget:{work:0}});assert.equal(exhausted.ok,false);assert.equal(exhausted.refusal.code,'work-budget-exceeded')
      const denied=await tool('prove',{subject:good,laws:fixture.laws,budget:{apiCalls:0}});assert.equal(denied.ok,false);assert.equal(denied.refusal.code,'api-budget-exceeded')
      const justProof=Math.ceil(Number(proved.budget.work.numerator)/Number(proved.budget.work.denominator))+1
      const noInference=await tool('suggest',{subject:good,laws:fixture.laws,budget:{work:justProof}});assert.equal(noInference.ok,false);assert.equal(noInference.refusal.code,'work-budget-exceeded')
    }
    const helpers=await tool('suggest',{subject:permitAccounting(),laws:permitAccountingLaws,budget:{work:5_000_000,apiCalls:32,candidates:64}})
    assert(helpers.ok,JSON.stringify(helpers));assert(helpers.result.discovered.length>0,'accounting needs a genuinely inferred inductive helper');assert(helpers.result.discovered.every((x:{proven:boolean,checked:boolean,supportSource:string})=>x.proven&&x.checked&&x.supportSource.includes('const support: Law[]')))
    const unknown=await tool('status',{unit:'unknown',revision:'0'.repeat(64)});assert.equal(unknown.ok,false);assert.equal(unknown.refusal.code,'missing-evidence')
    const tampered=await tool('status',{unit:'budget',revision:'0'.repeat(64),label:'conformance'});assert.equal(tampered.ok,false);assert.equal(tampered.refusal.code,'unsupported-field')
    return {schema:'gdp-wired/scripted-agent-session/v1',passed:true,rules:2,transport:'stdio JSON-RPC',networkCalls:0,engine:'existing GDP-Wired APIs only',calls:transcript.length,transcript}
  }finally{
    child.stdin.end();child.kill('SIGTERM');await new Promise<void>(resolve=>{if(child.exitCode!==null||child.signalCode!==null)resolve();else child.once('close',()=>resolve())})
  }
}
if(import.meta.main){const result=await scriptedSession(),at=process.argv.indexOf('--out');if(at>=0)writeFileSync(process.argv[at+1]!,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify({passed:result.passed,rules:result.rules,calls:result.calls,networkCalls:0}))}
