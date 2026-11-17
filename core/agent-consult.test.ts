import {test,expect} from 'bun:test'
import {spawn} from 'node:child_process'
import {createInterface} from 'node:readline'
import {existsSync,readFileSync} from 'node:fs'
import {createConsultation,toolNames,revision} from './agent-consult.ts'
import {budget,budgetLaws,permits,permitLaws,permitAccounting,permitAccountingLaws} from '../research/agent-tools/examples.ts'

const limits={work:5_000_000,apiCalls:32,depth:3,bound:2,candidates:64}
// Results deliberately remain unknown until checked: no unchecked result may be treated as a proof.
type Data={ok:boolean,label?:string,subject:{revision:string},refusal:{code:string},result:{verdicts:{proven:boolean,checked:boolean}[],nativeLabel:unknown,assumptions:unknown,cases:{counterexample:{steps:unknown[]}|null}[],newlyBroken:unknown[],discovered:{proven:boolean,checked:boolean,supportSource:string}[]},budget:{work:{numerator:string,denominator:string}}}

test('public sessions: original data tools plus workspace check, real traces and genuinely missing inductive invariant',async()=>{
  const session=createConsultation(),other=createConsultation()
  const call=async(tool:string,args:unknown)=>await session.call(tool,args) as unknown as Data
  try{
    expect(await session.handle({jsonrpc:'2.0',method:'notifications/cancelled',params:{requestId:9,reason:'not supported'}})).toBeNull()
    const listed=await session.handle({jsonrpc:'2.0',id:0,method:'tools/list'})
    expect((listed!.result as {tools:{name:string}[]}).tools.map(t=>t.name)).toEqual(toolNames)
    const proved=await call('prove',{subject:budget(),laws:budgetLaws,budget:limits})
    expect(proved.ok).toBe(true);expect(proved.label).toBe('proven')
    expect(proved.result.verdicts.every(v=>v.proven&&v.checked)).toBe(true)
    const status=await call('status',{unit:'budget',revision:proved.subject.revision})
    expect(status.label).toBe('proven');expect(status.result.nativeLabel).toBeNull()
    expect(status.result.assumptions).toBeDefined()
    const isolated=await other.call('status',{unit:'budget',revision:proved.subject.revision}) as unknown as Data
    expect(isolated.refusal.code).toBe('missing-evidence')
    const why=await call('why_not',{subject:budget(true),laws:budgetLaws,budget:limits})
    expect(why.ok).toBe(true);expect(why.result.cases[0]!.counterexample!.steps.length).toBeGreaterThan(0)
    const changed=await call('check_change',{before:budget(),after:budget(true),laws:budgetLaws,budget:limits})
    expect(changed.ok).toBe(true);expect(changed.result.newlyBroken.length).toBe(1)
    const helpers=await call('suggest',{subject:permitAccounting(),laws:permitAccountingLaws,budget:limits})
    expect(helpers.ok).toBe(true);expect(helpers.result.discovered.length).toBeGreaterThan(0)
    expect(helpers.result.discovered.every(l=>l.proven&&l.checked&&l.supportSource.includes('const support: Law[]'))).toBe(true)
    for(const allowance of [{work:0},{apiCalls:0}]){
      const denied=await call('prove',{subject:budget(),laws:budgetLaws,budget:allowance})
      expect(denied.ok).toBe(false)
      expect(denied.refusal.code).toBe('work' in allowance?'work-budget-exceeded':'api-budget-exceeded')
    }
    for(const args of [{module:'/tmp/untrusted.ts'},{source:'process.exit()'},{subject:budget(),laws:budgetLaws,root:'/'}]){
      const denied=await call('prove',args);expect(denied.ok).toBe(false);expect(denied.refusal.code).toBe('unsupported-field')
    }
    const tampered=await call('status',{unit:'budget',revision:proved.subject.revision,label:'conformance'})
    expect(tampered.refusal.code).toBe('unsupported-field')
  }finally{await session.close();await other.close()}
},60_000)

test('cancellation is fail-closed, isolated and never retained as proof evidence',async()=>{
  const session=createConsultation(),controller=new AbortController()
  try{
    controller.abort()
    const aborted=await session.call('prove',{subject:budget(),laws:budgetLaws},{signal:controller.signal}) as unknown as Data
    expect(aborted.ok).toBe(false);expect(aborted.refusal.code).toBe('cancelled')
    const inFlight=new AbortController()
    const pending=session.call('suggest',{subject:permitAccounting(),laws:permitAccountingLaws,budget:limits},{signal:inFlight.signal})
    // Yield just long enough to admit the worker, not to use elapsed time as a proof budget.
    await new Promise<void>(resolve=>setImmediate(resolve));inFlight.abort()
    const cancelled=await pending as unknown as Data
    expect(cancelled.ok).toBe(false);expect(cancelled.refusal.code).toBe('cancelled')
    const missing=await session.call('status',{unit:'permits',revision:revision(permitAccounting(),permitAccountingLaws)}) as unknown as Data
    expect(missing.refusal.code).toBe('missing-evidence')
    await session.close()
    const closed=await session.call('prove',{subject:budget(),laws:budgetLaws}) as unknown as Data
    expect(closed.refusal.code).toBe('cancelled')
  }finally{await session.close()}
},30_000)

test('context is explanatory and close joins simultaneous queued work',async()=>{
  const session=createConsultation(),subject=permits()
  subject.rule.pre={op:'<=',a:{op:'const',value:1},b:{op:'var',name:'capacity'}}
  const expected={pre:subject.rule.pre,requestAssumption:subject.rule.assume}
  try{
    const result=await session.call('prove',{subject,laws:permitLaws,budget:limits})
    expect(result.ok).toBe(true)
    const assumptions=result.assumptions as {scope:string,subjects:unknown[]}
    expect(assumptions.scope).toContain('declared initial state')
    expect(assumptions.subjects[0]).toMatchObject(expected)
    const status=await session.call('status',{unit:subject.unit,revision:(result.subject as {revision:string}).revision})
    expect((status.result as {assumptions:unknown}).assumptions).toEqual(assumptions)
    const denied=await session.call('prove',{subject,laws:permitLaws,budget:{work:0}})
    expect(denied.ok).toBe(false);expect(denied.assumptions).toEqual(assumptions)
    const args={subject:permitAccounting(),laws:permitAccountingLaws,budget:limits}
    const first=session.call('suggest',args),second=session.call('suggest',args)
    await new Promise<void>(resolve=>setImmediate(resolve))
    await session.close()
    // close resolves after the exact active worker exits and queued calls refuse.
    for(const result of await Promise.all([first,second])){
      expect(result.ok).toBe(false);expect((result.refusal as {code:string}).code).toBe('cancelled')
    }
  }finally{await session.close()}
},30_000)

test('packaging declares public API, executable CLI and separately compiled worker',()=>{
  const pkg=JSON.parse(readFileSync(new URL('../package.json',import.meta.url),'utf8'))
  const build=JSON.parse(readFileSync(new URL('../tsconfig.build.json',import.meta.url),'utf8'))
  expect(pkg.exports['./agent-consult']).toEqual({types:'./dist/core/agent-consult.d.ts',default:'./dist/core/agent-consult.js'})
  expect(pkg.bin['gdp-wired-agent-consult']).toBe('dist/core/agent-consult/cli.js')
  for(const file of ['core/agent-consult.ts','core/agent-consult/cli.ts','core/agent-consult/worker.ts'])expect(build.files).toContain(file)
  expect(readFileSync(new URL('./agent-consult/cli.ts',import.meta.url),'utf8').startsWith('#!/usr/bin/env node\n')).toBe(true)
})

// Run after build to exercise the actual Node entrypoint, not only Bun's source execution.
const built=existsSync(new URL('../dist/core/agent-consult/cli.js',import.meta.url))
test.skipIf(!built)('built Node stdio command uses installed JS worker, no Bun or project code',async()=>{
  const child=spawn('node',[new URL('../dist/core/agent-consult/cli.js',import.meta.url).pathname],{stdio:['pipe','pipe','pipe']})
  const lines=createInterface({input:child.stdout})[Symbol.asyncIterator]();let errors=''
  child.stderr.on('data',(b:Buffer)=>{errors+=b.toString()})
  const rpc=async(id:number,method:string,params:unknown={})=>{
    child.stdin.write(JSON.stringify({jsonrpc:'2.0',id,method,params})+'\n')
    const next=await lines.next();expect(next.done,errors).toBe(false)
    const response=JSON.parse(next.value!);expect(response.id).toBe(id);expect(response.error).toBeUndefined();return response.result
  }
  try{
    const hello=await rpc(1,'initialize');expect(hello.serverInfo.name).toBe('gdp-wired-agent-consult')
    const proof=await rpc(2,'tools/call',{name:'prove',arguments:{subject:budget(),laws:budgetLaws,budget:limits}})
    expect(proof.structuredContent.ok).toBe(true);expect(proof.structuredContent.label).toBe('proven')
    const status=await rpc(3,'tools/call',{name:'status',arguments:{unit:'budget',revision:proof.structuredContent.subject.revision}})
    expect(status.structuredContent.label).toBe('proven')
    const why=await rpc(4,'tools/call',{name:'why_not',arguments:{subject:budget(true),laws:budgetLaws,budget:limits}})
    expect(why.structuredContent.result.cases[0].counterexample.steps.length).toBeGreaterThan(0)
    const changed=await rpc(5,'tools/call',{name:'check_change',arguments:{before:budget(),after:budget(true),laws:budgetLaws,budget:limits}})
    expect(changed.structuredContent.result.newlyBroken.length).toBe(1)
    const suggested=await rpc(6,'tools/call',{name:'suggest',arguments:{subject:permitAccounting(),laws:permitAccountingLaws,budget:limits}})
    expect(suggested.structuredContent.result.discovered.length).toBeGreaterThan(0)
    const refused=await rpc(7,'tools/call',{name:'prove',arguments:{subject:budget(),laws:budgetLaws,budget:{work:0}}})
    expect(refused.structuredContent.refusal.code).toBe('work-budget-exceeded')
  }finally{
    child.stdin.end();child.kill('SIGTERM')
    await new Promise<void>(resolve=>{if(child.exitCode!==null||child.signalCode!==null)resolve();else child.once('close',()=>resolve())})
  }
},30_000)
