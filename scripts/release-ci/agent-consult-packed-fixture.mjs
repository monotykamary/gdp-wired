// Parent-admitted installed-consumer gate; never import checkout modules.
import assert from 'node:assert/strict'
import {spawn} from 'node:child_process'
import {createInterface} from 'node:readline'
import {readFileSync,writeFileSync,mkdirSync,symlinkSync,realpathSync,renameSync} from 'node:fs'
import {join,relative,isAbsolute} from 'node:path'
import {fileURLToPath,pathToFileURL} from 'node:url'
import {createConsultation,toolNames} from 'gdp-wired/agent-consult'
const base=process.cwd(),installed=join(base,'node_modules/gdp-wired')
const inside=(root,file)=>{const r=relative(root,file);return r!=='..'&&!r.startsWith('../')&&!isAbsolute(r)}
const entry=fileURLToPath(import.meta.resolve('gdp-wired/agent-consult'))
assert.ok(inside(installed,entry))
assert.ok(inside(join(base,'node_modules/typescript'),fileURLToPath(import.meta.resolve('typescript'))))
const pkg=JSON.parse(readFileSync(join(installed,'package.json'),'utf8'))
const wrapper=JSON.parse(readFileSync(join(base,'node_modules/gdp-wired-cli/package.json'),'utf8'))
assert.equal(pkg.version,process.env.GDP_EXPECT_VERSION)
assert.equal(wrapper.version,pkg.version);assert.equal(wrapper.dependencies['gdp-wired'],pkg.version)
const bin=join(base,'node_modules/.bin/gdp-wired-agent-consult')
assert.ok(inside(installed,realpathSync(bin)))
assert.ok(inside(join(base,'node_modules/gdp-wired-cli'),realpathSync(join(base,'node_modules/.bin/gdp-wired-cli'))))
const root=join(base,'workspace'),sibling=join(base,'workspace-sibling')
mkdirSync(root);mkdirSync(sibling)
const outside=join(sibling,'counter.py');writeFileSync(outside,'outside = True\n')
symlinkSync(outside,join(root,'escape.py'));mkdirSync(join(root,'folder'))
const budget={work:5000000,apiCalls:64,depth:3,bound:2,candidates:64}
const v=name=>({op:'var',name}),n=value=>({op:'const',value}),le=(a,b)=>({op:'<=',a,b})
const subject=(broken=false)=>({
  unit:'budget',
  rule:{
    name:'request budget',params:['cap'],inputs:['cost'],state:{spent:n(0)},
    step:{state:{spent:broken
      ? {op:'add',a:v('spent'),b:v('cost')}
      : {op:'min',a:v('cap'),b:{op:'add',a:v('spent'),b:v('cost')}}}},
  },
})
const laws=[{name:'spent never exceeds cap',holds:le(v('spent'),v('cap'))}]
// Retained permit-accounting inference example, expressed as public data only.
const got={op:'and',xs:[{op:'=',a:v('acquire'),b:n(1)},{op:'<',a:v('held'),b:v('capacity')}]}
const back={op:'and',xs:[{op:'=',a:v('acquire'),b:n(0)},{op:'<',a:n(0),b:v('held')}]}
const choose=(c,a,b)=>({op:'if',c,then:a,else:b}),plus=name=>({op:'add',a:v(name),b:n(1)})
const accounting={unit:'permits',rule:{name:'permit accounting',params:['capacity'],inputs:['acquire'],state:{held:n(0),acquired:n(0),released:n(0)},assume:le(v('acquire'),n(1)),step:{state:{held:choose(got,plus('held'),choose(back,{op:'sub',a:v('held'),b:n(1)},v('held'))),acquired:choose(got,plus('acquired'),v('acquired')),released:choose(back,plus('released'),v('released'))}}}}
const accountingLaws=[{name:'released never exceeds acquired',holds:le(v('released'),v('acquired'))}]
const expected=['prove','why_not','suggest','check_change','status','check']
assert.deepEqual([...toolNames].sort(),[...expected].sort())
const record=(kind,data)=>console.log(JSON.stringify({kind,...data}))
function source(ext,version){
  const guard=version==='bad'?'self.count < 10':`self.count + amount <= ${version==='good-edit'?8:10}`
  return ext==='py'?`# gdp: law bounded count: count <= 10\nclass Counter:\n    def __init__(self):\n        self.count = 0\n    def add(self, amount: int) -> None:\n        if ${guard}:\n            self.count += amount\n`:`// gdp: law bounded count: count <= 10\nexport class Counter {\n count = 0;\n add(amount: number) { if (${guard.replaceAll('self.','this.')}) this.count += amount; }\n}\n`
}
async function client(mode,roots){
  if(mode==='library'){
    const s=createConsultation({workspaceRoots:roots})
    return {call:(name,args)=>s.call(name,args),list:async()=>(await s.handle({jsonrpc:'2.0',id:1,method:'tools/list'})).result.tools,close:()=>s.close()}
  }
  const env={...process.env,GDP_AGENT_CONSULT_ROOTS:JSON.stringify(roots)}
  delete env.NODE_OPTIONS;delete env.NODE_PATH
  const child=spawn(bin,[],{cwd:base,env,stdio:['pipe','pipe','inherit']})
  const done=new Promise((resolve,reject)=>{child.once('error',reject);child.once('close',(code,signal)=>code===0&&!signal?resolve():reject(Error(`stdio exit ${code}/${signal}`)))})
  done.catch(()=>{})
  const lines=createInterface({input:child.stdout})[Symbol.asyncIterator]();let id=0
  async function rpc(method,params){
    const request={jsonrpc:'2.0',id:++id,method,params};record('request',{request})
    child.stdin.write(JSON.stringify(request)+'\n');const line=await lines.next()
    assert.equal(line.done,false);const response=JSON.parse(line.value)
    assert.equal(response.id,id);assert.equal(response.error,undefined);record('response',{response});return response.result
  }
  await rpc('initialize',{})
  return {call:async(name,args)=>(await rpc('tools/call',{name,arguments:args})).structuredContent,list:async()=>(await rpc('tools/list',{})).tools,close:async()=>{child.stdin.end();const timer=setTimeout(()=>child.kill('SIGKILL'),5000);try{await done}finally{clearTimeout(timer)}}}
}
async function denied(c,file,code,extra={}){const r=await c.call('check',{file,...extra});assert.equal(r.ok,false,JSON.stringify(r));assert.equal(r.refusal.code,code);record('refusal',{file,code})}
for(const mode of ['library','stdio']){
  const disabled=await client(mode,[])
  try{await denied(disabled,join(root,'counter.py'),'workspace-unconfigured')}finally{await disabled.close()}
  const c=await client(mode,[root])
  try{
    assert.deepEqual((await c.list()).map(t=>t.name).sort(),[...expected].sort())
    const call=async(name,args)=>{const r=await c.call(name,args);record('receipt',{mode,name,receipt:r});assert.equal(r.ok,true,JSON.stringify(r));return r}
    const proof=await call('prove',{subject:subject(),laws,budget});assert.equal(proof.label,'proven');assert.ok(proof.result.verdicts.length);assert.ok(proof.result.verdicts.every(v=>v.proven&&v.checked))
    const status=await call('status',{unit:'budget',revision:proof.subject.revision});assert.equal(status.label,'proven');assert.equal(status.result.nativeLabel,null)
    const why=await call('why_not',{subject:subject(true),laws,budget});assert.ok(why.result.cases[0].counterexample.steps.length)
    const changed=await call('check_change',{before:subject(),after:subject(true),laws,budget});assert.equal(changed.result.newlyBroken.length,1)
    const suggestion=await call('suggest',{subject:accounting,laws:accountingLaws,budget});assert.ok(suggestion.result.discovered.length);assert.ok(suggestion.result.discovered.every(l=>l.proven&&l.checked&&l.supportSource.includes('const support: Law[]')))
    for(const ext of ['py','ts']){
      let previous
      for(const version of ['good','good-edit','bad']){
        const file=join(root,'counter.'+ext),code=source(ext,version);writeFileSync(file,code);record('edit',{mode,file,version,source:code})
        const r=await call('check',{file,budget:{...budget,candidates:2}})
        assert.equal(r.label,version==='bad'?'broken':'proven');assert.ok(r.result.rules.length);assert.ok(r.result.rules.every(rule=>rule.ok))
        const law=r.result.rules.flatMap(rule=>rule.laws).find(l=>l.name==='bounded count');assert.ok(law)
        assert.equal(law.translation,'sampled');assert.equal(law.verdict,r.label)
        if(version==='bad')assert.ok(law.run?.length);else assert.ok(law.translationChecks>0)
        assert.match(r.subject.revision,/^[a-f0-9]{64}$/);if(previous)assert.notEqual(previous,r.subject.revision);previous=r.subject.revision
      }
    }
    await denied(c,outside,'outside-workspace');await denied(c,join(root,'escape.py'),'outside-workspace')
    await denied(c,root+'/../workspace-sibling/counter.py','invalid-file')
    await denied(c,'counter.py','invalid-file');await denied(c,'file://'+outside,'invalid-file')
    await denied(c,join(root,'folder'),'not-regular-file')
    await denied(c,join(root,'counter.py'),'unsupported-field',{workspaceRoots:[sibling]})
    for(const [allowance,code] of [[{work:0},'work-budget-exceeded'],[{apiCalls:0},'api-budget-exceeded']]){
      const r=await c.call('prove',{subject:subject(),laws,budget:allowance});assert.equal(r.ok,false);assert.equal(r.refusal.code,code)
    }
  }finally{await c.close()}
}
// Missing installed worker must fail closed, never fall back to project TS.
// The path below is only an installed-file fault injection, not an entrypoint.
const worker=fileURLToPath(new URL('./agent-consult/worker.js',pathToFileURL(entry)))
assert.ok(inside(installed,worker));renameSync(worker,worker+'.disabled')
const missing=createConsultation()
try{const r=await missing.call('prove',{subject:subject(),laws,budget});assert.equal(r.ok,false);assert.equal(r.refusal.code,'worker-failure');record('no-source-fallback',{receipt:r})}finally{await missing.close();renameSync(worker+'.disabled',worker)}
record('passed',{version:pkg.version,modes:['library','installed-bin'],tools:expected,translation:'sampled',countedProfile:'provisional',osSandbox:false})
