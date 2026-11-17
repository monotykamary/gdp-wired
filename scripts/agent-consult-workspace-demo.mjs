#!/usr/bin/env node
// Prepared executable demo, NOT a fabricated transcript. Run only on the admitted native VM after build.
// stdout is actual MCP request/response JSONL, suitable for a retained remote artifact.
import {spawn} from 'node:child_process'
import {createInterface} from 'node:readline'
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import assert from 'node:assert/strict'
const root=mkdtempSync(join(tmpdir(),'gdp-agent-check-demo-'))
const entry=new URL('../dist/core/agent-consult/cli.js',import.meta.url)
const child=spawn(process.execPath,[entry.pathname],{stdio:['pipe','pipe','inherit'],env:{...process.env,GDP_AGENT_CONSULT_ROOTS:JSON.stringify([root])}})
const lines=createInterface({input:child.stdout})[Symbol.asyncIterator]()
let id=0
async function rpc(method,params){
  const request={jsonrpc:'2.0',id:++id,method,...(params?{params}:{})}
  console.log(JSON.stringify({direction:'agent-to-server',request}))
  child.stdin.write(JSON.stringify(request)+'\n')
  const next=await lines.next();assert.equal(next.done,false,'server closed without receipt')
  const response=JSON.parse(next.value);assert.equal(response.id,id);assert.equal(response.error,undefined)
  console.log(JSON.stringify({direction:'server-to-agent',response}))
  return response.result
}
const source=(ext,version)=>{
  const guard=version==='bad'?'self.count < 10':`self.count + amount <= ${version==='good-edit'?8:10}`
  if(ext==='py')return `# gdp: law bounded count: count <= 10\nclass Counter:\n    def __init__(self):\n        self.count = 0\n    def add(self, amount: int) -> None:\n        if ${guard}:\n            self.count += amount\n`
  return `// gdp: law bounded count: count <= 10\nexport class Counter {\n count = 0;\n add(amount: number) { if (${guard.replaceAll('self.','this.')}) this.count += amount; }\n}\n`
}
try{
  await rpc('initialize');await rpc('tools/list')
  console.log(JSON.stringify({direction:'agent-scope',limitation:'Existing CLI source-law journal gate is preserved. This release supplies sampled native-law journals for Python and TypeScript, not exhaustive certification. Any translation:unchecked result remains unknown, never promoted from mathematical evidence.'}))
  for(const ext of ['py','ts']){
    let previous
    const mathematical=[]
    for(const version of ['good','good-edit','bad']){
      const file=join(root,'counter.'+ext),code=source(ext,version)
      writeFileSync(file,code)
      console.log(JSON.stringify({direction:'agent-edit',file,version,source:code}))
      const receipt=await rpc('tools/call',{name:'check',arguments:{file,budget:{work:5000000,apiCalls:64,candidates:2}}})
      const data=receipt.structuredContent
      assert.equal(data.ok,true,JSON.stringify(data))
      assert.ok(['proven','broken','unknown'].includes(data.label))
      assert.ok(data.result.rules.length>0,'source must be extracted')
      assert.ok(data.result.rules.every(rule=>rule.ok),'supported fixtures must not be refused')
      const stated=data.result.rules.flatMap(rule=>rule.laws)
      assert.ok(stated.length>0,'stated source laws must be read')
      const bounded=stated.find(law=>law.name==='bounded count')
      assert.ok(bounded,'bounded count law must be read')
      assert.equal(bounded.translation,'sampled','preserve native sampling evidence for this release baseline')
      assert.equal(bounded.verdict,version==='bad'?'broken':'proven')
      assert.equal(data.label,version==='bad'?'broken':'proven')
      if(version==='bad')assert.ok(bounded.run?.length,'broken edit needs its real run')
      else assert.ok(bounded.translationChecks>0,'proof requires native law observations')
      assert.match(data.subject.revision,/^[a-f0-9]{64}$/)
      if(previous)assert.notEqual(data.subject.revision,previous,'edit must change bound revision')
      previous=data.subject.revision
      mathematical.push({version,laws:data.result.rules.flatMap(rule=>rule.laws).map(law=>({name:law.name,sourceVerdict:law.verdict,translation:law.translation,kernelProven:law.kernelProven}))})
      for(const law of data.result.rules.flatMap(rule=>rule.laws)){
        if(law.translation==='unchecked')assert.notEqual(law.verdict,'proven','no promotion of unchecked native evidence')
        if(law.verdict==='broken')assert.ok(law.run?.length,'broken requires a real run')
        if(law.verdict==='unknown')assert.ok(law.why,'unknown requires reason')
      }
      // Record actual existing-engine outcomes, including translation-unknown. No invented expectations.
      console.log(JSON.stringify({direction:'agent-observation',file,version,label:data.label,revision:data.subject.revision,laws:data.result.rules.flatMap(rule=>rule.laws),proposed:data.result.rules.flatMap(rule=>rule.proposed)}))
    }
    const first=mathematical[0].laws.find(l=>l.name==='bounded count')
    const last=mathematical[2].laws.find(l=>l.name==='bounded count')
    if(typeof first?.kernelProven==='boolean'&&typeof last?.kernelProven==='boolean'){
      assert.equal(first.kernelProven,true,'good model mathematical evidence')
      assert.equal(last.kernelProven,false,'bad edit must lose mathematical proof without fabricating a source run')
    }
    console.log(JSON.stringify({direction:'agent-mathematical-evidence',language:ext,observed:mathematical,sourceJournalLimitation:true}))
  }
}finally{
  child.stdin.end()
  await new Promise((resolve,reject)=>{
    const deadline=setTimeout(()=>{child.kill('SIGKILL')},5000)
    const closed=(code,signal)=>{clearTimeout(deadline);if(code!==0||signal)reject(new Error(`MCP server did not close cleanly: ${code}/${signal}`));else resolve()}
    if(child.exitCode!==null||child.signalCode!==null)closed(child.exitCode,child.signalCode)
    else child.once('close',closed)
  })
  rmSync(root,{recursive:true,force:true})
}
