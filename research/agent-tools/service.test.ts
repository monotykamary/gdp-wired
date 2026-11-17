import {test,expect} from 'bun:test'
import {proofSummary,execute} from './service.ts'
import {budget,budgetLaws} from './examples.ts'
import {handle} from './stdio.ts'
import {toolNames} from './protocol.ts'

test('unchecked proof is never reported proven',()=>{
  expect(proofSummary({proven:true,checked:false}).status).toBe('unchecked')
  expect(proofSummary({proven:false,checked:true}).status).toBe('not-proven')
  expect(proofSummary({proven:true,checked:true}).status).toBe('proven')
})
test('MCP protocol validates methods and ignores notifications',async()=>{
  expect(await handle({jsonrpc:'2.0',method:'notifications/initialized'})).toBeNull()
  const unknown=await handle({jsonrpc:'2.0',id:3,method:'not-a-method'})
  expect((unknown?.error as {code:number}).code).toBe(-32601)
  const listed=await handle({jsonrpc:'2.0',id:4,method:'tools/list'})
  expect((listed?.result as {tools:{name:string}[]}).tools.map(t=>t.name)).toEqual(toolNames)
})
test('status does not accept labels supplied by a client',async()=>{
  const r=await handle({jsonrpc:'2.0',id:5,method:'tools/call',params:{name:'status',arguments:{unit:'budget',revision:'0'.repeat(64),label:'harness-checked'}}})
  const data=(r?.result as {structuredContent:{ok:boolean,refusal:{code:string}}}).structuredContent
  expect(data.ok).toBe(false);expect(data.refusal.code).toBe('unsupported-field')
})

test('counted proof does not consult wall clocks',()=>{
  const now=Date.now,perf=performance.now
  const forbidden=():never=>{throw Error('wall-clock consultation forbidden')}
  try {
    Date.now=forbidden;performance.now=forbidden
    const result=execute('prove',{subject:budget(),laws:budgetLaws,budget:{work:500000}})
    expect(result.ok).toBe(true)
  }finally{Date.now=now;performance.now=perf}
})
test('unsafe numeric traces refuse instead of fabricating integer arithmetic',()=>{
  const subject=budget(true)
  subject.rule.step.state!.spent={op:'add',a:{op:'const',value:Number.MAX_SAFE_INTEGER},b:{op:'const',value:Number.MAX_SAFE_INTEGER}}
  const result=execute('why_not',{subject,laws:[{name:'spent remains zero',holds:{op:'=',a:{op:'var',name:'spent'},b:{op:'const',value:0}}}],budget:{work:500000}})
  expect(result.ok).toBe(false)
  expect('refusal' in result&&result.refusal.code).toBe('numeric-range-refused')
})
