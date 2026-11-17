import {test,expect} from 'bun:test'
import {parseRequest,Refusal,revision,wireJSON} from './protocol.ts'
import {budget,budgetLaws,permits,permitLaws} from './examples.ts'

test('accepts only data, with stable rule/law binding',()=>{
  const q=parseRequest('prove',{subject:budget(),laws:budgetLaws})
  expect(q.subject?.unit).toBe('budget')
  expect(revision(budget(),budgetLaws)).toBe(revision(budget(),budgetLaws))
  expect(revision(budget(),budgetLaws)).not.toBe(revision(budget(true),budgetLaws))
  expect(parseRequest('prove',{subject:permits(),laws:permitLaws}).subject?.unit).toBe('permits')
})
test('refuses code, URLs, prototype names, undeclared variables and labels',()=>{
  for(const args of [{source:'fetch("https://example.com")'},{subject:{...budget(),unit:'__proto__'},laws:budgetLaws},{subject:budget(),laws:[{name:'bad',holds:{op:'=',a:{op:'var',name:'undeclared'},b:{op:'const',value:0}}}]}])expect(()=>parseRequest('prove',args)).toThrow(Refusal)
  expect(()=>parseRequest('status',{unit:'budget',revision:'0'.repeat(64),label:'proven'})).toThrow(Refusal)
})
test('wire numbers preserve bigint and refuse silent nonfinite coercion',()=>{
  expect(JSON.parse(wireJSON({n:42n}))).toEqual({n:{type:'bigint',decimal:'42'}})
  expect(()=>wireJSON({n:Infinity})).toThrow(Refusal)
  expect(()=>wireJSON({n:NaN})).toThrow(Refusal)
})

test('counted bounds reject wall-clock options and preserve zero allowance',()=>{
  expect(parseRequest('prove',{subject:budget(),laws:budgetLaws,budget:{work:0,apiCalls:0}}).budget.work).toBe(0)
  expect(()=>parseRequest('prove',{subject:budget(),laws:budgetLaws,budget:{ms:100}})).toThrow(Refusal)
  expect(()=>parseRequest('prove',{subject:budget(),laws:budgetLaws,budget:{work:Infinity}})).toThrow(Refusal)
})
test('change correspondence is explicit, never inferred by renaming',()=>{
  const after=budget(true);after.rule.inputs=['other']
  expect(()=>parseRequest('check_change',{before:budget(),after,laws:budgetLaws})).toThrow(Refusal)
})
