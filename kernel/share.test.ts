import {expect, test} from 'bun:test'
import {shareTerms} from './share.ts'

test('structural sharing ignores field insertion order, not operands or types', () => {
  const share = shareTerms(), x = {op:'var', name:'x'}, y = {op:'var', name:'y'}
  const a = share({op:'add', a:x, b:y})
  expect(share({b:{name:'y',op:'var'},op:'add',a:{name:'x',op:'var'}})).toBe(a)
  expect(share({op:'add', a:y, b:x})).not.toBe(a)
  expect(share({op:'const',value:0})).not.toBe(share({op:'const',value:-0}))
  expect(share({value:1})).not.toBe(share({value:'1'}))
  expect(share({value:null})).not.toBe(share({value:'null'}))
  expect(share({value:undefined})).not.toBe(share({}))
  expect(share([x,y])).not.toBe(share([y,x]))
  expect(share([x,y])).not.toBe(share({0:x,1:y}))
})

test('sharing is reader-local and does not mutate inputs', () => {
  const share = shareTerms(), first = Object.freeze({op:'var',name:'x'}), second = Object.freeze({...first})
  expect(share(first)).toBe(first)
  const input = Object.freeze({op:'add',a:second,b:second}), out=share(input)
  expect(out.a).toBe(first)
  expect(input.a).toBe(second)
  expect(out).not.toBe(input)
  expect(share(out)).toBe(out)
  expect(shareTerms()(second)).toBe(second)
})
