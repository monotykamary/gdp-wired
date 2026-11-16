import {expect,test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {validateKnownFailuresPolicy} from './known-failures.ts'

const retired=[
  'ordered.test.ts :: a queue of numbers: the first and last items, pop(0), checked against the code; a take removes the first item',
  'ordered.test.ts :: an order book of two lists: price-time priority proven, a self-trade found and replayed',
  'rounding.test.ts :: round(a / k) at |a| of 2^52 or more: an edge, the claim below it',
]
test('repaired ordered-source and rounding cases cannot be accepted as known failures again',()=>{
  const jobs=JSON.parse(readFileSync(new URL('../../supercomputer/suite.json',import.meta.url),'utf8'))
  const policy=validateKnownFailuresPolicy(JSON.parse(readFileSync(new URL('./known-failures.json',import.meta.url),'utf8')),jobs)
  const trading=policy.entries.find(entry=>entry.job==='trading')!
  expect(trading).toBeDefined()
  for(const name of retired)expect(trading.signature.failedTests).not.toContain(name)
  expect(trading.signature.failedTests).toHaveLength(3)
  expect(trading.signature.diagnostics).toEqual(['error: expect(received).toBe(expected)','error: expect(received).toEqual(expected)','error: expect(received).toEqual(expected)'])
})
