import {test,expect} from 'bun:test'
import {safetyContext} from './historical/safety-context.ts'
import {eprScope} from '../../kernel/prove.ts'
import {withProtocolPatterns} from './pattern-once.ts'
test('pattern scope uses the public API once and does not refine an unknown result',()=>{
  const c=safetyContext(),before=JSON.stringify(c.metadata.instances);let calls=0
  const scopeBefore=eprScope.patterns
  const out=withProtocolPatterns(c.input.m,c.input.laws,c.metadata.instances,c.original,()=>{calls++;expect(!!eprScope.patterns).toBe(process.env.GDP_EPR!=='0');return 'unknown'})
  expect(eprScope.patterns).toBe(scopeBefore)
  expect(out).toBe('unknown');expect(calls).toBe(1);expect(JSON.stringify(c.metadata.instances)).toBe(before)
})
test('an interrupted pattern-scoped query is not retried',()=>{
  const c=safetyContext();let calls=0
  expect(()=>withProtocolPatterns(c.input.m,c.input.laws,c.metadata.instances,c.original,()=>{calls++;throw Error('interrupted')})).toThrow('interrupted')
  expect(calls).toBe(1)
})
