import {expect,test} from 'bun:test'
import {rowCompositionFixture} from './count-row-composition.fixture.ts'
import {countStrategyKind,proveCountStrategyKind,proposeCountStrategyKindForClosing,type NonLiftedCountStrategyKind} from './count-strategies.ts'
test('G7: a guard recipe cannot dispatch the selected row constructor',()=>{
 const {m,law,family}=rowCompositionFixture();expect(countStrategyKind(m,family,law)).toBe('row')
 for(const dispatch of [proveCountStrategyKind,proposeCountStrategyKindForClosing]){
  let requests=0;const events:Record<string,unknown>[]=[]
  const result=dispatch('guard',m,family,law,Infinity,()=>{requests++;return {reads:[],insts:[]}},event=>events.push(event),1000)
  expect(result).toBeUndefined();expect(requests).toBe(0)
  expect(events).toEqual([{strategy:'guard',stage:'decline',reason:'strategy-kind-mismatch',actualKind:'row'}])
 }
})
test('G7: an untyped lifted ID cannot enter the non-lifted numeric seam',()=>{
 const {m,law,family}=rowCompositionFixture();let requests=0;const events:Record<string,unknown>[]=[]
 const result=proposeCountStrategyKindForClosing('lifted' as NonLiftedCountStrategyKind,m,family,law,Infinity,()=>{requests++;return {reads:[],insts:[]}},event=>events.push(event),1000)
 expect(result).toBeUndefined();expect(requests).toBe(0)
 expect(events.some(event=>event.stage==='selected'||event.stage==='search-budget')).toBe(false)
 expect(events[0]?.reason).toBe('strategy-kind-mismatch')
})
