import {test,expect} from 'bun:test'
import {boundedResearch,ResearchStop} from './bounded-research.ts'
import {costs} from '../../core/solver.ts'
import {fullWork,fullRate} from '../../kernel/prove.ts'
test('research cap stops real work and restores counter descriptors',()=>{
 const descriptor=Object.getOwnPropertyDescriptor(costs,'fm'),start=fullWork();let failure:unknown
 try{boundedResearch(1,1000,()=>{for(let i=0;i<10000;i++)costs.fm++})}catch(e){failure=e}
 expect(failure instanceof ResearchStop).toBe(true)
 expect((failure as ResearchStop).reason).toBe('counted-cap')
 expect((fullWork()-start)/fullRate).toBeGreaterThanOrEqual(1)
 const after=Object.getOwnPropertyDescriptor(costs,'fm')!;expect(Object.hasOwn(after,'get')).toBe(Object.hasOwn(descriptor??{},'get'));expect(after.writable).toBe(descriptor?.writable)
})
test('research cap restores descriptors after an unrelated error',()=>{
 expect(()=>boundedResearch(100,1000,()=>{throw new Error('caller')})).toThrow('caller')
 expect(Object.getOwnPropertyDescriptor(costs,'fm')?.writable).toBe(true)
})
