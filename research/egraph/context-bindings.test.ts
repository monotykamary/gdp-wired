import {test,expect} from 'bun:test'
import {contextBindings} from './context-bindings.ts'
const context=(bound:string,free='free')=>({m:{step:{flags:{q:{op:'all',key:'node'+bound,c:{op:'var',name:'node'+bound}}}}},laws:[{name:'law',forall:bound,holds:{op:'=',a:{op:'var',name:bound},b:{op:'var',name:free}}}]})
test('context correspondence records scoped binders, skolems and law permutation',()=>{
  const p=contextBindings(context('x'),context('y'))
  expect(p.renamings.x).toBe('y');expect(p.renamings['x#']).toBe('y#');expect(p.renamings.nodex).toBe('nodey');expect(p.lawOrder).toEqual([0])
})
test('free-variable changes and missing laws cannot masquerade as alpha equivalence',()=>{
  expect(()=>contextBindings(context('x'),context('y','changed'))).toThrow('variable mismatch')
  expect(()=>contextBindings(context('x'),{m:context('x').m,laws:[]})).toThrow('law set')
  // A valid scoped alpha change may still be unsafe as a flat metadata renaming.
  expect(()=>contextBindings(context('x','y'),context('y','y'))).toThrow('capture hazard')
  const s={...context('x'),m:{...context('x').m,free:{op:'var',name:'x'}}},t={...context('y'),m:{...context('y').m,free:{op:'var',name:'x'}}}
  expect(()=>contextBindings(s,t)).toThrow('capture hazard')
})
