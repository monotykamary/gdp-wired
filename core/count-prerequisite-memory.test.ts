import {expect,test} from 'bun:test'
import {prepareCountPrerequisiteMemory,type CountRememberedScope} from './count-prerequisite-memory.ts'
const scope=(name:string,...premises:string[]):CountRememberedScope=>({owner:{name},premises:premises.map(name=>({name}))})
test('a valid held scope and its discovery history survive a fallback',()=>{
 const machine={step:'same'},family=[{name:'a',value:1},{name:'b',value:2}]
 const first=prepareCountPrerequisiteMemory<CountRememberedScope>(undefined,machine,family).state,held=scope('a','b')
 first.scopes.set('a',held);first.committed.add('a');first.discovered.add('b')
 const next=prepareCountPrerequisiteMemory(first,{step:'same'},structuredClone(family))
 expect(next.state.scopes.get('a')).toBe(held);expect(next.invalidated).toEqual([])
 expect(next.state.committed.has('a')).toBe(true);expect(next.state.discovered.has('b')).toBe(true)
})
test('changed or removed actual premises invalidate held users transitively',()=>{
 const family=[{name:'a',value:1},{name:'b',value:2},{name:'c',value:3}]
 const state=prepareCountPrerequisiteMemory<CountRememberedScope>(undefined,{},family).state
 state.scopes.set('a',scope('a','b'));state.scopes.set('b',scope('b','c'));state.scopes.set('c',scope('c'))
 state.committed.add('a');state.committed.add('b');state.committed.add('c')
 const next=prepareCountPrerequisiteMemory(state,{},family.slice(0,2))
 expect(new Set(next.invalidated)).toEqual(new Set(['a','b','c']));expect(next.state.scopes.size).toBe(0);expect(next.state.committed.size).toBe(0)
})
test('unrelated family growth does not invalidate a held proof or repeat discovery',()=>{
 const first=prepareCountPrerequisiteMemory<CountRememberedScope>(undefined,{},[{name:'a'}]).state,held=scope('a')
 first.scopes.set('a',held);first.discovered.add('a');first.failed.add('old')
 const next=prepareCountPrerequisiteMemory(first,{},[{name:'a'},{name:'new'}])
 expect(next.state.scopes.get('a')).toBe(held);expect(next.state.discovered.has('a')).toBe(true)
 expect(next.state.failed.size).toBe(0)
})
test('a changed machine starts new scheduling state and reports invalidation',()=>{
 const first=prepareCountPrerequisiteMemory<CountRememberedScope>(undefined,{step:1},[{name:'a'}]).state
 first.scopes.set('a',scope('a'));first.discovered.add('a')
 const next=prepareCountPrerequisiteMemory(first,{step:2},[{name:'a'}])
 expect(next.invalidated).toEqual(['a']);expect(next.state.scopes.size).toBe(0);expect(next.state.discovered.size).toBe(0)
})
