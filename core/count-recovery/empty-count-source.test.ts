import {expect,test} from 'bun:test'
import {all,get,n,not,same,x,type E} from '../machine.ts'
import {emptyCountSource} from './empty-count-source.ts'
const member=(row:string)=>same(get('Cells',{op:'add',a:{op:'mul',k:17,a:x(row)},b:x('w')}),n(1))
const difference:E={op:'if',c:all(member('a'),not(member('b'))),then:n(1),else:n(0)}
test('an equal-row difference is an independent empty-count candidate',()=>{
 expect(emptyCountSource(difference,{a:x('i'),b:x('i')})).toBe(true)
 expect(emptyCountSource(difference)).toBe(false)
 expect(emptyCountSource(difference,{a:x('i'),b:x('j')})).toBe(false)
})
test('a search hint never treats matching positive membership as empty',()=>{
 expect(emptyCountSource({op:'if',c:all(member('a'),member('a')),then:n(1),else:n(0)})).toBe(false)
 expect(emptyCountSource({op:'if',c:all(member('a'),not(member('a'))),then:n(1),else:n(2)})).toBe(false)
})
test('nested zero branches and exhausted syntax bounds stay conservative',()=>{
 expect(emptyCountSource({op:'if',c:member('a'),then:n(0),else:n(0)})).toBe(true)
 let deep:E=n(0);for(let i=0;i<140;i++)deep={op:'if',c:member('a'),then:deep,else:n(0)}
 expect(emptyCountSource(deep)).toBe(false)
})
