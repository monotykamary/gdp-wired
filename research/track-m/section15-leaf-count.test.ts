import {test,expect} from 'bun:test'
import {all,any,n,less,x,type C} from '../../core/machine.ts'
import {guardLeafCount} from './section15-leaf-count.ts'
const a:C={op:'<=',a:x('a'),b:n(0)},b:C={op:'<=',a:x('b'),b:n(0)},c:C={op:'<=',a:x('c'),b:n(0)}
test('counts conjunction short-circuit leaves exactly',()=>{expect(guardLeafCount(all(a,b,c),[a,b,c],new Map())).toBe(4)})
test('counts mixed Boolean guard leaves without assuming a conjunction',()=>{expect(guardLeafCount(any(all(a,b),c),[a,b,c],new Map())).toBe(7)})
test('a decided guard needs one leaf and repeated tests add none',()=>{expect(guardLeafCount(all(a,a),[a,a],new Map())).toBe(2);expect(guardLeafCount(less(n(0),n(1)),[],new Map())).toBe(1)})
