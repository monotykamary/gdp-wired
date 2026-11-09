import {expect,test} from 'bun:test'
import {x} from '../../core/machine.ts'
import {chooseRowPair,rowProbe} from './section15-row-probe.ts'
const pairs=[[x('a'),x('r')],[x('b'),x('r')]] as const
test('row selection needs a model and prefers the violated equal source row',()=>{
 expect(chooseRowPair(pairs,new Map(),undefined,['a'])).toBeUndefined()
 expect(chooseRowPair(pairs,new Map(),{a:2,b:3,r:2},['a','b'])).toBe(0)
 expect(chooseRowPair(pairs,new Map(),{a:2,b:3,r:3},['a','b'])).toBe(1)
 expect(chooseRowPair(pairs,new Map(),{a:2,b:3},['a'])).toBeUndefined()
})
test('probe state is scoped and nested observations do not leak',()=>{
 expect(rowProbe.active).toBe(false)
 const outer=rowProbe.run(()=>{rowProbe.remember({a:1},['a']);const inner=rowProbe.run(()=>{rowProbe.remember({b:2},['b']);return 7});expect(inner.point).toEqual({b:2});return 3})
 expect(outer.value).toBe(3);expect(outer.point).toEqual({a:1});expect(rowProbe.active).toBe(false)
 const error=new Error('probe exception');expect(()=>rowProbe.run(()=>{throw error})).toThrow(error);expect(rowProbe.active).toBe(false)
})
