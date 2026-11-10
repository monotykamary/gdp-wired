import {expect,test} from 'bun:test'
import {WallProfiler} from './wall-profile.ts'
test('wall profile accounts for nested phases without double counting',()=>{
 let now=0;const p=new WallProfiler(true,()=>now)
 expect(p.run('outer',()=>{now=2;p.run('child',()=>{now=7});now=10;return 42})).toBe(42)
 expect(p.snapshot().outer).toMatchObject({calls:1,wallMs:5,inclusiveMs:10})
 expect(p.snapshot().child).toMatchObject({calls:1,wallMs:5,inclusiveMs:5})
})
test('native subphases are subtracted and thrown calls still close their timer',()=>{
 let now=0;const p=new WallProfiler(true,()=>now)
 expect(()=>p.run('search',()=>{now=5;p.native('unfold',3);throw new Error('sentinel')})).toThrow('sentinel')
 expect(p.snapshot().search).toMatchObject({wallMs:2,inclusiveMs:5})
 expect(p.snapshot().unfold).toMatchObject({wallMs:3})
 p.run('after',()=>{now=7})
 expect(p.snapshot().after).toMatchObject({wallMs:2})
})
test('disabled profiling does not read its clock or change a result',()=>{
 const p=new WallProfiler(false,()=>{throw new Error('clock must stay unused')})
 expect(p.run('off',()=>17)).toBe(17)
 expect(p.snapshot()).toEqual({})
})
