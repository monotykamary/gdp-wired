import {expect,test} from 'bun:test'
import {type Count,frameOk} from '../kernel/kernel.ts'
import {get,n,x} from './machine.ts'
import {clock} from '../kernel/prove.ts'
import {FrameFactPool} from './count-emitter-frame-pool.ts'
const body=get('R',x('k')),counts:Count[]=[{v:'pre',key:'k',below:n(4),body},{v:'post',key:'k',below:n(4),body:{op:'if',c:{op:'=',a:x('op'),b:n(1)},then:body,else:get('S',x('k'))}}]
const op=[{op:1,'1':-1},{op:-1,'1':1}]
test('per-fact guards discard unrelated path decisions and reuse the checked frame',()=>{
 const frames:Parameters<typeof frameOk>[1][]=[],pool=new FrameFactPool(counts,frames,clock()+500)
 expect(pool.offer({post:'post',pre:'pre',when:[...op,{irrelevant:1,'1':-3}]})).toBe(true)
 expect(frames.length).toBe(1);expect(frames[0]!.when.length).toBeLessThan(3);expect(frameOk(counts,frames[0]!)).toBe(true)
 const before=pool.stats().validated
 expect(pool.offer({post:'post',pre:'pre',when:[...op,{other:-1,'1':2}]})).toBe(true)
 expect(frames.length).toBe(1);expect(pool.stats().validated).toBe(before);expect(pool.stats().reused).toBe(1)
})
test('pair equality is symmetric but never leaks to a different count environment',()=>{
 const frames:Parameters<typeof frameOk>[1][]=[],pool=new FrameFactPool(counts,frames,clock()+500)
 expect(pool.offer({post:'post',pre:'pre',when:op})).toBe(true)
 expect(pool.offer({post:'pre',pre:'post',when:op})).toBe(true);expect(frames.length).toBe(1)
 const broken=counts.map(c=>c.v==='post'?{...c,body:get('wrong',x('k'))}:c),other=new FrameFactPool(broken,[],clock()+500)
 expect(other.offer({post:'post',pre:'pre',when:op})).toBe(false);expect(other.frames.length).toBe(0)
})
test('wrong branch, missing count and changed key are refused',()=>{
 const pool=new FrameFactPool(counts,[],clock()+500)
 expect(pool.offer({post:'post',pre:'pre',when:[{op:1}]})).toBe(false)
 expect(pool.offer({post:'absent',pre:'pre',when:op})).toBe(false)
 const other=new FrameFactPool(counts.map(c=>c.v==='post'?{...c,key:'otherKey'}:c),[],clock()+500)
 expect(other.offer({post:'post',pre:'pre',when:op})).toBe(false)
})
test('a late request never adds a frame; seeded arrays are rejected',()=>{
 const pool=new FrameFactPool(counts,[],clock()-1)
 expect(pool.offer({post:'post',pre:'pre',when:op})).toBe(false);expect(pool.frames.length).toBe(0)
 expect(()=>new FrameFactPool(counts,[{post:'post',pre:'pre',when:op}],clock()+500)).toThrow('start empty')
})
