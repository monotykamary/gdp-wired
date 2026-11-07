import {expect,test} from 'bun:test'
import {get,n,same,x} from '../../core/machine.ts'
import {check} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {liftCountProxies} from './lift-count-proxies.ts'
test('count proxies lift through explicit read equalities without whole-goal search',()=>{
 const r=x('count'),cell=get('Rows',n(0)),part={name:'numeric',hyps:[{op:'<=' as const,a:r,b:n(0)},{op:'<=' as const,a:n(1),b:r}]},whole={name:'original',hyps:[{op:'<=' as const,a:cell,b:n(0)},same(r,cell),{op:'<=' as const,a:n(1),b:r}]}
 const out=grow(part,new Map(),{nodes:0,until:clock()+500})
 expect('tree'in out).toBe(true)
 if('tree'in out){const proof=liftCountProxies(part,whole,out.tree,[['count','Rows',n(0)]]);expect(proof).toBeDefined();if(proof)expect(check(whole,proof)).toBe(true)}
})
test('count proxy transport cannot invent a missing read equality',()=>{
 const r=x('count'),cell=get('Rows',n(0)),part={name:'numeric',hyps:[{op:'<=' as const,a:r,b:n(0)},{op:'<=' as const,a:n(1),b:r}]},whole={name:'possible',hyps:[{op:'<=' as const,a:cell,b:n(0)},{op:'<=' as const,a:n(1),b:r}]}
 const out=grow(part,new Map(),{nodes:0,until:clock()+500})
 if('tree'in out)expect(liftCountProxies(part,whole,out.tree,[['count','Rows',n(0)]])).toBeUndefined()
 else throw new Error('expected the contradictory numeric fixture to be proved')
})
for(const guarded of [true,false])test(`count proxy domain guards ${guarded?'are checked':'cannot be assumed'}`,()=>{
 const r=x('count'),key=x('key'),cell=get('Rows',key)
 const part={name:'numeric',hyps:[{op:'<=' as const,a:{op:'mul' as const,k:2,a:r},b:n(1)},{op:'<=' as const,a:n(1),b:r}]}
 const whole={name:'guarded original',hyps:[{op:'<=' as const,a:{op:'mul' as const,k:2,a:cell},b:n(1)},{op:'or' as const,xs:[{op:'<=' as const,a:n(4),b:key},same(r,cell)]},{op:'<=' as const,a:n(1),b:r},...(guarded?[{op:'<' as const,a:key,b:n(4)}]:[])]}
 const out=grow(part,new Map(),{nodes:0,until:clock()+500})
 expect('tree'in out).toBe(true)
 if('tree'in out){
  const proof=liftCountProxies(part,whole,out.tree,[['count','Rows',key]])
  if(guarded){expect(proof).toBeDefined();if(proof)expect(check(whole,proof)).toBe(true)}
  else expect(proof).toBeUndefined()
 }
})
