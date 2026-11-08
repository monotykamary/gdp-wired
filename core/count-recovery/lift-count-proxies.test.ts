import {expect,test} from 'bun:test'
import {get,minus,n,same,x} from '../machine.ts'
import {canon,check,linear,type Path} from '../../kernel/kernel.ts'
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
for(const bindings of [true,false])test(`composite count terms ${bindings?'lift':'cannot invent bindings'}`,()=>{
 const a=x('leftCount'),b=x('rightCount'),left=get('Rows',n(0)),right=get('Rows',n(1))
 const part={name:'numeric subtraction',hyps:[{op:'<=' as const,a:minus(a,b),b:n(0)},{op:'<' as const,a:b,b:a}]}
 const whole={name:'original subtraction',hyps:[{op:'<=' as const,a:minus(left,right),b:n(0)},{op:'<' as const,a:b,b:a},...(bindings?[same(a,left),same(b,right)]:[])]}
 const out=grow(part,new Map(),{nodes:0,until:clock()+500})
 expect('tree'in out).toBe(true)
 if('tree'in out){const proof=liftCountProxies(part,whole,out.tree,[['leftCount','Rows',n(0)],['rightCount','Rows',n(1)]]);if(bindings){expect(proof).toBeDefined();if(proof)expect(check(whole,proof)).toBe(true)}else expect(proof).toBeUndefined()}
})
test('numeric count bindings retain constraints in an existing guard path',()=>{
 const r=x('count'),cell=get('Rows',n(0)),lin=linear(cell,new Map())!,path:Path=new Map([[canon(lin),{lin,holds:true}]])
 const part={name:'numeric guarded count',hyps:[same(r,cell),{op:'<=' as const,a:n(1),b:r}]},whole={name:'original guarded count',hyps:[same(r,cell),{op:'<=' as const,a:n(1),b:cell}]}
 const out=grow(part,path,{nodes:0,until:clock()+500})
 expect('tree'in out).toBe(true)
 if('tree'in out){const tree=liftCountProxies(part,whole,out.tree,[['count','Rows',n(0)]],path,path);expect(tree).toBeDefined();if(tree)expect(check(whole,tree,path)).toBe(true)}
 expect('tree'in grow({name:'disconnected',hyps:[{op:'<=' as const,a:n(1),b:r}]},path,{nodes:0,until:clock()+500})).toBe(false)
})
test('a deferred transport is not an accepted proof',()=>{
 const goal={name:'possible',hyps:[same(x('x'),n(0))]},invalid={leaf:[]}
 expect(liftCountProxies(goal,goal,invalid,[])).toBeUndefined()
 const proposal=liftCountProxies(goal,goal,invalid,[],new Map(),new Map(),undefined,{deferCheck:true})
 expect(proposal).toBeDefined()
 if(proposal)expect(check(goal,proposal)).toBe(false)
})
for(const deferred of [false,true])for(const guarded of [true,false])test(`count proxy domain guards ${guarded?'are checked':'cannot be assumed'} (deferred=${deferred})`,()=>{
 const r=x('count'),key=x('key'),cell=get('Rows',key)
 const part={name:'numeric',hyps:[{op:'<=' as const,a:{op:'mul' as const,k:2,a:r},b:n(1)},{op:'<=' as const,a:n(1),b:r}]}
 const whole={name:'guarded original',hyps:[{op:'<=' as const,a:{op:'mul' as const,k:2,a:cell},b:n(1)},{op:'or' as const,xs:[{op:'<=' as const,a:n(4),b:key},same(r,cell)]},{op:'<=' as const,a:n(1),b:r},...(guarded?[{op:'<' as const,a:key,b:n(4)}]:[])]}
 const out=grow(part,new Map(),{nodes:0,until:clock()+500})
 expect('tree'in out).toBe(true)
 if('tree'in out){
  const proof=liftCountProxies(part,whole,out.tree,[['count','Rows',key]],new Map(),new Map(),undefined,{deferCheck:deferred})
  if(guarded){expect(proof).toBeDefined();if(proof)expect(check(whole,proof)).toBe(true)}
  else expect(proof).toBeUndefined()
 }
})
