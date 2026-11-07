import {expect,test} from 'bun:test'
import {all,any,get,ite,less,minus,n,not,plus,same,times,x} from '../../core/machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {booleanCore} from './boolean-core.ts'
for(const supported of [true,false])test(`Boolean union core ${supported?'checks membership cases':'does not invent the subset premise'}`,()=>{
 const a=same(get('A',x('w')),n(1)),b=same(get('B',x('w')),n(1)),s={op:'<=' as const,a:n(1),b:get('S',x('w'))},bit=(c:Parameters<typeof ite>[0])=>ite(c,n(1),n(0))
 const left=plus(bit(all(a,not(s))),bit(s)),right=plus(plus(bit(all(a,not(b))),bit(all(a,b))),bit(all(b,not(a))))
 const head={op:'<=' as const,a:x('count'),b:n(0)},g={name:'union core',hyps:[...(supported?[any(not(s),b)]:[]),any(head,less(right,left)),not(head)]},tree=booleanCore(g,new Map(),new Set(['w']),clock()+1000,[])
 if(supported){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
})

for(const equal of [true,false])test(`witness key congruence ${equal?'checks a natural-subtraction alias':'does not assume row equality'}`,()=>{
 const forward={row:1,actor:-1},back={row:-1,actor:1},path:Path=equal?new Map([[canon(forward),{lin:forward,holds:true}],[canon(back),{lin:back,holds:true}]]):new Map()
 const shifted=minus(plus(times(4,x('row')),x('member')),times(4,x('actor'))),g={name:'key alias',hyps:[same(get('Set',shifted),n(1)),same(get('Set',x('member')),n(0))]}
 const tree=booleanCore(g,path,new Set(['member']),clock()+1000,[])
 if(equal){expect(tree).toBeDefined();if(tree)expect(check(g,tree,path)).toBe(true)}else expect(tree).toBeUndefined()
})
