import {expect,test} from 'bun:test'
import {all,any,atMost,get,ite,less,minus,n,not,plus,same,times,x} from '../../core/machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {booleanCandidates,booleanCore} from './boolean-core.ts'
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

for(const reverse of [false,true])test(`a partition CInst checks directly in ${reverse?'reverse':'forward'} direction`,()=>{
 const a=same(get('A',x('w')),n(1)),b=same(get('B',x('w')),n(1)),bit=(c:Parameters<typeof ite>[0])=>ite(c,n(1),n(0)),sum=plus(bit(all(a,b)),bit(all(a,not(b)))),whole=bit(a)
 const head=atMost(x('countDifference'),n(0)),bad=reverse?less(whole,sum):less(sum,whole),g={name:'partition',hyps:[any(head,bad),not(head)]}
 const tree=booleanCore(g,new Map(),new Set(['w']),clock()+1000,[])
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
})

for(const correct of [true,false])test(`packed copy offsets ${correct?'check through their row-order guard':'do not hide a wrong offset'}`,()=>{
 const source=x('source'),destination=x('destination'),member=x('member'),order=atMost(destination,source),key=plus(times(4,destination),member),offset=times(4,minus(destination,source)),copied=ite(order,plus(key,times(4,minus(source,destination))),minus(key,correct?offset:plus(offset,n(1))))
 const g={name:'copy offset',hyps:[same(get('Packed',copied),n(1)),same(get('Packed',plus(times(4,source),member)),n(0))]}
 expect(booleanCandidates(g,new Map(),new Set(['member'])).some(p=>JSON.stringify(p.c)===JSON.stringify(order))).toBe(true)
 const tree=booleanCore(g,new Map(),new Set(['member']),clock()+1000,[])
 if(correct){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
})

test('primitive copy guards outrank compound cell-key aliases in the fixed pool',()=>{
 const w=x('w'),source=x('source'),destination=x('destination'),guard=atMost(destination,source),keyGuard=same(w,destination),compound=plus(times(4,source),w),g={name:'candidate priority',hyps:[same(ite(guard,get('M',w),get('M',compound)),n(1)),same(ite(keyGuard,n(1),n(0)),n(1))]}
 const candidates=booleanCandidates(g,new Map(),new Set(['w'])),score=(c:unknown)=>candidates.find(p=>JSON.stringify(p.c)===JSON.stringify(c))?.score??0
 expect(score(guard)).toBeGreaterThan(score(same(w,compound)))
 expect(score(keyGuard)).toBeGreaterThan(score(same(w,compound)))
})

test('a point update proposes its witness-versus-actor equality',()=>{
 const choice=same(x('member'),x('actor')),g={name:'point update',hyps:[less(x('old'),ite(choice,n(0),x('old')))]}
 expect(booleanCandidates(g,new Map(),new Set(['member'])).some(({c})=>JSON.stringify(c)===JSON.stringify(choice))).toBe(true)
 const tree=booleanCore(g,new Map(),new Set(['member']),clock()+1000,[])
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
})

for(const supported of [true,false])test(`forced facts leave room for Boolean proposals (${supported?'valid':'missing subset'})`,()=>{
 const a=same(get('A',x('w')),n(1)),b=same(get('B',x('w')),n(1)),s={op:'<=' as const,a:n(1),b:get('S',x('w'))},bit=(c:Parameters<typeof ite>[0])=>ite(c,n(1),n(0))
 const left=plus(bit(all(a,not(s))),bit(s)),right=plus(plus(bit(all(a,not(b))),bit(all(a,b))),bit(all(b,not(a))))
 const head={op:'<=' as const,a:x('count'),b:n(0)},forced=Array.from({length:12},(_,i)=>same(x(`given${i}`),n(1))),g={name:'forced union facts',hyps:[...forced,...(supported?[any(not(s),b)]:[]),any(head,less(right,left)),not(head)]},trace:object[]=[]
 const tree=booleanCore(g,new Map(),new Set(['w']),clock()+1000,trace)
 expect(trace.some(e=>(e as any).stage==='boolean-core'&&(e as any).facts>=12)).toBe(true)
 if(supported){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
})

for(const equal of [true,false])test(`witness-domain guards ${equal?'follow a checked row equality':'are not assumed across rows'}`,()=>{
 const forward={row:1,actor:-1},back={row:-1,actor:1},path:Path=equal?new Map([[canon(forward),{lin:forward,holds:true}],[canon(back),{lin:back,holds:true}]]):new Map()
 const start=times(64,x('actor')),key=plus(times(64,x('row')),x('member')),inside=all(atMost(start,key),less(key,plus(start,x('size')))),value=ite(inside,get('New',x('member')),get('Old',x('member')))
 const g={name:'row domain',hyps:[less(x('member'),x('size')),atMost(x('size'),n(64)),not(same(value,get('New',x('member'))))]},tree=booleanCore(g,path,new Set(['member']),clock()+1000,[])
 if(equal){expect(tree).toBeDefined();if(tree)expect(check(g,tree,path)).toBe(true)}else expect(tree).toBeUndefined()
})
