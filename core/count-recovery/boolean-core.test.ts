import {expect,test} from 'bun:test'
import {all,any,atMost,get,ite,less,minus,n,not,plus,same,times,x} from '../machine.ts'
import {canon,check,facts,type Path} from '../../kernel/kernel.ts'
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

test('inactive Boolean arms stay pruned inside a forced indicator',()=>{
 const mode=same(x('mode'),n(6)),inactive=atMost(n(1),get('S',x('w'))),active=same(get('Config',x('w')),n(1))
 const bad=less(n(0),ite(any(all(same(x('mode'),n(0)),inactive),all(mode,active)),n(1),n(0)))
 const path:Path=new Map([...facts(mode,new Map()),...facts(less(n(0),x('mode')),new Map()),...facts(bad,new Map())].map(lin=>[canon(lin),{lin,holds:true}]))
 const cs=booleanCandidates({name:'condition roles',hyps:[bad]},path,new Set(['w']),true)
 expect(cs.some(p=>JSON.stringify(p.c)===JSON.stringify(active))).toBe(true)
 expect(cs.some(p=>JSON.stringify(p.c).includes('"map":"S"'))).toBe(false)
})

test('a forced comparison still exposes its conditional operands',()=>{
 const a=same(get('A',x('w')),n(1)),b=same(get('B',x('w')),n(1)),bad=less(ite(a,n(1),n(0)),ite(b,n(1),n(0)))
 const path:Path=new Map(facts(bad,new Map()).map(lin=>[canon(lin),{lin,holds:true}])),g={name:'forced comparison',hyps:[bad]},cs=booleanCandidates(g,path,new Set(['w']),true)
 for(const c of [a,b])expect(cs.some(p=>JSON.stringify(p.c)===JSON.stringify(c))).toBe(true)
})

for(const fixed of [true,false])test(`inactive scalar writes ${fixed?'do not occupy the witness case pool':'remain open without the selector'}`,()=>{
 const old=get('Cell',x('w'));let written=old
 for(let i=0;i<6;i++)written=ite(same(x('mode'),n(i)),get(`Other${i}`,x('w')),written)
 const g={name:'scalar selector',hyps:[...(fixed?[same(x('mode'),n(6))]:[]),less(written,old)]},tree=booleanCore(g,new Map(),new Set(['w']),clock()+1000,[],{scalarGuards:true})
 if(fixed){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
})

for(const packed of [false,true])for(const guarded of [true,false])test(`${packed?'packed ':''}conditional indicator copy ${guarded?'checks a non-newer destination':'does not invent the version guard'}`,()=>{
 const owner=x('owner'),source=x('source'),w=x('w'),tw=get('term',w),ts=get('term',source),to=get('term',owner),vw=get('version',w),vs=get('version',source),vo=get('version',owner)
 const writtenTerm=ite(same(w,owner),ts,tw),writtenVersion=ite(same(w,owner),vs,vw),sourceKey=plus(times(64,source),w),ownerKey=plus(times(64,owner),w)
 const member=get('member',packed?sourceKey:w),copied=packed?ite(atMost(owner,source),get('member',plus(ownerKey,times(64,minus(source,owner)))),get('member',minus(ownerKey,times(64,minus(owner,source))))):member
 const before=all(same(member,n(1)),less(get('clock',w),ts),not(any(less(ts,tw),all(same(ts,tw),less(vs,vw))))),after=all(same(copied,n(1)),less(get('clock',w),ts),not(any(less(ts,writtenTerm),all(same(ts,writtenTerm),less(vs,writtenVersion)))))
 const guard=not(any(less(ts,to),all(same(ts,to),less(vs,vo)))),g={name:'conditional indicator copy',hyps:[...(guarded?[guard]:[]),less(ite(before,n(1),n(0)),ite(after,n(1),n(0)))]}
 const tree=booleanCore(g,new Map(),new Set(['w']),clock()+1000,[],{extended:true,scalarGuards:true})
 if(guarded){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
})

for(const zero of [true,false])test(`witness field comparisons ${zero?'expose an impossible indicator':'remain unproved without the bound'}`,()=>{
 const comparison=less(get('Value',x('w')),get('Cutoff',x('row'))),g={name:'indicator condition',hyps:[less(n(0),ite(comparison,n(1),n(0))),...(zero?[same(get('Cutoff',x('row')),n(0))]:[])]}
 expect(booleanCandidates(g,new Map(),new Set(['w']),true).some(p=>JSON.stringify(p.c)===JSON.stringify(comparison))).toBe(true)
 const tree=booleanCore(g,new Map(),new Set(['w']),clock()+1000,[],{extended:true})
 if(zero){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
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
