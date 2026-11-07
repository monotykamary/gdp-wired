import {expect,test} from 'bun:test'
import {get,ite,n,x} from '../../core/machine.ts'
import {check} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {carriedCase} from './carried-case.ts'
for(const impossible of [true,false])test(`carried witness split ${impossible?'checks both branches':'cannot prove a satisfiable goal'}`,()=>{
 const member={op:'<=' as const,a:n(1),b:get('Input',x('witness'))},g={name:'carried core',hyps:[{op:'<=' as const,a:ite(member,n(1),n(impossible?2:0)),b:n(impossible?0:1)}]}
 const tree=carriedCase(g,new Map(),['Input'],new Set(['witness']),clock()+1000,[])
 if(impossible){expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}else expect(tree).toBeUndefined()
})
