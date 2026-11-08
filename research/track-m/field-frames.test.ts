import {expect,test} from 'bun:test'
import {get,ite,n,not,same,x} from '../../core/machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {booleanCore} from './boolean-core.ts'
import {fieldFrames} from './field-frames.ts'
test('field frame candidates keep only requested non-member cells',()=>{
 const before=get('Epoch',x('target')),after=ite(same(x('target'),x('source')),get('Clock',x('source')),before)
 const member=ite(same(x('$member'),x('source')),n(1),get('Members',x('$member')))
 expect(fieldFrames([after,member],[before,get('Members',x('$member'))],new Map())).toEqual([{after,before}])
})
for(const supported of [true,false])test(`a copied equal field ${supported?'checks without fixing the target key':'is not assumed equal'}`,()=>{
 const before=get('Epoch',x('target')),after=ite(same(x('target'),x('source')),get('Clock',x('source')),before)
 const lin={'Clock[source:1]':1,'Epoch[source:1]':-1},back={'Clock[source:1]':-1,'Epoch[source:1]':1},root:Path=supported?new Map([[canon(lin),{lin,holds:true}],[canon(back),{lin:back,holds:true}]]):new Map()
 const g={name:'field frame',hyps:[not(same(after,before))]},tree=booleanCore(g,root,new Set(['target']),clock()+1000,[])
 if(supported){expect(tree).toBeDefined();if(tree)expect(check(g,tree,root)).toBe(true)}else expect(tree).toBeUndefined()
})
