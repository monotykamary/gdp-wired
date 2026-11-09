import {get,minus,n,same,x} from '../../core/machine.ts'
import {check} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {liftCountProxies} from './lift-count-proxies.ts'
console.error('loaded')
const r=x('count'),cell=get('Rows',n(0)),part={name:'numeric',hyps:[{op:'<=' as const,a:r,b:n(0)},{op:'<=' as const,a:n(1),b:r}]},whole={name:'original',hyps:[{op:'<=' as const,a:cell,b:n(0)},same(r,cell),{op:'<=' as const,a:n(1),b:r}]}
console.error('grow simple')
const out=grow(part,new Map(),{nodes:0,until:clock()+500})
console.error('grown simple', 'tree'in out)
if('tree'in out){console.error('lift simple');const proof=liftCountProxies(part,whole,out.tree,[['count','Rows',n(0)]]);console.error('lifted simple',!!proof,proof&&check(whole,proof))}
const a=x('leftCount'),b=x('rightCount'),left=get('Rows',n(0)),right=get('Rows',n(1))
const p={name:'sub',hyps:[{op:'<=' as const,a:minus(a,b),b:n(0)},{op:'<' as const,a:b,b:a}]},w={name:'original sub',hyps:[{op:'<=' as const,a:minus(left,right),b:n(0)},{op:'<' as const,a:b,b:a},same(a,left),same(b,right)]}
console.error('grow sub')
const sub=grow(p,new Map(),{nodes:0,until:clock()+500})
console.error('grown sub','tree'in sub)
if('tree'in sub){console.error('lift sub');const proof=liftCountProxies(p,w,sub.tree,[['leftCount','Rows',n(0)],['rightCount','Rows',n(1)]]);console.error('lifted sub',!!proof,proof&&check(w,proof))}
