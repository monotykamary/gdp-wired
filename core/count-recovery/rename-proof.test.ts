import {expect,test} from 'bun:test'
import {type Goal,type Path,canon,check} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {all,atMost,get,ite,less,n,not,plus,same,times,x} from '../machine.ts'
import {renameProof} from './rename-proof.ts'
const swap={left:'right',right:'left'}
const path=(rows:Record<string,number>[]):Path=>new Map(rows.map(lin=>[canon(lin),{lin,holds:true}]))
const proof=(g:Goal,p:Path)=>{const out=grow(g,p,{nodes:0,until:clock()+1000});if(!('tree'in out))throw new Error('fixture must refute');return out.tree}
test('ordinary row proofs are instantiated by used-row matching, not trusted symmetry',()=>{
 const a=x('left'),b=x('right'),g={name:'row order',hyps:[less(a,b)]}
 const p=path([{left:1,actor:-1},{actor:1,left:-1},{right:1,actor:-1}]),q=path([{right:1,actor:-1},{actor:1,right:-1},{left:1,actor:-1}])
 const source=proof(g,p),mirrored=renameProof(g,source,p,q,swap,clock()+1000)
 // The asymmetric conclusion cannot supply the renamed source row.
 expect(!mirrored||!check(g,mirrored,q)).toBe(true)
 expect(check(g,source,p)).toBe(true)
})
test('packed cells and conditional term columns can be mirrored into a full checked subtree',()=>{
 const a=x('left'),b=x('right'),i=x('actor'),c=x('column'),key=(r:typeof a)=>plus(times(8,r),c)
 const cell=(r:typeof a)=>ite(same(r,i),get('Rows',key(i)),get('Rows',key(r)))
 const invariant=all(same(get('Rows',key(a)),get('Rows',key(i))),same(get('Rows',key(b)),get('Rows',key(i))))
 const g={name:'conditional copies',hyps:[invariant,not(same(cell(a),cell(b)))]}
 const p=path([{left:1,actor:-1},{actor:1,left:-1},{right:1,actor:-1,'1':1}]),q=path([{right:1,actor:-1},{actor:1,right:-1},{left:1,actor:-1,'1':1}])
 const source=proof(g,p),mirrored=renameProof(g,source,p,q,swap,clock()+1000)
 expect(mirrored).toBeDefined();if(mirrored)expect(check(g,mirrored,q)).toBe(true)
})
test('monomial columns retain their polynomial meaning under row renaming',()=>{
 const a=x('left'),b=x('right'),squared=(v:typeof a)=>({op:'prod' as const,a:v,b:v}),g={name:'squares',hyps:[less(squared(a),n(0)),less(squared(b),n(0))]},p=new Map()
 const source=proof(g,p),mirrored=renameProof(g,source,p,p,swap,clock()+1000)
 expect(mirrored).toBeDefined();if(mirrored)expect(check(g,mirrored)).toBe(true)
})

test('renaming refuses expired work and cannot validate fabricated leaves',()=>{
 const g={name:'possible',hyps:[all(atMost(n(0),x('left')),atMost(n(0),x('right')))]},p=new Map()
 expect(renameProof(g,{leaf:[]},p,p,swap,clock()-1)).toBeUndefined()
 const bad=renameProof(g,{leaf:[]},p,p,swap,clock()+1000)
 expect(!bad||!check(g,bad)).toBe(true)
})
