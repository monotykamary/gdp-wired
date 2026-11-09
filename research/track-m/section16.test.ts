import {expect,test} from 'bun:test'
import {statement} from './section16-statements.ts'
const v=(name:string)=>({op:'var',name}),n=(value:number)=>({op:'const',value})
test('normalization retains guards and does not assert root validity',()=>{
 const q={op:'<=',a:{op:'if',c:{op:'and',xs:[{op:'<',a:v('j$'),b:v('size')},{op:'=',a:v('?canVote'),b:n(1)}]},then:{op:'get',map:'CfgT',key:v('j$')},else:n(0)},b:{op:'get',map:'CT',key:v('i')}}
 const a=statement({bound:q})!,b=statement({bound:{...q,a:{...q.a,c:{...q.a.c,xs:[...q.a.c.xs].reverse()}}}})!
 expect(a).toEqual(b);expect(a.mentions).toEqual({op:false,guard:true,postState:false});expect(a.text).toContain('?canVote')
})
test('frame normalization keeps post-state and action references',()=>{
 const a=statement({inst:{unit:0,terms:[[1,'r0'],[-1,'r1']]},reads:[['r0','size#',v('op')],['r1','size',v('i')]]})!
 expect(a.mentions).toEqual({op:true,guard:false,postState:true});expect(a.text).toContain('size#[op]')
})
test('an indexed success without a matching statement stays unresolved',()=>{expect(statement({stage:'frame-lemma',index:26,proved:true,ms:149})).toBeNull()})
