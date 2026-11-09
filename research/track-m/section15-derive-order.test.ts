import {expect,test} from 'bun:test'
import {deriveClassOrder,sameCountBody,type DeriveClass} from './section15-derive-order.ts'
import {type Count,type Path,canon} from '../../kernel/kernel.ts'
const item=(index:number,part:Partial<DeriveClass>={}):DeriveClass=>({index,frame:false,monotone:false,member:false,alias:false,partition:false,zero:false,...part})
test('derive classes precede partitions, omit zero claims, and preserve class order',()=>{
 expect(deriveClassOrder([item(8,{zero:true,frame:true}),item(4,{partition:true}),item(3,{alias:true}),item(2,{member:true}),item(1,{monotone:true}),item(0,{frame:true}),item(9)])).toEqual([0,1,2,3,4])
})
test('a class pass is at most 24 distinct attempts, never an unbounded new pool',()=>{
 const rows=Array.from({length:50},(_,i)=>item(i%30,{frame:true}))
 const out=deriveClassOrder(rows);expect(out.length).toBe(24);expect(new Set(out).size).toBe(24);expect(out).toEqual(Array.from({length:24},(_,i)=>i))
})
test('frame classification resolves only path-decided value branches',()=>{
 const a:Count={v:'pre',key:'j',below:{op:'const',value:3},body:{op:'get',map:'M',key:{op:'var',name:'j'}}}
 const b:Count={v:'post',key:'k',below:a.below,body:{op:'if',c:{op:'<=',a:{op:'var',name:'op'},b:{op:'const',value:0}},then:{op:'const',value:1},else:{op:'get',map:'M',key:{op:'var',name:'k'}}}}
 const p:Path=new Map([[canon({op:1}),{lin:{op:1},holds:false}]])
 expect(sameCountBody(a,b,p)).toBe(true);expect(sameCountBody(a,b,new Map())).toBe(false)
 expect(sameCountBody(a,{...a,below:{op:'const',value:4}},p)).toBe(false)
})
