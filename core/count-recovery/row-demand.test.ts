import {expect,test} from 'bun:test'
import {type Machine,get,ite,n,same,x} from '../machine.ts'
import {canon,check,type Path,truth} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {demandedRowPair,proveRowCases,writesReadState} from './row-cases.ts'
const pairs=[[x('a'),x('i')],[x('b'),x('i')]] as const
const impossible={name:'contradiction',hyps:[same(n(0),n(1))]}
const close=(path:Path,end:number)=>{const out=grow(impossible,path,{nodes:0,until:end});return 'tree'in out?out.tree:undefined}
test('model-directed row search proves the unsplit root once',()=>{
 let calls=0
 const tree=proveRowCases(impossible,new Map(),[...pairs],clock()+1000,(p,e)=>{calls++;return close(p,e)},undefined,{model:()=>({a:0,b:1,i:0})})
 expect(tree).toBeDefined();expect(calls).toBe(1);expect(check(impossible,tree!)).toBe(true)
})
test('a model selects its equal row before other unresolved rows and skips unknown cells',()=>{
 expect(demandedRowPair([...pairs],new Map(),{a:2,b:1,i:1})).toBe(pairs[1])
 expect(demandedRowPair([...pairs],new Map(),{b:1,i:1})).toBe(pairs[1])
 expect(demandedRowPair([...pairs],new Map(),{a:NaN,i:0})).toBeUndefined()
})
test('both orderings of a demanded disequality are covered and checked',()=>{
 let calls=0;const events:any[]=[]
 const tree=proveRowCases(impossible,new Map(),[...pairs],clock()+1500,(p,e)=>{calls++;return truth(same(x('b'),x('i')),p)===undefined?undefined:close(p,e)},e=>events.push(e),{model:()=>({a:2,b:1,i:1})})
 expect(tree).toBeDefined();expect(check(impossible,tree!)).toBe(true)
 expect(events.filter(e=>e.stage==='row-demand')).toHaveLength(1)
 expect(events.find(e=>e.stage==='row-demand').pair).toEqual(pairs[1]);expect(calls).toBe(3)
})
test('no model means no speculative row enumeration; invalid leaves are never accepted',()=>{
 let calls=0
 expect(proveRowCases(impossible,new Map(),[...pairs],clock()+1000,()=>{calls++;return undefined},undefined,{model:()=>undefined})).toBeUndefined()
 expect(calls).toBe(1)
 expect(proveRowCases({name:'possible',hyps:[]},new Map(),[...pairs],clock()+1000,()=>({leaf:[]}),undefined,{model:()=>({a:0,b:0,i:0})})).toBeUndefined()
})
test('write-free detection follows count bodies, bounds, scalar writes, and inactive map branches',()=>{
 const m:Machine={name:'frames',params:[],inputs:['op','i'],state:{limit:n(2)},maps:{V:0,Other:0},counts:{N:{j:'r',key:'k',below:x('limit'),body:get('V',x('k'))}},step:{maps:{V:{each:'k',value:ite(same(x('op'),n(1)),n(1),get('V',x('k')))},Other:{each:'k',value:n(1)}}}}
 const cert={reads:[['post','N#',x('a')]] as [string,string,ReturnType<typeof x>][]}
 const a={op:1},b={op:-1},root:Path=new Map([[canon(a),{lin:a,holds:true}],[canon(b),{lin:b,holds:true}]])
 expect(writesReadState(m,cert,root)).toBe(false)
 expect(writesReadState(m,cert,new Map())).toBe(true)
 const frame={...m,step:{maps:{V:{each:'k',value:get('V',x('k'))},Other:{each:'k',value:n(1)}}}}
 expect(writesReadState(frame,cert,new Map())).toBe(false)
 expect(writesReadState({...frame,step:{...frame.step,state:{limit:n(3)}}},cert,new Map())).toBe(true)
 expect(writesReadState(m,{reads:[['x','missing#',x('a')]]},new Map())).toBe(true)
})
