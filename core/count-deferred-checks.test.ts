import {expect,test} from 'bun:test'
import {type CountCert,type FrameCut,type Goal,type Tree,check,framePath} from '../kernel/kernel.ts'
import {rowsAt} from '../kernel/prove.ts'
import {solve} from './solver.ts'
import {type Law,type Machine,atMost,n,same,x} from './machine.ts'
import {deferIntermediateCountChecks,finishCountStrategy} from './count-strategy.ts'
import {minimalViewFirst} from './count-minimal-view.ts'
import {stabilizeGuardedTree} from './count-stabilize-tree.ts'
test('deferred intermediate checking requires both composition-only options',()=>{
 for(const compose of [false,true])for(const defer of [false,true])expect(deferIntermediateCountChecks({deferToComposition:compose,deferIntermediateChecks:defer})).toBe(compose&&defer)
})
test('an unchecked minimal proposal still fails the unchanged checker',()=>{
 const full:Goal={name:'satisfiable',hyps:[atMost(n(0),x('a'))]},minimal:Goal={name:'empty',hyps:[]},path=new Map(),fake=()=>({tree:{leaf:[]},nodes:0})
 expect(minimalViewFirst(full,minimal,path,Infinity,fake).tree).toBeUndefined()
 const proposed=minimalViewFirst(full,minimal,path,Infinity,fake,path,{deferCheck:true})
 expect(proposed.tree).toBeDefined()
 expect(proposed.tree&&check(full,proposed.tree,path)).toBe(false)
})
test('deferred stabilization reindexes but does not certify an invalid leaf',()=>{
 const goal:Goal={name:'satisfiable',hyps:[]},tree={leaf:[]},roots=new Map([[tree,new Map()]])
 expect(stabilizeGuardedTree(goal,tree,[],[],roots,Infinity).tree).toBeUndefined()
 const proposed=stabilizeGuardedTree(goal,tree,[],[],roots,Infinity,{deferCheck:true})
 expect(proposed.tree).toBeDefined()
 expect(proposed.tree&&check(goal,proposed.tree)).toBe(false)
})
test('deferred stabilization still repairs changed row layouts',()=>{
 const goal:Goal={name:'shifted rows',hyps:[atMost(x('a'),n(0)),atMost(n(1),x('b'))]},frame:FrameCut={post:'a',pre:'b',when:[]},before=framePath([frame],[],new Map()),result=solve(rowsAt(goal,before),1000)
 expect(result.kind).toBe('refuted');if(result.kind!=='refuted')return
 const tree:Tree={leaf:result.steps},frames=[frame,frame],after=framePath(frames,[],new Map())
 expect(check(goal,tree,after)).toBe(false)
 const proposed=stabilizeGuardedTree(goal,tree,frames,[],new Map([[tree,before]]),Infinity,{deferCheck:true})
 expect(proposed.failed).toBe(false)
 expect(proposed.tree&&check(goal,proposed.tree,after)).toBe(true)
})
test('standalone finishing does not honor the intermediate-only option',()=>{
 const m:Machine={name:'constant fixture',params:[],inputs:[],state:{},maps:{},step:{}},law:Law={name:'constant',holds:same(n(0),n(0))},cert:CountCert={reads:[],insts:[],tree:{leaf:[]}}
 expect(finishCountStrategy(m,[law],law,{},'none',cert,Infinity,()=>cert,undefined,{deferIntermediateChecks:true})).toBeUndefined()
 const proposed=finishCountStrategy(m,[law],law,{},'none',cert,Infinity,()=>cert,undefined,{deferToComposition:true,deferIntermediateChecks:true})
 expect(proposed?.status).toBe('unchecked')
})
