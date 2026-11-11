import {describe,expect,it} from 'bun:test'
import {all,any,atMost,less,minus,n,not,plus,times,x} from './machine.ts'
import {type Goal,check} from '../kernel/kernel.ts'
import {clock,counted,fullRate,withWall} from '../kernel/prove.ts'
import {proveQuorumCountLeaf} from './count-quorum-leaf.ts'
const q=x('q'),v=x('v'),dq=x('dq'),dv=x('dv'),overlap=x('overlap'),hq=x('hq'),hv=x('hv')
const rq=plus(dq,overlap),rv=plus(dv,overlap)
const guard=all(atMost(times(2,hq),rq),less(rq,plus(times(2,hq),n(2))),atMost(times(2,hv),rv),less(rv,plus(times(2,hv),n(2))))
const pair=any(not(guard),less(overlap,plus(minus(plus(hq,n(1)),dq),minus(plus(hv,n(1)),dv))),atMost(times(2,q),rq),atMost(times(2,v),rv))
const facts=[atMost(plus(q,v),plus(plus(dq,dv),overlap)),atMost(v,rv),atMost(q,rq)]
function attempt(omit=-1){
 const goal:Goal={name:'three-fact quorum',hyps:[guard,pair,less(rq,times(2,q)),less(rv,times(2,v)),...facts.filter((_,index)=>index!==omit)]}
 return withWall(performance.now()+10000,()=>counted(fullRate,()=>{const tree=proveQuorumCountLeaf(goal,goal,new Map(),pair,{first:'q',second:'v'},[hq,hv],clock()+500);return {goal,tree}},true))
}
describe('explicit quorum arithmetic',()=>{
 it('checks with the three membership facts and four deterministic splits',()=>{const {goal,tree}=attempt();expect(tree).toBeDefined();expect(tree&&check(goal,tree,new Map())).toBe(true)})
 for(let omitted=0;omitted<3;omitted++)it(`does not invent omitted membership fact ${omitted}`,()=>{expect(attempt(omitted).tree).toBeUndefined()})
})
