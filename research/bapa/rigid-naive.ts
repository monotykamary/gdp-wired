// Original ivybench naive_consensus actions/relations. Intersection is ASSUMED,
// never counted; the three source helpers below are GIVEN, not found.
import {argsKey, type C, type E, type Law, type Machine} from '../../core/machine.ts'
import {ghostedMachine, ghostedOk, type Ghosted} from '../../kernel/kernel.ts'
import {type FunctionInstanceSpec} from '../../kernel/function-instances.ts'
import {lowerRigid} from './rigid-lower.ts'
import {rigidQuorumSignature} from './rigid-minimal.ts'
const v=(name:string):E=>({op:'var',name}), k=(value:number):E=>({op:'const',value})
const eq=(a:E,b:E):C=>({op:'=',a,b}), lt=(a:E,b:E):C=>({op:'<',a,b})
const and=(...xs:C[]):C=>({op:'and',xs}), or=(...xs:C[]):C=>({op:'or',xs}), not=(x:C):C=>({op:'not',x})
const implies=(a:C,b:C):C=>or(not(a),b), read=(map:string,key:E):E=>({op:'get',map,key})
const tuple=(a:E,b:E):E=>({op:'tup',a,b}), vote=(n:E,x:E)=>read('vote',tuple(n,x)), decide=(q:E,x:E)=>read('decide',tuple(q,x)), decision=(x:E)=>read('decision',x)
const member=(n:E,q:E)=>read('member',argsKey([n,q])), witness=(x:E)=>read('learnedQuorum',x)
const finite=(sort:string,key:string,size:string,c:C):C=>({op:'all',key,finite:sort,c:implies(lt(v(key),v(size)),c)})
const event=(n:number)=>eq(v('action'),k(n)), yes=(name:string):C=>({op:'flag',name})
const update=(condition:C,value:E,old:E):E=>({op:'if',c:condition,then:value,else:old})
export function rigidNaive() {
  const n=v('node'), q=v('quorum'), x=v('value')
  const cast=event(0), collect=event(1), learn=event(2)
  const base:Machine={name:'Ivy naive_consensus, original intersecting quorum sort (GIVEN helpers)',params:['nodes','quorums','values'],inputs:['action','node','quorum','value'],state:{},maps:{vote:0,decide:0,decision:0},step:{
    flags:{unvoted:finite('Value','w','values',eq(vote(n,v('w')),k(0))), collected:finite('Node','r','nodes',implies(eq(member(v('r'),q),k(1)),eq(vote(v('r'),x),k(1))))},
    maps:{vote:{key:tuple(n,x),value:update(cast,k(1),vote(n,x))},decide:{key:tuple(q,x),value:update(collect,k(1),decide(q,x))},decision:{key:x,value:update(learn,k(1),decision(x))}},
  },assume:and(lt(x,v('values')),or(and(cast,lt(n,v('nodes')),yes('unvoted')),and(collect,lt(q,v('quorums')),yes('collected')),and(learn,lt(q,v('quorums')),eq(decide(q,x),k(1))))) }
  const lowered=lowerRigid(base,rigidQuorumSignature)
  const ghosted:Ghosted={orig:lowered.abstractMachine,vars:{},maps:{learnedQuorum:{start:0,write:{key:x,value:update(learn,q,witness(x))}}}}
  if(!ghostedOk(ghosted)) throw Error('proof-only learnedQuorum is not fresh')
  const nn=v('n'), a=v('a'), b=v('b'), qq=v('q')
  const helpers:Law[]=[
    {name:'GIVEN unique vote per node',forall:'n',keys:['a','b'],holds:implies(and(lt(nn,v('nodes')),lt(a,v('values')),lt(b,v('values')),eq(vote(nn,a),k(1)),eq(vote(nn,b),k(1))),eq(a,b))},
    {name:'GIVEN decided quorum members voted',forall:'q',keys:['a','n'],holds:implies(and(lt(qq,v('quorums')),lt(a,v('values')),lt(nn,v('nodes')),eq(decide(qq,a),k(1)),eq(member(nn,qq),k(1))),eq(vote(nn,a),k(1)))},
    {name:'GIVEN learned value has deciding quorum (ghost witness)',forall:'a',holds:implies(and(lt(a,v('values')),eq(decision(a),k(1))),and(lt(witness(a),v('quorums')),eq(decide(witness(a),a),k(1))))},
  ]
  const safety:Law={name:'original agreement',forall:'a',keys:['b'],holds:implies(and(lt(a,v('values')),lt(b,v('values')),eq(decision(a),k(1)),eq(decision(b),k(1))),eq(a,b))}
  const strategy:FunctionInstanceSpec={...lowered.functionInstances,maps:{learnedQuorum:{result:'Quorum',args:['Value']}},variables:{node:'Node',quorum:'Quorum',value:'Value',n:'Node',q:'Quorum',a:'Value',b:'Value',r:'Node',w:'Value'},limits:{work:2_000_000,candidates:128,tuples:4096,depth:4}}
  return {lowered,ghosted,machine:ghostedMachine(ghosted),helpers,safety,laws:[...helpers,safety],strategy}
}
