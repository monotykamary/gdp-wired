import {expect,test} from 'bun:test'
import {atMost,n,x} from '../machine.ts'
import {type Goal,type Path,canon,check} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {sourceProofMemo} from './source-memo.ts'
const contradiction:Goal={name:'false',hyps:[atMost(n(1),n(0))]}
const proof=(g:Goal,p:Path)=>{const out=grow(g,p,{nodes:0,until:clock()+1000});if(!('tree'in out))throw new Error('fixture must refute');return out.tree}
test('source memo reuses only a transported tree at the same logical path',()=>{
 const memo=sourceProofMemo(),a={a:1},b={b:1},p:Path=new Map([[canon(a),{lin:a,holds:true}],[canon(b),{lin:b,holds:false}]]),tree=proof(contradiction,p)
 memo.put(contradiction,p,tree)
 const reordered=new Map([...p].reverse()),copy={...contradiction,hyps:[...contradiction.hyps]},got=memo.get(copy,reordered,clock()+1000)
 expect(got).toBeDefined();if(got)expect(check(copy,got,reordered)).toBe(true)
 expect(memo.get(copy,new Map(),clock()+1000)).toBeUndefined()
 expect(memo.get(copy,reordered,clock()-1)).toBeUndefined()
})
test('source memo reuses unchanged used rows across activation paths, not missing assumptions',()=>{
 const memo=sourceProofMemo(),goal:Goal={name:'bound',hyps:[atMost(x('amount'),n(0))]},amount={amount:-1,'1':1},phase={phase:1,'1':-1}
 const p:Path=new Map([[canon(amount),{lin:amount,holds:true}],[canon(phase),{lin:phase,holds:true}]]),q:Path=new Map([[canon(amount),{lin:amount,holds:true}],[canon(phase),{lin:phase,holds:false}]])
 const tree=proof(goal,p);memo.put(goal,p,tree)
 const got=memo.get(goal,q,clock()+1000);expect(got).toBeDefined();if(got)expect(check(goal,got,q)).toBe(true)
 const missing:Path=new Map([[canon(phase),{lin:phase,holds:false}]])
 expect(memo.get(goal,missing,clock()+1000)).toBeUndefined()
})

test('source memo tries an exact match beyond two geometrically nearer paths',()=>{
 const memo=sourceProofMemo(),goal:Goal={name:'nearby',hyps:[atMost(x('amount'),n(0))]},bound=(k:number)=>{const lin={amount:-1,'1':k};return [canon(lin),{lin,holds:true}] as const}
 const destination:Path=new Map([bound(1)]),useful:Path=new Map([bound(1)])
 for(const name of ['unrelatedA','unrelatedB','unrelatedC']){const lin={[name]:1};useful.set(canon(lin),{lin,holds:true})}
 memo.put(goal,useful,proof(goal,useful))
 for(const k of [2,3]){const nearer:Path=new Map([bound(k)]);memo.put(goal,nearer,proof(goal,nearer))}
 const got=memo.get(goal,destination,clock()+1000)
 expect(got).toBeDefined();if(got)expect(check(goal,got,destination)).toBe(true)
})

test('source memo cannot turn a changed satisfiable goal into a checked proof',()=>{
 const memo=sourceProofMemo(),p:Path=new Map(),tree=proof(contradiction,p)
 memo.put(contradiction,p,tree)
 const possible:Goal={name:'possible',hyps:[atMost(n(0),x('amount'))]},got=memo.get(possible,p,clock()+1000)
 expect(!got||!check(possible,got,p)).toBe(true)
})
