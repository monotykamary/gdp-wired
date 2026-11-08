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
test('source memo cannot turn a changed satisfiable goal into a checked proof',()=>{
 const memo=sourceProofMemo(),p:Path=new Map(),tree=proof(contradiction,p)
 memo.put(contradiction,p,tree)
 const possible:Goal={name:'possible',hyps:[atMost(n(0),x('amount'))]},got=memo.get(possible,p,clock()+1000)
 expect(!got||!check(possible,got,p)).toBe(true)
})
