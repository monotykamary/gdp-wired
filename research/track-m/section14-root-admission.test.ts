import {test,expect} from 'bun:test'
import {type Count,type CountInst,countHyp,checkCounted,check,linear,canon} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,grow} from '../../kernel/prove.ts'
import {sub} from '../../core/solver.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
const count=(v:string,c:any):Count=>({v,key:'k',below:{op:'var',name:'size'},body:{op:'if',c,then:{op:'const',value:1},else:{op:'const',value:0}}})
const atom={op:'=' as const,a:{op:'get' as const,map:'M',key:{op:'var' as const,name:'k'}},b:{op:'const' as const,value:1}}
test('a root count identity is checked independently before admission',()=>{
 const counts=[count('a',atom),count('b',{op:'or',xs:[atom,{op:'=',a:{op:'get',map:'N',key:{op:'var',name:'k'}},b:{op:'const',value:1}}]})],inst:CountInst={wit:'w',below:{op:'var',name:'size'},terms:[[1,'a'],[-1,'b']],unit:0},hyp=countHyp(counts,inst)!
 if(hyp.op!=='or'||hyp.xs[0]?.op!=='<=')throw new Error('shape');const good=hyp.xs[0],goal={name:'identity',hyps:[{op:'not' as const,x:good},hyp]}
 const q=counted(fullRate,()=>grow(goal,new Map(),{nodes:0,until:clock()+1000}),true);expect('tree'in q).toBe(true);if(!('tree'in q))return
 expect(checkCounted({name:'identity',hyps:[{op:'not',x:good}],counts},{insts:[inst],tree:q.tree})).toBe(true)
 const cut=sub(linear(good.a,new Map())!,linear(good.b,new Map())!),root={name:'root',hyps:[hyp]},lemma=admitConditionalCut(root,goal,q.tree,new Map(),new Map(),cut,[],performance.now()+10000)
 expect(lemma).toBeDefined();if(!lemma)return;expect(lemma.when).toHaveLength(0)
 const local={name:'root',hyps:lemma.slice!.map(i=>root.hyps[i]!)},path=new Map([[canon(cut),{lin:cut,holds:false}]])
 expect(check(local,lemma.tree,path)).toBe(true)
 expect(check(local,{leaf:[]},path)).toBe(false)
 const reversed=Object.fromEntries(Object.entries(cut).map(([k,v])=>[k,-v]));expect(check(local,lemma.tree,new Map([[canon(reversed),{lin:reversed,holds:false}]]))).toBe(false)
})
