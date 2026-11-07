import {expect,test} from 'bun:test'
import {ite,n,same,x} from '../../core/machine.ts'
import {canon,check,type Path} from '../../kernel/kernel.ts'
import {clock,grow,widen} from '../../kernel/prove.ts'
import {piecesAt,walkLive} from './live-dependencies.ts'
test('dependency slices ignore inactive witnesses without rewriting source terms',()=>{
 const term=ite(same(x('op'),n(0)),x('foreignWitness'),x('liveWitness')),before=JSON.stringify(term),lin={op:-1,'1':1},path:Path=new Map([[canon(lin),{lin,holds:true}]])
 const names=(path:Path)=>{const out=new Set<string>();walkLive(term,path,o=>{if(o.op==='var')out.add(o.name)});return [...out].sort()}
 expect(names(path)).toEqual(['liveWitness'])
 expect(names(new Map())).toEqual(['foreignWitness','liveWitness','op'])
 expect(JSON.stringify(term)).toBe(before)
})
test('active implications expose independently sliceable conjuncts at the original path',()=>{
 const guard=same(x('op'),n(4)),field=same(x('flag'),n(1)),count=same(x('cardinality'),n(2)),premise={op:'or' as const,xs:[{op:'not' as const,x:guard},{op:'and' as const,xs:[field,count]}]}
 const upper={op:1,'1':-4},lower={op:-1,'1':4},path:Path=new Map([[canon(upper),{lin:upper,holds:true}],[canon(lower),{lin:lower,holds:true}]])
 expect(piecesAt(premise,path)).toEqual([field,count])
 expect(piecesAt(premise,new Map())).toEqual([premise])
 const whole={name:'original implication',hyps:[premise,same(x('flag'),n(0))]},part={...whole,hyps:whole.hyps.flatMap(c=>piecesAt(c,path))}
 const out=grow(part,path,{nodes:0,until:clock()+1000})
 expect('tree'in out).toBe(true)
 if('tree'in out){const proof=widen(part,whole,out.tree,{},path,path);expect(proof).toBeDefined();if(proof)expect(check(whole,proof,path)).toBe(true)}
})
