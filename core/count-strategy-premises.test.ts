import {expect,test} from 'bun:test'
import {type Law,n,same,x} from './machine.ts'
import {type CountStrategyProof} from './count-strategy.ts'
import {recordCountStrategyPremises} from './count-strategy-premises.ts'
import {assumed} from '../kernel/kernel.ts'
const law=(name:string,keys:string[]=[]):Law=>({name,forall:'a',keys,holds:same(x('a'),x('a'))})
test('premises record instantiated family laws, not the offered roster or flags',()=>{
 const a=law('first'),b=law('second',['b']),unused=law('unused')
 const proof:CountStrategyProof={instances:{first:[n(0),n(1)],second:[n(0),n(1)],unused:[],'?guard':[n(2)]},certs:{}}
 expect(recordCountStrategyPremises([unused,b,a],proof).premises).toEqual([b.name,a.name])
 expect(proof.premises).toBeUndefined()
})
test('recording recomputes metadata without changing certificates or tuples',()=>{
 const a=law('actual'),offered=law('offered'),proof:CountStrategyProof={instances:{actual:[n(0)]},certs:{},premises:[offered.name]}
 const recorded=recordCountStrategyPremises([a,offered],proof)
 expect(recorded.premises).toEqual([a.name]);expect(Object.isFrozen(recorded.premises)).toBe(true)
 expect(recorded.instances).toBe(proof.instances);expect(recorded.certs).toBe(proof.certs);expect(proof.premises).toEqual([offered.name])
})
test('scalar instances are distinct from empty quantified tuple lists',()=>{
 const scalar:Law={name:'scalar',holds:same(n(0),n(0))},quantified=law('quantified')
 expect(recordCountStrategyPremises([scalar,quantified],{instances:{scalar:[],quantified:[]},certs:{}}).premises).toEqual([scalar.name])
})
test('implicit scalar assumptions are recorded without a tuple entry',()=>{
 const scalar:Law={name:'implicit scalar',holds:same(x('phase'),n(0))},quantified=law('uninstantiated')
 expect(assumed([scalar,quantified],{})).toEqual([scalar.holds])
 expect(recordCountStrategyPremises([scalar,quantified],{instances:{},certs:{}}).premises).toEqual([scalar.name])
 expect(()=>recordCountStrategyPremises([scalar],{instances:{[scalar.name]:[n(0)]},certs:{}})).toThrow('malformed')
})
test('ambiguous names and incomplete tuples cannot produce a premise audit',()=>{
 const a=law('pair',['b'])
 expect(()=>recordCountStrategyPremises([a,{...a}],{instances:{},certs:{}})).toThrow('ambiguous')
 expect(()=>recordCountStrategyPremises([a],{instances:{pair:[n(0)]},certs:{}})).toThrow('malformed')
})
