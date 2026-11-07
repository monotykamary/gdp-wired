import {expect,test} from 'bun:test'
import {get,ite,less,n,same,x} from '../../core/machine.ts'
import {checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {frameLemmas} from './frame-lemmas.ts'

test('factored frame lemmas produce an ordinary checked count tree',()=>{
 const pre=ite(same(get('Members',x('cell')),n(1)),n(1),n(0)),base={j:'row',key:'cell',below:n(4)}
 const decls=[{...base,map:'A',body:pre},{...base,map:'A#',body:ite(same(x('op'),n(1)),n(1),pre)}]
 const cert={reads:[['before','A',n(0)],['after','A#',n(0)]] as [string,string,ReturnType<typeof n>][],insts:[{wit:'member',below:n(4),unit:0,terms:[[1,'after'],[-1,'before']] as [number,string][]}]}
 const hyps=[same(x('op'),n(0)),less(get('A',n(0)),get('A#',n(0)))],g=mcGoal(hyps,decls,cert)!
 const trace:object[]=[],tree=frameLemmas(g,cert,clock()+1000,trace)
 expect(tree).toBeDefined()
 if(tree)expect(checkMC(hyps,decls,{...cert,tree})).toBe(true)
 const changed=[same(x('op'),n(1)),less(get('A',n(0)),get('A#',n(0)))],bad=mcGoal(changed,decls,cert)!
 expect(frameLemmas(bad,cert,clock()+400,[])).toBeUndefined()
})
