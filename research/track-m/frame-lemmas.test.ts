import {expect,test} from 'bun:test'
import {any,atMost,get,ite,less,n,same,x} from '../../core/machine.ts'
import {checkMC,mcGoal,type CountCert} from '../../kernel/kernel.ts'
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

test('an unsuccessful shared-frame probe can stop before spending the leaf allowance',()=>{
 const cert:Pick<CountCert,'reads'|'insts'>={reads:[['a','A',n(0)],['afterA','A#',n(0)],['b','B',n(0)],['afterB','B#',n(0)]],insts:[{wit:'one',below:n(4),unit:0,terms:[[1,'afterA'],[-1,'a']]},{wit:'two',below:n(4),unit:0,terms:[[1,'afterB'],[-1,'b']]}]}
 const g={name:'possible',hyps:[any(atMost(x('afterA'),x('a')),less(n(0),n(1))),any(atMost(x('afterB'),x('b')),less(n(0),n(1)))]},trace:object[]=[]
 expect(frameLemmas(g,cert,clock()+1000,trace,new Map(),{stopAfterFailed:1})).toBeUndefined()
 expect(trace.filter(e=>(e as any).stage==='frame-lemma')).toHaveLength(1)
})
