import {expect,test} from 'bun:test'
import {type C,type Machine,all,any,atMost,get,ite,less,n,not,plus,same,times,x} from '../../core/machine.ts'
import {check,checkMC,mcGoal,type CountCert} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {fieldBoundLemmas,fieldBounds} from './field-bound-lemmas.ts'

test('strict successor member bounds suggest checked field ceilings without protocol names',()=>{
 const m:Machine={name:'ceilings',params:[],inputs:['source'],inputMaps:['Selected'],state:{},maps:{Clock:0,Epoch:0},step:{flags:{eligible:{op:'all',key:'v',c:less(get('Clock',x('v')),plus(get('Clock',x('source')),n(1)))}}}}
 const ds=[{map:'Below',j:'row',key:'k',below:n(4),body:ite(less(get('Clock',x('k')),get('Epoch',x('row'))),n(1),n(0))}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['number','Below',x('target')]],insts:[]}
 const good=atMost(ite(all(same(x('?eligible'),n(1)),less(x('target'),n(4))),get('Epoch',x('target')),n(0)),get('Clock',x('source')))
 expect(fieldBounds(m,ds,cert)).toEqual([good])
 expect(fieldBoundLemmas(m,ds,{name:'empty',hyps:[]},cert,clock()+1000,[])).toBeUndefined()
 const goal={name:'ceiling',hyps:[same(x('?eligible'),n(1)),less(x('target'),n(4)),good,less(get('Clock',x('source')),get('Epoch',x('target')))]},tree=fieldBoundLemmas(m,ds,goal,cert,clock()+1000,[])
 expect(tree).toBeDefined();if(tree)expect(check(goal,tree)).toBe(true)
})

test('ceiling slices keep carried membership encoded as 1 <= the set cell',()=>{
 const member=(key:ReturnType<typeof x>)=>atMost(n(1),get('Selected',key)),ind=(c:C)=>ite(c,n(1),n(0)),bound=less(get('Clock',x('v')),plus(get('Clock',x('source')),n(1)))
 const m:Machine={name:'majority ceiling',params:[],inputs:['source'],inputMaps:['Selected'],state:{},maps:{Clock:0,Epoch:0,A:0},step:{flags:{eligible:{op:'all',key:'v',c:any(not(member(x('v'))),bound)}}}}
 const ds=[{map:'Votes',j:'row',key:'k',below:n(3),body:ind(member(x('k')))},{map:'Size',j:'row',key:'k',below:n(3),body:ind(same(get('A',x('k')),n(1)))},{map:'InputSize',j:'row',key:'k',below:n(3),body:ind(same(get('A',x('k')),n(1)))},{map:'Bad',j:'row',key:'k',below:n(3),body:ind(all(same(get('A',x('k')),n(1)),less(get('Clock',x('k')),get('Epoch',x('row')))))}]
 const cert:Pick<CountCert,'reads'|'insts'>={reads:[['votes','Votes',n(0)],['size','Size',n(0)],['inputsize','InputSize',n(0)],['bad','Bad',x('target')]],insts:[{wit:'probe',below:n(3),unit:0,terms:[[1,'votes'],[-1,'bad']]},{wit:'shadow',below:n(3),unit:0,terms:[[1,'size'],[-1,'inputsize']]}]}
 const hyps=[less(get('InputSize',n(0)),times(2,get('Votes',n(0)))),atMost(times(2,get('Bad',x('target'))),get('Size',n(0))),less(get('Clock',x('source')),get('Epoch',x('target'))),any(not(less(x('probe'),n(3))),not(member(x('probe'))),all(less(get('Clock',x('probe')),plus(get('Clock',x('source')),n(1))),same(get('A',x('probe')),n(1))))]
 const goal=mcGoal(hyps,ds,cert)!,tree=fieldBoundLemmas(m,ds,goal,cert,clock()+2000,[])
 expect(tree).toBeDefined();if(tree)expect(checkMC(hyps,ds,{...cert,tree})).toBe(true)
})
