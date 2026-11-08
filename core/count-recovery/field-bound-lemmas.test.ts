import {expect,test} from 'bun:test'
import {type C,type Machine,all,any,atMost,get,ite,less,minus,n,not,plus,same,times,x} from '../machine.ts'
import {canon,check,checkMC,linear,mcGoal,type CountCert,type Path} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {countBindingsAt,emptyCountCandidate,fieldBoundLemmas,fieldBounds} from './field-bound-lemmas.ts'

test('empty-count candidates are post-state singleton upper bounds on field comparisons',()=>{
 const body=ite(less(get('Clock',x('k')),get('Epoch',x('row'))),n(1),n(0)),m:Machine={name:'empty proposals',params:[],inputs:[],state:{},counts:{Below:{j:'row',key:'k',below:n(4),body},Constant:{j:'row',key:'k',below:n(4),body:n(1)}},step:{}}
 const cert:Pick<CountCert,'reads'|'insts'>={reads:[['pre','Below',x('target')],['post','Below#',x('target')],['other','Constant#',x('target')]],insts:[]},base={wit:'sample',below:n(4),unit:0 as const,terms:[[1,'post']] as [number,string][]}
 expect(emptyCountCandidate(m,cert,base)).toBe(true)
 for(const id of ['pre','other'])expect(emptyCountCandidate(m,cert,{...base,terms:[[1,id]]})).toBe(false)
 expect(emptyCountCandidate(m,cert,{...base,terms:[[-1,'post']]})).toBe(false)
 expect(emptyCountCandidate(m,cert,{...base,unit:1})).toBe(false)
})
for(const zero of [true,false])test(`a singleton empty count ${zero?'checks at a zero threshold':'is not assumed empty'}`,()=>{
  const body=ite(less(get('Clock',x('k')),get('Epoch',x('row'))),n(1),n(0)),m:Machine={name:'empty count',params:[],inputs:['source'],state:{},maps:{Clock:0,Epoch:0},inputMaps:['Selected'],counts:{Below:{j:'row',key:'k',below:n(4),body}},step:{flags:{eligible:{op:'all',key:'v',c:less(get('Clock',x('v')),plus(get('Clock',x('source')),n(1)))}}}}
  const ds=[{map:'Below',...m.counts!.Below!},{map:'Below#',...m.counts!.Below!}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['pre','Below',x('target')],['post','Below#',x('target')]],insts:[{wit:'sample',below:n(4),unit:0,terms:[[1,'post']]}]}
  const hyps=[less(x('target'),n(4)),less(n(0),get('Below#',x('target'))),...(zero?[same(get('Epoch',x('target')),n(0))]:[])],goal=mcGoal(hyps,ds,cert)!,tree=fieldBoundLemmas(m,ds,goal,cert,clock()+1500,[])
  if(zero){expect(tree).toBeDefined();if(tree)expect(checkMC(hyps,ds,{...cert,tree})).toBe(true)}else expect(tree).toBeUndefined()
})
test('numeric count bridges include nested path cells but omit unrelated reads',()=>{
 const a=get('Left',n(0)),b=get('Right',n(0)),lin=linear(minus(a,b),new Map())!,root:Path=new Map([[canon(lin),{lin,holds:true}]])
 const reads:CountCert['reads']=[['a','Left',n(0)],['b','Right',n(0)],['unused','Right',n(1)],['other','Other',n(0)]]
 expect(countBindingsAt(reads,root)).toEqual([same(x('a'),a),same(x('b'),b)])
 expect(countBindingsAt(reads,new Map())).toEqual([])
})

test('strict successor member bounds suggest checked field ceilings without protocol names',()=>{
 const m:Machine={name:'ceilings',params:[],inputs:['source'],inputMaps:['Selected'],state:{},maps:{Clock:0,Epoch:0},step:{flags:{eligible:{op:'all',key:'v',c:less(get('Clock',x('v')),plus(get('Clock',x('source')),n(1)))}}}}
 const ds=[{map:'Below',j:'row',key:'k',below:n(4),body:ite(less(get('Clock',x('k')),get('Epoch',x('row'))),n(1),n(0))}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['number','Below',x('target')]],insts:[]}
 const good=atMost(ite(all(same(x('?eligible'),n(1)),less(x('target'),n(4))),get('Epoch',x('target')),n(0)),get('Clock',x('source')))
 expect(fieldBounds(m,ds,cert)).toEqual([good])
 expect(fieldBoundLemmas(m,ds,{name:'empty',hyps:[]},cert,clock()+1000,[])).toBeUndefined()
 const goal={name:'ceiling',hyps:[same(x('?eligible'),n(1)),less(x('target'),n(4)),good,less(get('Clock',x('source')),get('Epoch',x('target')))]},events:any[]=[],tree=fieldBoundLemmas(m,ds,goal,cert,clock()+1000,events)
 expect(events.some(e=>e.stage==='field-domain'&&e.checked&&e.direct)).toBe(true)
 expect(tree).toBeDefined();if(tree)expect(check(goal,tree)).toBe(true)
})

test('ceilings retain input-key fields used by a write beside the post-count target',()=>{
 const m:Machine={name:'writer ceiling',params:[],inputs:['source'],inputMaps:['Selected'],state:{},maps:{Clock:0,Epoch:0},step:{flags:{eligible:{op:'all',key:'v',c:less(get('Clock',x('v')),plus(get('Clock',x('source')),n(1)))}},maps:{Epoch:{key:x('source'),value:plus(get('Epoch',x('source')),n(1))}}}}
 const d={j:'row',key:'k',below:n(4),body:ite(less(get('Clock',x('k')),get('Epoch',x('row'))),n(1),n(0))},ds=[{...d,map:'Below'},{...d,map:'Below#'}]
 const cert={reads:[['target','Below',x('target')],['actor','Below',x('source')],['next','Below#',x('target')]] as CountCert['reads'],insts:[]}
 const good=(row:ReturnType<typeof x>)=>atMost(ite(all(same(x('?eligible'),n(1)),less(row,n(4))),get('Epoch',row),n(0)),get('Clock',x('source')))
 expect(fieldBounds(m,ds,cert)).toEqual([good(x('target')),good(x('source'))])
})

test('equal per-member fields also suggest checked ceiling candidates',()=>{
 const m:Machine={name:'equal ceilings',params:[],inputs:['source'],inputMaps:['Selected'],state:{},maps:{Clock:0,Epoch:0},step:{flags:{committed:{op:'all',key:'v',c:same(get('Clock',x('v')),get('Clock',x('source')))}}}}
 const ds=[{map:'Below',j:'row',key:'k',below:n(4),body:ite(less(get('Clock',x('k')),get('Epoch',x('row'))),n(1),n(0))}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['number','Below',x('target')]],insts:[]}
 expect(fieldBounds(m,ds,cert)).toEqual([atMost(ite(all(same(x('?committed'),n(1)),less(x('target'),n(4))),get('Epoch',x('target')),n(0)),get('Clock',x('source')))])
 expect(fieldBoundLemmas(m,ds,{name:'no premises',hyps:[]},cert,clock()+1000,[])).toBeUndefined()
})

test('equal row keys produce checked count-read alias cuts',()=>{
 const m:Machine={name:'aliases',params:[],inputs:['a','i'],state:{},step:{}},ds=[{map:'Size',j:'row',key:'k',below:n(4),body:n(1)}]
 const cert:Pick<CountCert,'reads'|'insts'>={reads:[['left','Size',x('a')],['right','Size',x('i')]],insts:[]},g=mcGoal([less(get('Size',x('a')),get('Size',x('i')))],ds,cert)!
 const root:Path=new Map();for(const lin of [{a:1,i:-1},{a:-1,i:1}])root.set(canon(lin),{lin,holds:true})
 const events:object[]=[],tree=fieldBoundLemmas(m,ds,g,cert,clock()+1000,events,undefined,root)
 expect(events.some(e=>(e as any).stage==='read-alias'&&(e as any).checked)).toBe(true)
 expect(tree).toBeDefined();if(tree)expect(check(g,tree,root)).toBe(true)
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
