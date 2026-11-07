import {test, expect} from 'bun:test'
import {certFor} from './counts.ts'
import {type C, type E, type Law, type Machine, x, get, not, same} from './machine.ts'
import {type CountDecl, type CountCert, type Goal, assumed, check, checkMC, mcGoal, substC, substE, countedObligations} from '../kernel/kernel.ts'
import {grow, clock, counted, fullRate, withWall, withDeadline} from '../kernel/prove.ts'
import {modelSequence} from '../kernel/model-sequence.ts'
import {linOfE, canon} from './solver.ts'
import {countPoolKey, rootFlagMatches, keyId, countedInstanceSources, completeReadMatches, projectBoundCoordinate, genuinelyKeyless, vacuousCountBinder, seedVacuousCounts, sparseReadInstances, matchAffineRemainder, stableState, stableSelected, bareRangeMap, targetKindMatches, seededBoundMaps, targetFlagMatches, ownPREMatches, remainingCoordinateProposals, grammarPool, reservationState, reservePool, ids, polaritySelection, prepareSupport, sourceBoundMaps, selectedCertificate, chosenView, candidateWork, instId, smallSelection, UnsupportedCountProposal, sourceContext} from './count-support.ts'

test('source contexts keep original definition support and unary guards without protocol names',()=>{
 for(const prefix of ['fir','renamed'])for(const radix of [7,19]){
  const n=(value:number):E=>({op:'const',value}),mp=(name:string)=>prefix+name,read=(name:string,key:E)=>get(mp(name),key),ge=(e:E):C=>({op:'<=',a:n(1),b:e}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:radix,a},b})
  const m:Machine={name:prefix,params:[],inputs:['a','b'],state:{mode:n(0)},maps:{[mp('main')]:0,[mp('needed')]:0,[mp('noise')]:0},counts:{[mp('score')]:{j:'arg',key:'w',below:n(radix),body:read('needed',pack(x('arg'),x('w')))},[mp('whole')]:{j:'unused',key:'w',below:n(radix),body:read('noise',x('w'))},[mp('irrelevant')]:{j:'arg',key:'w',below:n(radix),body:read('noise',pack(x('arg'),x('w')))}},step:{maps:{[mp('main')]:{key:pack(x('a'),x('b')),value:n(0)}}}}
  const target:Law={name:prefix+' target',forall:'p',holds:{op:'and',xs:[ge(read('score',x('p'))),ge(read('main',x('p')))]}},needed:Law={name:prefix+' needed',forall:'p',holds:ge(read('needed',x('p')))},relation:Law={name:prefix+' direct',forall:'p',keys:['q'],holds:{op:'and',xs:[ge(read('main',x('p'))),ge(read('needed',x('q')))]}},derived:Law={...relation,name:prefix+' derived'},guard:Law={name:prefix+' guard',forall:'p',holds:{op:'or',xs:[{op:'not',x:ge(read('needed',x('p')))},{op:'<=',a:n(0),b:x('mode')}]}},keyless:Law={name:prefix+' keyless source',forall:'p',holds:ge(read('whole',x('p')))},noise:Law={name:prefix+' unrelated',forall:'p',holds:ge(read('noise',x('p')))},stateNoise:Law={name:prefix+' state guess',forall:'p',holds:{op:'and',xs:[ge(read('needed',x('p'))),{op:'=',a:x('mode'),b:n(0)}]}},wide:Law={name:prefix+' wide',forall:'p',keys:['q','r'],holds:ge(read('needed',pack(x('p'),x('q'))))},otherCount:Law={name:prefix+' other count',forall:'p',holds:ge(read('irrelevant',x('p')))}
  const laws=[noise,target,derived,needed,stateNoise,relation,wide,guard,otherCount,keyless],before=JSON.stringify(laws),selected=sourceContext(m,laws,target,new Set([derived,guard]))
  expect(selected).toEqual([target,needed,relation,guard,keyless]);expect(sourceContext(m,laws,relation,new Set([derived,guard]))).toEqual([needed,relation,guard]);expect(selected.every(l=>laws.includes(l))).toBe(true);expect(JSON.stringify(laws)).toBe(before)
 }
})

test('v4 single complete root reads retain every guard across unrelated names and radices',()=>{
 for(const base of [17,83])for(const prefix of ['cedar_','other_']){
  const n=(value:number):E=>({op:'const',value}),v=(s:string)=>x(prefix+s),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:base,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b}),lt=(a:E,b:E):C=>({op:'<',a,b})
  const own:Law={name:prefix+'root',forall:prefix+'a',keys:[prefix+'b',prefix+'c',prefix+'d'],holds:{op:'and',xs:[le(n(1),get(prefix+'source',pack(v('a'),v('b')))),le(n(1),get(prefix+'source',pack(v('c'),v('d'))))]}}
  const law:Law={name:prefix+'guarded implication',forall:prefix+'u',keys:[prefix+'v'],holds:{op:'or',xs:[not({op:'and',xs:[lt(v('u'),n(base)),lt(v('v'),n(base)),same(v('enabled'),n(1))]}),not(le(n(1),get(prefix+'source',pack(v('u'),v('v'))))),le(n(1),get(prefix+'dest',pack(v('u'),v('v'))))]}}
  const m:Machine={name:prefix+'machine',params:[prefix+'enabled'],inputs:[],state:{},maps:{[prefix+'source']:0,[prefix+'dest']:0},step:{}}
  const result=sparseReadInstances(m,[law,own],own,{}, {name:'current',hyps:[]},{reads:[],insts:[]},2),wanted=[[v('a#'),v('b')],[v('c'),v('d')]]
  expect(result.completeMatches.map(p=>p.tuple)).toEqual(wanted);expect(result.summary.completeReadAdmissions).toBe(2)
  for(const p of result.completeMatches){expect(p.kind).toBe('complete-coherent-read');expect(p.coherentReadMatch).toBe(true);expect(p.source.kind).toBe('root');expect(p.premise).toEqual(assumed([law],{[law.name]:p.tuple})[0]!);expect(p.premise.op).toBe('or')}
  expect(result.at[law.name]).toEqual(wanted.flat());expect(result.added.every(a=>a.coherent)).toBe(true)
  // Only these complete root bindings may cross the early primitive filter.
  expect(prepareSupport(m,[law,own],own,{},1).at[law.name]).toEqual(wanted.flat())
 }
})

test('free transition reads close whole guarded laws and their exact primitive ranges',()=>{
 for(const base of [17,83])for(const prefix of ['beech_','renamed_']){
  const n=(value:number):E=>({op:'const',value}),v=(name:string)=>x(prefix+name),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:base,a},b}),triple=(a:E,b:E,c:E)=>pack(pack(a,b),c),le=(a:E,b:E):C=>({op:'<=',a,b}),lt=(a:E,b:E):C=>({op:'<',a,b})
  const source:Law={name:prefix+'guarded source',forall:prefix+'i',keys:[prefix+'j',prefix+'k'],holds:{op:'or',xs:[not({op:'and',xs:[lt(v('i'),v('size')),lt(v('j'),n(base)),lt(v('k'),n(base))]}),not(le(n(1),get(prefix+'cells',triple(v('i'),v('j'),v('k'))))),le(n(1),get(prefix+'chosen',pack(v('j'),v('k'))))]}}
  const kind:Law={name:prefix+'guarded kind',forall:prefix+'key',holds:{op:'or',xs:[not(lt(v('key'),n(base*base))),le(get(prefix+'chosen',v('key')),n(1))]}},own:Law={name:prefix+'scalar target',holds:le(v('remembered'),n(1))}
  const m:Machine={name:prefix+'machine',params:[prefix+'size'],inputs:['sender','round','value'].map(k=>prefix+k),state:{[prefix+'remembered']:n(0)},maps:{[prefix+'cells']:0,[prefix+'chosen']:0},step:{state:{[prefix+'remembered']:{op:'if',c:{op:'flag',name:prefix+'enabled'},then:n(1),else:v('remembered')}},flags:{[prefix+'ready']:le(n(1),get(prefix+'cells',triple(v('sender'),v('round'),v('value')))),[prefix+'enabled']:{op:'flag',name:prefix+'ready'},[prefix+'disconnected']:le(n(1),get(prefix+'cells',triple(v('round'),v('sender'),v('value'))))}}}
  const laws=[source,kind,own],empty={reads:[],insts:[]},result=sparseReadInstances(m,laws,own,{}, {name:'scalar',hyps:[]},empty),wanted=[v('sender'),v('round'),v('value')]
  const match=result.completeMatches.find(p=>p.law===source.name)!
  expect(match.tuple).toEqual(wanted);expect(match.source.kind).toBe('transition');expect(match.source.path).toEqual(['step','flags',prefix+'ready','b'])
  expect(match.premise).toEqual(assumed([source],{[source.name]:wanted})[0]!);expect(match.premise.op).toBe('or')
  expect(result.at[source.name]).toEqual(wanted);expect(result.at[kind.name]).toEqual([pack(v('round'),v('value'))])
  expect(result.readKindMatches.find(p=>p.law===kind.name)!.premise).toEqual(assumed([kind],{[kind.name]:[pack(v('round'),v('value'))]})[0]!)
  const early=prepareSupport(m,laws,own,{},1);expect(early.at[source.name]).toEqual(wanted);expect(early.at[kind.name]).toEqual([pack(v('round'),v('value'))])
  const quantified:Machine={...m,step:{...m.step,flags:{...m.step.flags,[prefix+'enabled']:{op:'all',key:prefix+'sender',c:le(n(1),get(prefix+'cells',triple(v('sender'),v('round'),v('value'))))}}}}
  expect(completeReadMatches(quantified,[source],own,[],empty)).toHaveLength(0)
  const captured:Machine={...m,step:{...m.step,flags:{...m.step.flags,[prefix+'enabled']:le(n(1),get(prefix+'cells',triple(v('notGlobal'),v('round'),v('value'))))}}}
  expect(completeReadMatches(captured,[source],own,[],empty)).toHaveLength(0)
 }
})

test('root flag arguments retain fixed state/input coordinates without asserting aliases',()=>{
 const n=(value:number):E=>({op:'const',value}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:37,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const q:C={op:'all',key:'tail',c:le(get('cells',pack(pack(x('cursor'),n(0)),x('tail'))),n(1))}
 const p:C={op:'all',key:'value',c:le(get('chosen',pack(x('request'),x('value'))),n(1))}
 const m:Machine={name:'flag argument projection',params:[],inputs:['request'],state:{cursor:n(0)},maps:{cells:0,chosen:0},step:{flags:{bounded:q,other:p}}}
 const own:Law={name:'guarded root',forall:'node',keys:['row','column'],holds:{op:'and',xs:[le(get('cells',pack(pack(x('node'),x('row')),x('column'))),n(1)),le(get('chosen',pack(x('row'),x('column'))),n(1))]}}
 const matches=rootFlagMatches(m,own),bounded=matches.find(p=>p.law==='?bounded')!,other=matches.find(p=>p.law==='?other')!
 expect(keyId(bounded.tuple[0]!)).toBe(keyId(pack(x('row'),x('column'))));expect(bounded.matchingOnly.cursor).toEqual(x('node#'))
 expect(bounded.premise).toEqual({op:'or',xs:[same(x('?bounded'),n(0)),substC(q.c,{vars:{tail:bounded.tuple[0]!},maps:{},flags:{}})]})
 expect(JSON.stringify(bounded.premise)).toContain('cursor');expect(JSON.stringify(bounded.premise)).not.toContain('node#');expect(other.tuple).toEqual([x('column')]);expect(JSON.stringify(other.premise)).toContain('request')
})

test('root and free transition ranges precede ambient read slots',()=>{
 const k=(value:number):E=>({op:'const',value}),get=(map:string,key:E):E=>({op:'get',map,key}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const m:Machine={name:'root range priority',params:['p0','p1','p2','p3','p4'],inputs:['write'],state:{},maps:{cells:0,other:0},step:{maps:{cells:{key:x('write'),value:get('cells',x('write'))}}}}
 const ambient:Law={name:'ambient',holds:{op:'and',xs:m.params.map(p=>le(get('cells',x(p)),k(1)))}},range:Law={name:'cell kind',forall:'k',holds:le(get('cells',x('k')),k(1))},own:Law={name:'root relation',forall:'node',holds:le(get('cells',x('node')),get('other',x('node')))}
 const r=prepareSupport(m,[ambient,range,own],own,{},0),terms=r.at[range.name]!
 expect(terms.slice(0,2)).toEqual([x('node#'),x('write')]);expect(terms.length).toBeLessThanOrEqual(4);expect(r.seedCount).toBeLessThanOrEqual(64)
})

test('count pool keys ignore primitive and duplicate growth but retain exact reads and definitions',()=>{
 const n=(value:number):E=>({op:'const',value}),le=(a:E,b:E):C=>({op:'<=',a,b}),read=get('count',x('key')),post=not(le(read,n(3))),goal:Goal={name:'pool',hyps:[le(read,n(4)),post]}
 const decls:CountDecl[]=[{map:'count',j:'key',key:'item',below:n(8),body:get('cells',x('item'))}],base=countPoolKey(goal,decls)
 expect(countPoolKey({...goal,hyps:[le(get('other',x('fresh')),n(1)),...goal.hyps]},decls)).toBe(base)
 expect(countPoolKey({...goal,hyps:[le(read,n(7)),...goal.hyps]},decls)).toBe(base)
 expect(countPoolKey({...goal,hyps:[le(get('count',{op:'add',a:x('key'),b:n(0)}),n(7)),...goal.hyps]},decls)).not.toBe(base)
 expect(countPoolKey(goal,[{...decls[0]!,body:get('other',x('item'))}])).not.toBe(base)
})

test('v4 selected single-read triples exclude stale, unselected and captured witnesses',()=>{
 for(const base of [19,61])for(const prefix of ['maple_','renamed_']){
  const n=(value:number):E=>({op:'const',value}),v=(s:string)=>x(prefix+s),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:base,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b}),triple=(a:E,b:E,c:E):E=>pack(pack(a,b),c)
  const def={j:prefix+'j',lo:prefix+'low',base,key:prefix+'node',below:v('size'),body:get(prefix+'votes',triple(v('node'),v('j'),v('low')))}
  const m:Machine={name:prefix+'machine',params:[prefix+'size',prefix+'round',prefix+'value',prefix+'enabled'],inputs:[],state:{},maps:{[prefix+'votes']:0,[prefix+'proposal']:0},counts:{[prefix+'query']:def},step:{}}
  const own:Law={name:prefix+'target',holds:le(n(0),v('size'))},law:Law={name:prefix+'ternary',forall:prefix+'i',keys:[prefix+'r',prefix+'v'],holds:{op:'or',xs:[not({op:'and',xs:[le(v('i'),v('size')),same(v('enabled'),n(1))]}),not(le(n(1),get(prefix+'votes',triple(v('i'),v('r'),v('v'))))),le(n(1),get(prefix+'proposal',pack(v('r'),v('v'))))]}}
  const decls:CountDecl[]=[{map:prefix+'query',...def}],cert:Pick<CountCert,'reads'|'insts'>={reads:[[prefix+'read',prefix+'query',pack(v('round'),v('value'))]],insts:[{wit:prefix+'live',below:v('size'),terms:[[1,prefix+'read']],unit:0}]}
  const matches=completeReadMatches(m,[law],own,decls,cert),wanted=[v('live'),v('round'),v('value')]
  expect(matches).toHaveLength(1);expect(matches[0]!.tuple).toEqual(wanted);expect(matches[0]!.source.witness).toBe(prefix+'live');expect(matches[0]!.premise).toEqual(assumed([law],{[law.name]:wanted})[0]!)
  const renamed={...cert,insts:[{...cert.insts[0]!,wit:prefix+'fresh'}]}
  expect(completeReadMatches(m,[law],own,decls,renamed)[0]!.tuple).toEqual([v('fresh'),v('round'),v('value')])
  const poison:Goal={name:'unselected raw read',hyps:[le(n(1),get(prefix+'votes',triple(v('ghost'),v('round'),v('value'))))]}
  expect(sparseReadInstances(m,[law],own,{},poison,cert).completeMatches.every(p=>!JSON.stringify(p).includes(prefix+'ghost'))).toBe(true)
  expect(completeReadMatches(m,[law],own,decls,{...cert,insts:[]})).toHaveLength(0)
  expect(completeReadMatches(m,[law],own,decls,{...cert,insts:[{...cert.insts[0]!,wit:prefix+'size'}]})).toHaveLength(0)
  expect(completeReadMatches(m,[law],own,decls,{...cert,insts:[...cert.insts,...cert.insts]})).toHaveLength(0)
  expect(completeReadMatches(m,[law],own,decls,{...cert,reads:[[prefix+'read',prefix+'query',pack(v('live'),v('value'))]]})).toHaveLength(0)
  expect(completeReadMatches(m,[{...law,some:[prefix+'hidden']}],own,decls,cert)).toHaveLength(0)
  expect(completeReadMatches(m,[{...law,keys:[...law.keys!,prefix+'missing']}],own,decls,cert)).toHaveLength(0)
 }
})

test('v4 complete matches precede optional exhaustion without minting work or source slots',()=>{
 const n=(value:number):E=>({op:'const',value}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:31,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const own:Law={name:'priority root',forall:'a',keys:['b','c','d'],holds:{op:'and',xs:[le(n(1),get('current',pack(x('a'),x('b')))),le(n(1),get('current',pack(x('c'),x('d'))))]}},law:Law={name:'complete',forall:'u',keys:['v'],holds:le(get('current',pack(x('u'),x('v'))),get('dest',pack(x('u'),x('v'))))}
 const m:Machine={name:'shared work control',params:[],inputs:[],state:{},maps:{current:0,dest:0},step:{}},poison=Array.from({length:700},(_,j)=>le(get('current',pack(x('row'+j),x('col'+j))),n(1))),goal:Goal={name:'large optional input',hyps:poison},cert={reads:[],insts:[]},budget=candidateWork();budget.state.work=64800
 const result=sparseReadInstances(m,[law],own,{},goal,cert,64,undefined,[],new Set(),poison,budget)
 expect(result.completeMatches.map(p=>p.tuple)).toEqual([[x('a#'),x('b')],[x('c'),x('d')]])
 expect(result.summary.completeReadAdmissions).toBe(2);expect(result.summary.generationWork.work).toBe(65536);expect(result.summary.generationWork.exhausted).toBe(true)
 expect(budget.state.phases.find(p=>p.phase==='sources:complete')!.work).toBeLessThan(65536)
 const prior={[law.name]:[n(0),n(0),n(1),n(1),n(2),n(2)]},one=sparseReadInstances(m,[law],own,prior,goal,cert,1)
 expect(one.added).toHaveLength(1);expect(one.at[law.name]).toHaveLength(8);expect(prior[law.name]).toHaveLength(6)
 expect(sparseReadInstances(m,[law],own,one.at,goal,cert,64).added.filter(p=>p.law===law.name)).toHaveLength(0)
 expect(sparseReadInstances(m,[law],own,{},goal,cert,0).summary.generationWork.work).toBe(0)
 const stopped=withWall(performance.now()-1,()=>sparseReadInstances(m,[law],own,{},goal,cert,64));expect(stopped.completeMatches).toHaveLength(0);expect(stopped.added.filter(p=>p.law===law.name)).toHaveLength(0);expect(stopped.summary.generationWork.deadline).toBe(true)
})

test('v4 incomplete or fixed-coordinate matches are never labelled complete',()=>{
 const n=(value:number):E=>({op:'const',value}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:43,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const own:Law={name:'root',forall:'a',keys:['b'],holds:le(n(1),get('current',pack(x('a'),x('b'))))},m:Machine={name:'fixed coordinates',params:[],inputs:[],state:{fixed:n(0)},maps:{current:0},step:{}},partial:Law={name:'needs another read',forall:'u',keys:['v','w'],holds:{op:'and',xs:[le(get('current',pack(x('u'),x('v'))),n(1)),le(get('current',pack(x('u'),x('w'))),n(1))]}},fixed:Law={name:'fixed state is not a binder',forall:'v',holds:le(get('current',pack(x('fixed'),x('v'))),n(1))},local:Law={name:'local read hidden',forall:'u',holds:{op:'all',key:'local',c:le(get('current',pack(x('u'),x('local'))),n(1))}}
 expect(completeReadMatches(m,[partial,fixed,local],own,[],{reads:[],insts:[]})).toHaveLength(0)
})

test("bound-only projection keeps NONALIAS satisfiable", () => {
// Newly requested projection controls only; no replay of passed D73/D75 controls.
const json=(v:unknown)=>JSON.stringify(v),num=(value:number):E=>({op:'const',value}),key=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:64,a},b}),m:Machine={name:'projection control',params:[],inputs:[],state:{pr:num(0)},maps:{P:0},step:{}}
const l={name:'fixed-row only',forall:'k',holds:same(get('P',key(x('pr'),x('k'))),num(1))},projection=projectBoundCoordinate(m,key(x('pr'),x('k')),key(x('a'),x('b')),'k')
if(!projection||json(projection.binding)!==json({k:x('b')})||projection.unmatchedFixed[0]?.name!=='pr')throw Error('projection not bound-only')
const premise=assumed([l],{[l.name]:[x('b')]}),conclusion=same(get('P',key(x('a'),x('b'))),num(1)),negative:Goal={name:'nonalias must not prove',hyps:[...premise,not(conclusion)]},positive:Goal={name:'alias proves',hyps:[...premise,same(x('a'),x('pr')),not(conclusion)]},start=performance.now(),until=clock()+1000
const result=counted(fullRate,()=>withWall(start+1000,()=>withDeadline(until,()=>{const n=modelSequence()(negative,until),p=grow(positive,new Map(),{nodes:0,until});return {n,p}})),true)
const negativeSat=!('tree'in result.n)&&result.n.stuck==='sat',positiveChecked='tree'in result.p&&check(positive,result.p.tree),treeRejectsWithoutAlias='tree'in result.p&&!check(negative,result.p.tree),plainRejected=!projectBoundCoordinate(m,x('k'),x('b'),'k')
const out={passed:negativeSat&&positiveChecked&&treeRejectsWithoutAlias&&plainRejected,projection,premise,negativeSat,positiveChecked,treeRejectsWithoutAlias,plainRejected,negativeModel:!('tree'in result.n)?result.n.witness:undefined,wallMs:performance.now()-start}
expect(out.passed).toBe(true)
expect([negativeSat,positiveChecked,treeRejectsWithoutAlias,plainRejected]).toEqual([true,true,true,true])

}, 5000)

test("vacuous query binder is definition-derived", () => {
const k=(value:number):E=>({op:'const',value}),base:CountDecl={map:'T',j:'j',key:'n',below:x('size'),body:{op:'if',c:{op:'=',a:get('Cells',x('n')),b:k(1)},then:k(1),else:k(0)}},law=(holds:C):Law=>({name:'test',forall:'u',holds}),read=law({op:'<',a:k(0),b:get('T',x('u'))}),machine=(d:CountDecl):Machine=>({name:'control',params:['size'],inputs:[],state:{},step:{},counts:{T:d}}),rows:{name:string,actual:boolean,expected:boolean}[]=[]
const test=(name:string,d:CountDecl,l:Law,expected:boolean)=>{const actual=vacuousCountBinder(machine(d),l);rows.push({name,actual,expected});if(actual!==expected)throw Error(name)}
test('ignored single key',base,read,true)
test('decoded both slots ignored',{...base,base:37,lo:'lo'},read,true)
test('primary slot in body',{...base,body:get('Cells',x('j'))},read,false)
test('primary slot in bound',{...base,below:x('j')},read,false)
test('decoded low slot in body',{...base,base:37,lo:'lo',body:get('Cells',x('lo'))},read,false)
test('decoded low slot in bound',{...base,base:37,lo:'lo',below:x('lo')},read,false)
test('base without decoded low slot',{...base,base:37},read,false)
test('low slot without base',{...base,lo:'lo'},read,false)
test('outside scalar occurrence',base,law({op:'and',xs:[read.holds,{op:'<',a:x('u'),b:x('size')}]}),false)
test('outside map occurrence',base,law({op:'and',xs:[read.holds,{op:'<',a:k(0),b:get('Other',x('u'))}]}),false)
test('plain map kind',base,law({op:'<=',a:get('Other',x('u')),b:k(1)}),false)
test('no occurrence',base,law({op:'=',a:k(0),b:k(0)}),false)
const seeded=seedVacuousCounts(machine(base),[read],{},1);if(seeded.added.length!==1||JSON.stringify(seeded.added[0]!.tuple)!==JSON.stringify([k(0)]))throw Error('zero seed')
if(genuinelyKeyless({...base,base:37,lo:'lo',body:get('Cells',x('lo'))}))throw Error('low slot')

}, 5000)

test("selected witness joins reject stale and wrong-map sources", () => {
const n=(value:number):E=>({op:'const',value}),key=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:17,a},b}),positive=(map:string,k:E):C=>({op:'<=',a:n(1),b:get(map,k)}),rows:unknown[]=[]
for(const live of ['arbitraryWitness','anotherLive'])for(const mode of ['positive','no-write-anchor','same-map','different-witness','not-live','wrong-map'] as const){
 const actual=mode==='not-live'?'unselected':live,right=mode==='different-witness'?'other':actual,high=mode==='no-write-anchor'?'unrelatedHigh':'fixed',second=mode==='same-map'?'Promise':'Departed',m:Machine={name:'join test',params:[],inputs:['inputLow'],state:{fixed:n(0)},step:{maps:{Own:{key:key(x('fixed'),x('inputLow')),value:n(1)}}}},own:Law={name:'own',forall:'ownKey',holds:positive('Own',key(x('ownKey'),x('otherOwn')))},l:Law={name:'relation',forall:'node',keys:['hi','lo'],holds:{op:'or',xs:[not(positive('Promise',key(x('hi'),x('node')))),positive(second,key(x('node'),x('lo')))]}},c:Pick<CountCert,'reads'|'insts'>={reads:[['read','Count',n(0)]],insts:[{wit:live,below:n(5),terms:[[1,'read']],unit:0}]},g={name:'goal',hyps:[positive(mode==='wrong-map'?'Different':'Promise',key(x(high),x(actual))),positive(second,key(x(right),x('low')))]},r=sparseReadInstances(m,[l],own,{},g,c,64),wanted=[x(live),x(high),x('low')],found=r.added.find(a=>a.law===l.name&&JSON.stringify(a.tuple)===JSON.stringify(wanted)),expected=mode==='positive'||mode==='no-write-anchor'||mode==='same-map'
 if(!!found!==expected||r.summary.livePairWork>4096||r.added.length>64||r.added.some(a=>!a.coherent))throw Error('live join '+mode)
 if(found&&(!found.sources.every(p=>p.source.kind==='read'&&p.sameMap)||found.sources.length!==2))throw Error('not own-map reads')
 if(expected&&mode!=='same-map')expect(sparseReadInstances(m,[l],own,{},g,c,1).added.some(a=>a.law===l.name&&JSON.stringify(a.tuple)===JSON.stringify(wanted))).toBe(true)
 rows.push({live,mode,expected,found,summary:r.summary})
}

}, 5000)

test('count preparation reserves the same global budget for actual selected witnesses',()=>{
 const n=(value:number):E=>({op:'const',value}),own:Law={name:'root',forall:'key',holds:{op:'<=',a:get('bits',x('key')),b:n(1)}},ranges:Law[]=Array.from({length:80},(_,i)=>({name:'source '+i,forall:'key',holds:{op:'<=',a:get('bits',x('key')),b:n(1)}})),laws=[own,...ranges],m:Machine={name:'reservation control',params:[],inputs:[],state:{},maps:{bits:0},counts:{members:{j:'unused',key:'j',below:n(5),body:get('bits',x('j'))}},step:{}}
 const prepared=prepareSupport(m,laws,own,{},1)
 expect(prepared.seedCount).toBe(32)
 expect(Object.values(prepared.at).reduce((n,ts)=>n+ts.length,0)).toBe(32)
 const ds:CountDecl[]=[{map:'members',j:'unused',key:'j',below:n(5),body:get('bits',x('j'))}],cert={reads:[['read','members',n(0)]] as CountCert['reads'],insts:[{wit:'live',below:n(5),terms:[[1,'read']] as [number,string][],unit:0}]},goal=mcGoal([],ds,cert)!,late=sparseReadInstances(m,laws,own,prepared.at,goal,cert,64-prepared.seedCount,undefined,ds)
 expect(late.added).toHaveLength(32)
 expect(late.added.map(p=>p.tuple)).toEqual(Array.from({length:32},()=>[x('live')]))
 expect(prepared.seedCount+late.added.length).toBe(64)
 expect(Object.values(late.at).every(ts=>ts.length<=4)).toBe(true)
})

test("affine remainder preserves exact polynomial", () => {
const k=(value:number):E=>({op:'const',value}),mul=(n:number,e:E):E=>({op:'mul',k:n,a:e}),add=(a:E,b:E):E=>({op:'add',a,b}),rows:unknown[]=[]
const test=(name:string,p:E,a:E,ns:string[],live:Set<string>,expected:boolean)=>{const r=matchAffineRemainder(p,a,ns,live);if(!!r!==expected)throw Error(name);if(r){const v=linOfE(substE(p,{vars:r.binding,maps:{},flags:{}})),b=linOfE(a);if(!v||!b||canon(v)!==canon(b))throw Error('polynomial '+name)}rows.push({name,expected,result:r})}
for(const [scale,inner,liveName]of [[4096,64,'selectedNode'],[37,5,'renamedWitness']] as const){const p=add(mul(scale,x('node')),x('packed')),a=add(add(mul(scale,x(liveName)),mul(inner,x('round'))),x('value'));test('renamed scale '+scale,p,a,['node','packed'],new Set([liveName]),true)}
const p=add(mul(17,x('node')),x('tail')),a=add(mul(17,x('live')),add(mul(3,x('x')),x('y')))
test('negative remainder constant',add(p,k(3)),add(a,k(1)),['node','tail'],new Set(['live']),false)
test('negative unsupported coefficient',p,add(mul(17,x('live')),mul(-1,x('x'))),['node','tail'],new Set(['live']),false)
test('multi unit ambiguous',add(mul(17,x('node')),add(x('one'),x('two'))),a,['node','one','two'],new Set(['live']),false)
test('other coordinate ambiguous',p,add(add(mul(17,x('live')),mul(17,x('other'))),x('y')),['node','tail'],new Set(['live']),false)
test('fixed coordinate mismatch',add(p,mul(7,x('fixed'))),add(a,mul(7,x('otherFixed'))),['node','tail'],new Set(['live']),false)
test('fixed coordinate unchanged',add(p,mul(7,x('fixed'))),add(a,mul(7,x('fixed'))),['node','tail'],new Set(['live']),true)
test('no current witness',p,a,['node','tail'],new Set(['notLive']),false)
test('fractional unsupported',p,add(mul(17,x('live')),mul(0.5,x('x'))),['node','tail'],new Set(['live']),false)
test('zero remainder',p,mul(17,x('live')),['node','tail'],new Set(['live']),true)

}, 5000)

test("stable selected closure rejects capture and alias", () => {
const k=(value:number):E=>({op:'const',value}),get=(map:string,key:E):E=>({op:'get',map,key}),rows:unknown[]=[]
const ds:CountDecl[]=['A','B'].map(map=>({map,j:'j'+map,key:'node'+map,below:k(5),body:get('cells'+map,x('node'+map))})),g:Goal={name:'control',hyps:[{op:'<=',a:k(0),b:get('A',k(0))}]}
const first:Pick<CountCert,'reads'|'insts'|'picks'>={reads:[['r0','A',k(0)],['r1','B',k(1)]],insts:[{wit:'live0',below:k(5),terms:[[1,'r0'],[1,'r1']],unit:-1}],picks:[]}
const state=stableState([g,ds]),a=stableSelected(g,ds,first,state,{lazyRoom:false,fullPoolUsed:false}),support:Goal={name:'support',hyps:[...g.hyps,{op:'=',a:get('support',x(a.cert.insts[0]!.wit)),b:k(1)}]}
const changed:typeof first={reads:[['r6','A',k(3)],['r8','B',k(1)],['r7','A',k(0)]],insts:[{...first.insts[0]!,wit:'pool900',terms:[[1,'r8'],[1,'r7']]}],picks:[]}
const b=stableSelected(support,ds,changed,state,{lazyRoom:false,fullPoolUsed:false});if(b.cert.insts[0]!.wit!=='live0'||JSON.stringify(support.hyps.at(-1)).includes('pool900'))throw Error('support not stable');rows.push({name:'inserted/reordered read IDs and reversed terms retain actual support witness',result:b.record})
const reject=(name:string,f:()=>unknown)=>{let rejected=false;try{f()}catch{rejected=true}if(!rejected)throw Error(name+' not rejected');rows.push({name,rejected})}
reject('changed definition never reuses old witness',()=>stableSelected(support,[{...ds[0]!,body:get('different',x('nodeA'))},ds[1]!],changed,state,{lazyRoom:false,fullPoolUsed:false}))
reject('nonunique selected names',()=>stableSelected(g,ds,{...first,insts:[...first.insts,...first.insts]},stableState([g,ds]),{lazyRoom:false,fullPoolUsed:false}))
reject('raw source variable collision',()=>stableSelected(g,ds,first,stableState([g,ds,x('live0')]),{lazyRoom:false,fullPoolUsed:false}))
reject('source bound/name collision',()=>stableSelected(g,ds,first,stableState([g,ds,{forall:'live0'}]),{lazyRoom:false,fullPoolUsed:false}))
reject('full pool model view forbidden',()=>stableSelected(g,ds,first,stableState([g,ds]),{lazyRoom:false,fullPoolUsed:true}))
reject('lazy model view forbidden',()=>stableSelected(g,ds,first,stableState([g,ds]),{lazyRoom:true,fullPoolUsed:false}))
const kg:Goal={...g,hyps:[{op:'<',a:k(0),b:k(0)},...g.hyps]},uncut:typeof first={...first,reads:[...first.reads,['unused','A',x('live0')]]},projected=stableSelected(kg,ds,uncut,stableState([g,ds]),{lazyRoom:false,fullPoolUsed:false})
const proof=grow(mcGoal(kg.hyps,ds,projected.cert)!,new Map(),{nodes:0,until:clock()+500});if(!('tree'in proof))throw Error('kernel control tree');const tree=proof.tree
if(!checkMC(kg.hyps,ds,{...projected.cert,tree})||checkMC(kg.hyps,ds,{...uncut,tree}))throw Error('positive kernel projection or uncut capture');rows.push({name:'kernel accepts projected certificate and rejects uncut captured read',projectedCheck:true,uncutCheck:false,record:projected.record})
const captured:typeof first={...uncut,insts:[{...first.insts[0]!,terms:[[1,'r0'],[1,'unused']]}]}
reject('referenced captured read is rejected, never dropped',()=>stableSelected(kg,ds,captured,stableState([g,ds]),{lazyRoom:false,fullPoolUsed:false}));if(checkMC(kg.hyps,ds,{...captured,tree}))throw Error('kernel accepted referenced capture')
const alias:typeof first={...first,reads:[...first.reads,['r0','B',k(4)]]};reject('referenced read identifier alias rejected',()=>stableSelected(kg,ds,alias,stableState([g,ds]),{lazyRoom:false,fullPoolUsed:false}));if(checkMC(kg.hyps,ds,{...alias,tree}))throw Error('kernel accepted read alias')

}, 5000)

test("current target kind instances retain guards", () => {
const c=(value:number):E=>({op:'const',value}),get=(map:string,key:E):E=>({op:'get',map,key}),le=(a:E,b:E):C=>({op:'<=',a,b}),eq=(a:E,b:E):C=>({op:'=',a,b}),add=(a:E,b:E):E=>({op:'add',a,b}),mul=(k:number,a:E):E=>({op:'mul',k,a}),j=x('j'),node=x('node'),key=add(mul(17,node),x('q'))
const m:Machine={name:'renamed-control',params:['size'],inputs:['q'],state:{gate:c(0)},maps:{cells:0,other:0},step:{},counts:{query:{j:'j',key:'node',below:x('size'),body:get('cells',key)},peer:{j:'j',key:'node',below:x('size'),body:get('other',node)}}}
const law:Law={name:'cell-range',forall:'k',holds:le(get('cells',x('k')),c(7))},guarded:Law={name:'guarded-range',forall:'k',holds:{op:'or',xs:[{op:'not',x:eq(x('gate'),c(1))},le(get('cells',x('k')),c(7))]}},wrong:Law={name:'wrong-map',forall:'k',holds:le(get('absent',x('k')),c(7))},nonkind:Law={name:'relation-not-range',forall:'k',holds:le(get('cells',x('k')),get('other',x('k')))},unused:Law={name:'other-key-range',forall:'k',holds:le(get('outside',x('k')),c(1))},own:Law={name:'target',holds:le(get('query',x('q')),x('size'))},bound:Law={name:'seeded-bound',forall:'ignored',holds:le(get('peer',x('ignored')),x('size'))}
const laws=[law,guarded,wrong,nonkind,unused],decls:CountDecl[]=[...Object.entries(m.counts!).map(([map,d])=>({map,...d})),{map:'query#',...m.counts!.query!}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['r','query',x('q')],['s','peer',c(0)]],insts:[{wit:'current',below:x('size'),terms:[[1,'r'],[1,'s']],unit:-1}]},post:C={op:'not',x:le(get('query#',x('q')),x('size'))},sources=seededBoundMaps(m,[bound],[{law:bound.name,tuple:[c(0)]}])
const rows:unknown[]=[],assert=(v:unknown,s:string)=>{if(!v)throw Error(s);rows.push({name:s,passed:true})},matches=targetKindMatches(m,laws,decls,cert,post,sources),actual=add(mul(17,x('current')),x('q'))
assert(matches.length===2&&matches.every(k=>k.map==='cells'&&JSON.stringify(k.tuple)==JSON.stringify([actual])),'only same-map actual current target-body full AST key')
assert(!matches.some(k=>k.law===nonkind.name||k.law===wrong.name||k.law===unused.name),'wrong-map non-body and non-kind laws excluded')
const completeRelation=completeReadMatches(m,[nonkind],own,decls,cert)
assert(completeRelation.length===2&&completeRelation.every(p=>p.coherentReadMatch&&JSON.stringify(p.premise)===JSON.stringify(assumed([nonkind],{[nonkind.name]:p.tuple})[0])),'both exact cells and peer reads can instantiate the generic relation, unlike the kind-only matcher')
assert(bareRangeMap(m,guarded)==='cells'&&matches.find(k=>k.law===guarded.name)?.premise.op==='or','whole guarded PRE retained')
const goal=mcGoal([],decls,{...cert,picks:[]})!,result=sparseReadInstances(m,[law,guarded,wrong,unused],own,{},goal,cert,2,post,decls,sources)
assert(result.added.length===2&&result.summary.sharedGlobalBudget&&result.summary.cap===2,'kinds share total budget rather than additional seeds')
assert(JSON.stringify(assumed([guarded],result.at)[0])===JSON.stringify(matches.find(k=>k.law===guarded.name)!.premise),'kernel receives full original guard and existing bound seven, not invented Booleanity')
assert(sparseReadInstances(m,[law,guarded,wrong,unused],own,result.at,goal,cert,2,post,decls,sources).added.length===0,'already-existing kind instances deduplicated')
const stale={...cert,insts:[{...cert.insts[0]!,wit:'fresh'}]},fresh=targetKindMatches(m,laws,decls,stale,post,sources)
assert(fresh.length===2&&fresh.every(k=>!JSON.stringify(k.tuple).includes('current')&&JSON.stringify(k.tuple).includes('fresh')),'stale witness not reused after current selected instance changes')
assert(targetKindMatches(m,laws,decls,{...cert,insts:[{...cert.insts[0]!,unit:0}]},post,sources).length===0,'non-meet count instance excluded')
assert(targetKindMatches(m,laws,decls.map(d=>d.map==='peer'?{...d,body:get('other',j)}:d),cert,post,sources).length===0,'non-keyless partner is not the selected target meet')
const other={...m.counts!.peer!},two={...m,counts:{...m.counts,unseeded:other}},both=[...decls,{map:'unseeded',...other}],lookalike={...cert,reads:cert.reads.map(r=>r[0]==='s'?['s','unseeded',c(0)] as [string,string,E]:r)}
assert(sources.size===1&&sources.has('peer')&&targetKindMatches(two,laws,both,lookalike,post,sources).length===0&&targetKindMatches(two,laws,both,cert,post,sources).length===2,'both keyless but only actually seeded PRE-bound source qualifies')
assert(targetKindMatches(m,laws,decls,cert,post,seededBoundMaps(m,[bound],[])).length===0,'an existing but unseeded PRE-bound law does not qualify')
const capped=sparseReadInstances(m,[law,guarded,wrong,unused],own,{[law.name]:[c(0),c(1),c(2),c(3)],[guarded.name]:[c(0),c(1),c(2),c(3)]},goal,cert,64,post,decls,sources)
assert(capped.added.length===0,'existing per-law four cap retained')

}, 5000)

test("current flag terms retain flag-false guards", () => {
const k=(value:number):E=>({op:'const',value}),get=(map:string,key:E):E=>({op:'get',map,key}),plus=(a:E,b:E):E=>({op:'add',a,b}),times=(k:number,a:E):E=>({op:'mul',k,a}),eq=(a:E,b:E):C=>({op:'=',a,b}),le=(a:E,b:E):C=>({op:'<=',a,b}),json=(x:unknown)=>JSON.stringify(x)
const rows:unknown[]=[],need=(v:unknown,name:string)=>{if(!v)throw Error(name);rows.push({name,passed:true})}
for(const [scale,radix]of [[97,11],[31,5]]){
 const tail=plus(times(radix!,x('aa')),x('bb')),condition:C={op:'or',xs:[{op:'not',x:eq(x('enabled'),k(1))},le(get('cells',plus(times(scale!,x('cursor')),x('slot'))),k(0))]},q:C={op:'all',key:'slot',c:condition}
 const m:Machine={name:'renamed-flag-control',params:['size','aa','bb'],inputs:[],state:{cursor:k(0),enabled:k(0)},maps:{cells:0,members:0,unrelated:0},step:{flags:{check:q}},counts:{target:{j:'j',key:'node',below:x('size'),body:get('cells',plus(times(scale!,x('node')),tail))},peer:{j:'jp',key:'np',below:x('size'),body:get('members',x('np'))}}}
 const own:Law={name:'plain',holds:le(x('cursor'),x('size'))},bound:Law={name:'bound',forall:'ignored',holds:le(get('peer',x('ignored')),x('size'))},sources=seededBoundMaps(m,[bound],[{law:bound.name,tuple:[k(0)]}]),decls:CountDecl[]=[...Object.entries(m.counts!).map(([map,d])=>({map,...d})),{map:'target#',...m.counts!.target!}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['r','target',k(0)],['s','peer',k(0)]],insts:[{wit:'live',below:x('size'),terms:[[1,'r'],[1,'s']],unit:-1}]},post:C={op:'not',x:le(get('target#',k(0)),x('size'))},matches=targetFlagMatches(m,decls,cert,post,sources),f=matches[0]
 need(matches.length===1&&f&&json(f.tuple)===json([tail]),'arbitrary scale/packed term '+scale+'/'+radix)
 if(!f)throw Error('missing flag')
 const body=substC(condition,{vars:{slot:tail},maps:{},flags:{}})
 need(f.premise.op==='or'&&json(f.premise.xs[1])===json(body),'exact original body with ONLY real binder substitution '+scale)
 need(json(f.matchingOnly.cursor)===json(x('live'))&&json(body).includes('cursor')&&!json(body).includes('live'),'temporary state coordinate binding discarded '+scale)
 need(f.premise.op==='or'&&f.premise.xs[0]?.op==='='&&json(f.premise.xs[0].a)===json(x('?check'))&&json(f.premise.xs[0].b)===json(k(0)),'flag=false retains implication guard '+scale)
 const gg=mcGoal([],decls,{...cert,picks:[]})!,r=sparseReadInstances(m,[own],own,{},gg,cert,1,post,decls,sources)
 need(r.added.length===1&&r.summary.flagAdmissions===1&&r.summary.cap===1,'flag term shares total seed cap '+scale)
 const goal=countedObligations(m,[own],{[own.name]:r.at},0)[1]!.goal
 need(goal.hyps.some(h=>json(h)===json(f.premise))&&goal.hyps.some(h=>json(h)===json(f.domain))&&!goal.hyps.some(h=>json(h)===json(body)),'kernel API preserves domain and guarded body, never assumes body '+scale)
 need(sparseReadInstances(m,[own],own,r.at,gg,cert,1,post,decls,sources).added.length===0,'flag term deduplicated '+scale)
 const wrong={...m,step:{flags:{check:{...q,c:le(get('unrelated',plus(times(scale!,x('cursor')),x('slot'))),k(0))}}}}
 need(targetFlagMatches(wrong,decls,cert,post,sources).length===0,'wrong map rejected '+scale)
 const stale=decls.map(d=>d.map==='target'?{...d,body:get('cells',plus(times(scale!,x('stale')),tail))}:d)
 need(targetFlagMatches(m,stale,cert,post,sources).length===0,'noncurrent source read rejected '+scale)
 const noPrefix={...m,step:{flags:{check:{...q,c:le(get('cells',x('slot')),k(0))}}}}
 need(targetFlagMatches(noPrefix,decls,cert,post,sources).length===0,'non-coordinate flag template rejected '+scale)
}

}, 5000)

test("own PRE instances retain count anchors", () => {
const k=(value:number):E=>({op:'const',value}),get=(map:string,key:E):E=>({op:'get',map,key}),plus=(a:E,b:E):E=>({op:'add',a,b}),times=(k:number,a:E):E=>({op:'mul',k,a}),pack=(a:E,b:E)=>plus(times(47,a),b),le=(a:E,b:E):C=>({op:'<=',a,b}),json=(v:unknown)=>JSON.stringify(v)
const m:Machine={name:'own-pre-control',params:['size','aa','bb','top','chosen','other'],inputs:[],state:{busy:k(0)},maps:{cells:0,prior:0,peerMap:0},step:{},counts:{target:{j:'j',key:'node',below:x('size'),body:get('cells',plus(times(1000,x('node')),x('j')))},peer:{j:'jp',key:'np',below:x('size'),body:get('peerMap',x('np'))}}}
const own:Law={name:'relational bound',forall:'u',keys:['v','c','d'],holds:{op:'or',xs:[{op:'not',x:{op:'and',xs:[le(k(1),get('prior',pack(x('c'),x('d')))),{op:'<',a:x('u'),b:x('c')},{op:'not',x:{op:'=',a:x('v'),b:x('d')}},{op:'<',a:x('v'),b:k(47)},{op:'<',a:x('d'),b:k(47)}]}},{op:'not',x:{op:'<',a:x('size'),b:times(2,get('target',pack(x('u'),x('v'))))}}]}},source:Law={name:'guarded source',holds:{op:'or',xs:[{op:'not',x:{op:'=',a:x('busy'),b:k(1)}},le(k(1),get('prior',pack(x('top'),x('chosen'))))]}},bound:Law={name:'peer bound',forall:'q',holds:le(get('peer',x('q')),x('size'))},sources=seededBoundMaps(m,[bound],[{law:bound.name,tuple:[k(0)]}]),key=pack(x('aa'),x('bb')),decls:CountDecl[]=[...Object.entries(m.counts!).map(([map,d])=>({map,...d})),{map:'target#',...m.counts!.target!}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['r','target',key],['s','peer',k(0)]],insts:[{wit:'live',below:x('size'),terms:[[1,'r'],[1,'s']],unit:-1}]},post:C={op:'not',x:le(get('target#',key),x('size'))}
const rows:unknown[]=[],need=(v:unknown,name:string)=>{if(!v)throw Error(name);rows.push({name,passed:true})},wanted=['aa','bb','top','chosen'].map(x),match=(o=own,ss=source,cc=cert,pre:C[]=[ss.holds])=>ownPREMatches(m,[o,ss],o,decls,cc,post,sources,pre),actual=match()
need(actual.length===1&&json(actual[0]!.tuple)===json(wanted),'complete own tuple from current PRE target count and unquantified PRE source')
need(json(actual[0]!.premise)===json(assumed([own],{[own.name]:wanted})[0])&&json(actual[0]!.sourcePremise)===json(source.holds),'entire original own guard/domain and source guard retained')
need(match(own,source,{...cert,reads:cert.reads.map(r=>r[1]==='target'?[r[0],'wrongCount',r[2]]:r)}).length===0,'wrong count map rejected')
need(match(own,source,{...cert,reads:cert.reads.map(r=>r[1]==='target'?[r[0],r[1],pack(x('other'),x('bb'))]:r)}).length===0,'stale count key rejected by current target selection')
need(match(own,{...source,holds:le(k(1),get('cells',pack(x('top'),x('chosen'))))}).length===0,'wrong primitive source map rejected')
need(match(own,source,cert,[]).length===0,'POST-only source excluded')
need(match(own,{...source,forall:'q'}).length===0,'quantified source excluded')
const conflictOwn={...own,holds:{op:'and',xs:[le(get('target',pack(x('u'),x('v'))),x('size')),le(k(1),get('prior',pack(pack(x('c'),x('u')),x('d'))))]} as C},conflictSource={...source,holds:le(k(1),get('prior',pack(pack(x('top'),x('other')),x('chosen'))))}
need(match(conflictOwn,conflictSource).length===0,'conflicting anchor/source bindings rejected')
const g=mcGoal([source.holds,post],decls,{...cert,picks:[]})!,add=sparseReadInstances(m,[own,source],own,{},g,cert,1,post,decls,sources,[source.holds])
need(add.added.length===1&&add.summary.ownPREAdmissions===1&&json(add.at[own.name])===json(wanted),'own exception admitted in shared global budget')
need(sparseReadInstances(m,[own,source],own,{},g,cert,0,post,decls,sources,[source.holds]).added.length===0,'zero global budget honored')
const four=Array.from({length:4},(_,i)=>[k(i),k(i),k(i),k(i)]).flat()
need(sparseReadInstances(m,[own,source],own,{[own.name]:four},g,cert,1,post,decls,sources,[source.holds]).summary.ownPREAdmissions===0,'four per own law cap unchanged')
const names=['size','aa','bb','top','chosen','other','busy','cells','prior','peerMap','target','target#','peer','j','node','jp','np','u','v','c','d','live','r','s','q',own.name,source.name],ren=Object.fromEntries(names.map((n,i)=>[n,'renamed'+i]));ren['target#']=ren.target!+'#';const inv=Object.fromEntries(Object.entries(ren).map(([a,b])=>[b,a])),rename=(v:unknown,by:Record<string,string>):unknown=>typeof v==='string'?(by[v]??v):Array.isArray(v)?v.map(x=>rename(x,by)):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([a,b])=>[by[a]??a,rename(b,by)])):v
const other=ownPREMatches(rename(m,ren) as Machine,rename([own,source],ren) as Law[],rename(own,ren) as Law,rename(decls,ren) as CountDecl[],rename(cert,ren) as typeof cert,rename(post,ren) as C,new Set([...sources].map(s=>ren[s]??s)),rename([source.holds],ren) as C[])
need(json(rename(other,inv))===json(actual),'name-independent renaming covariance')

}, 5000)

test("remaining-coordinate proposals never assert alias", () => {
const k=(value:number):E=>({op:'const',value}),get=(map:string,key:E):E=>({op:'get',map,key}),plus=(a:E,b:E):E=>({op:'add',a,b}),times=(k:number,a:E):E=>({op:'mul',k,a}),pack=(a:E,b:E)=>plus(times(47,a),b),le=(a:E,b:E):C=>({op:'<=',a,b}),lt=(a:E,b:E):C=>({op:'<',a,b}),json=(v:unknown)=>JSON.stringify(v)
const m:Machine={name:'remaining-coordinate control',params:['size','aa','bb','top','chosen','other'],inputs:[],state:{busy:k(0)},maps:{cells:0,prior:0,peerMap:0,wrong:0},step:{},counts:{target:{j:'j',key:'node',below:x('size'),body:get('cells',plus(times(1000,x('node')),x('j')))},peer:{j:'jp',key:'np',below:x('size'),body:get('peerMap',x('np'))}}}
const law:Law={name:'guarded uniqueness',forall:'u',keys:['v','w'],holds:{op:'or',xs:[not({op:'and',xs:[same(x('busy'),k(1)),le(k(1),get('prior',pack(x('u'),x('v')))),le(k(1),get('prior',pack(x('u'),x('w')))),lt(x('v'),k(47)),lt(x('w'),k(47))]}),same(x('v'),x('w'))]}},source:Law={name:'guarded actual source',holds:{op:'or',xs:[not(same(x('busy'),k(1))),le(k(1),get('prior',pack(x('top'),x('chosen'))))]}},own:Law={name:'current target',holds:le(k(0),x('size'))},bound:Law={name:'source bound',forall:'q',holds:le(get('peer',x('q')),x('size'))}
const key=pack(x('aa'),x('bb')),anchorHyp=le(k(1),get('prior',key)),pre=[anchorHyp,source.holds],maps=seededBoundMaps(m,[bound],[{law:bound.name,tuple:[k(0)]}]),decls:CountDecl[]=[...Object.entries(m.counts!).map(([map,d])=>({map,...d})),{map:'target#',...m.counts!.target!}],cert:Pick<CountCert,'reads'|'insts'>={reads:[['r','target',key],['s','peer',k(0)]],insts:[{wit:'live',below:x('size'),terms:[[1,'r'],[1,'s']],unit:-1}]},post:C=not(le(get('target#',key),x('size')))
const rows:unknown[]=[],need=(v:unknown,name:string)=>{if(!v)throw Error(name);rows.push({name,passed:true})},match=(l=law,s=source,p:C[]=[anchorHyp,s.holds],cc=cert,po=post)=>remainingCoordinateProposals(m,[l,s],decls,cc,po,maps,p),actual=match(),wanted=['aa','bb','chosen'].map(x),p=actual.find(p=>json(p.tuple)===json(wanted))
need(p&&actual.length===2,'both whole-law orientations proposed from exact current PRE anchor')
need(p&&!p.coherentReadMatch&&p.ignoredCounterpartCoordinates.length===1&&p.ignoredCounterpartCoordinates[0]?.binder==='u'&&!p.sourceKeyReconstructed,'different source row logged as ignored counterpart, never coherent read equality')
need(p&&json(p.anchor)===json({u:x('aa'),v:x('bb')})&&json(p.term)===json(x('chosen')),'only remaining binder proposed, anchor coordinates retained')
need(p&&json(p.premise)===json(assumed([law],{[law.name]:wanted})[0]),'original whole PRE body, guards and domain equal kernel substitution')
need(p&&json(p.sourcePremise)===json(source.holds),'whole unquantified guarded PRE source retained')
need(match(law,source,[le(k(1),get('wrong',key)),source.holds]).length===0,'wrong map anchor rejected')
need(match(law,source,[le(k(1),get('prior',pack(x('other'),x('bb')))),source.holds]).length===0,'stale anchor rejected')
need(match(law,source,pre,cert,not(le(get('target#',pack(x('other'),x('bb'))),x('size')))).length===0,'non-target count key rejected')
need(match(law,source,[source.holds]).length===0,'missing actual PRE anchor rejected')
need(match(law,source,[anchorHyp]).length===0,'POST-only source rejected')
need(match(law,{...source,forall:'q'}).length===0,'quantified source rejected')
need(match({...law,keys:['v','w','extra']}).length===0,'multiple remaining binders rejected')
need(match(law,{...source,holds:le(k(1),get('wrong',pack(x('top'),x('chosen'))))}).length===0,'wrong map source rejected')
need(match(law,{...source,holds:le(k(1),get('prior',plus(x('top'),x('chosen'))))}).length===0,'ambiguous coefficient projection rejected')
need(match(law,{...source,holds:le(k(1),get('prior',plus(times(-47,x('top')),x('chosen'))))}).length===0,'negative coefficient projection rejected')
const g=mcGoal([...pre,post],decls,{...cert,picks:[]})!,add=sparseReadInstances(m,[law,source],own,{},g,cert,1,post,decls,maps,pre)
need(add.summary.termProposalAdmissions===1&&add.added.length===1&&add.summary.sharedGlobalBudget,'proposal priority shares global admission budget')
need(sparseReadInstances(m,[law,source],own,{},g,cert,0,post,decls,maps,pre).added.length===0,'zero total budget preserved')
const four=Array.from({length:4},(_,i)=>[k(i),k(i),k(i)]).flat()
need(sparseReadInstances(m,[law,source],own,{[law.name]:four},g,cert,64,post,decls,maps,pre).summary.termProposalAdmissions===0,'four per law preserved')
need(sparseReadInstances(m,[law,source],own,{[law.name]:actual.flatMap(p=>p.tuple)},g,cert,64,post,decls,maps,pre).summary.termProposalAdmissions===0,'existing proposals deduplicated')
// No alias equation is ever emitted above. The equation below belongs ONLY to the positive control.
const full=assumed([law],{[law.name]:wanted})[0]!,base=[full,...pre,same(x('busy'),k(1)),lt(x('bb'),k(47)),lt(x('chosen'),k(47)),not(same(x('bb'),x('chosen')))],negative:Goal={name:'distinct rows may propose distinct values',hyps:[...base,not(same(x('aa'),x('top')))]},positive:Goal={name:'explicit row alias closes uniqueness',hyps:[...base,same(x('aa'),x('top'))]},start=performance.now(),until=clock()+1000
const result=counted(fullRate,()=>withWall(start+1000,()=>withDeadline(until,()=>{const n=modelSequence()(negative,until),p=grow(positive,new Map(),{nodes:0,until});return {n,p}})),true)
need(!('tree'in result.n)&&result.n.stuck==='sat','NONALIAS negative remains satisfiable with different values in different rows')
need('tree'in result.p&&check(positive,result.p.tree),'alias positive independently kernel checked')
need('tree'in result.p&&!check(negative,result.p.tree),'alias proof rejected without alias premise')
const names=['size','aa','bb','top','chosen','other','busy','cells','prior','peerMap','wrong','target','target#','peer','j','node','jp','np','u','v','w','live','r','s','q',law.name,source.name],ren=Object.fromEntries(names.map((n,i)=>[n,'renamed'+i]));ren['target#']=ren.target!+'#';const inv=Object.fromEntries(Object.entries(ren).map(([a,b])=>[b,a])),rename=(v:unknown,by:Record<string,string>):unknown=>typeof v==='string'?(by[v]??v):Array.isArray(v)?v.map(x=>rename(x,by)):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([a,b])=>[by[a]??a,rename(b,by)])):v
const other=remainingCoordinateProposals(rename(m,ren) as Machine,rename([law,source],ren) as Law[],rename(decls,ren) as CountDecl[],rename(cert,ren) as typeof cert,rename(post,ren) as C,new Set([...maps].map(s=>ren[s]??s)),rename(pre,ren) as C[])
need(json(rename(other,inv))===json(actual),'complete renaming covariance')
const scale=(v:unknown):unknown=>Array.isArray(v)?v.map(scale):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([n,x])=>[n,((v as E).op==='mul'&&n==='k'&&x===47)||((v as E).op==='const'&&n==='value'&&x===47)||(n==='coefficient'&&x===47)?83:scale(x)])):v
const scaled=remainingCoordinateProposals(scale(m) as Machine,scale([law,source]) as Law[],scale(decls) as CountDecl[],scale(cert) as typeof cert,scale(post) as C,maps,scale(pre) as C[])
need(json(scaled)===json(scale(actual)),'arbitrary packing scale covariance')

}, 5000)

test('generic root-linked terms retain anchors and cross the real early phase gate',()=>{
 for(const base of [17,83])for(const prefix of ['first','alpha']){
  const n=(v:number):E=>({op:'const',value:v}),v=(s:string)=>x(prefix+s),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:base,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b}),lt=(a:E,b:E):C=>({op:'<',a,b})
  const own:Law={name:prefix+'root',forall:prefix+'row',keys:[prefix+'value'],holds:le(n(1),get(prefix+'cells',pack(v('row'),v('value'))))}
  const law:Law={name:prefix+'unique',forall:prefix+'a',keys:[prefix+'b',prefix+'c'],holds:{op:'or',xs:[not({op:'and',xs:[lt(v('a'),n(base)),lt(v('b'),n(base)),lt(v('c'),n(base)),not(same(v('b'),v('c')))]}),not({op:'and',xs:[le(n(1),get(prefix+'cells',pack(v('a'),v('b')))),le(n(1),get(prefix+'cells',pack(v('a'),v('c'))))]})]}}
  const m:Machine={name:prefix+' generic',params:[prefix+'N'],inputs:[prefix+'inputRow',prefix+'inputValue'],state:{},maps:{[prefix+'cells']:0},step:{maps:{[prefix+'cells']:{key:pack(v('inputRow'),v('inputValue')),value:n(1)}}}}
  const prepared=prepareSupport(m,[own,law],own,{},1),wanted=[v('row#'),v('value'),v('inputValue')]
  expect(prepared.at[law.name]!.length).toBeLessThanOrEqual(6) // equivalent cold permutations share one source slot
  const p=prepared.termAdmissions.find(p=>JSON.stringify(p.tuple)===JSON.stringify(wanted))
  expect(p).toBeDefined();expect(p!.rootLinked).toBe(true);expect(p!.coherentReadMatch).toBe(false)
  expect(p!.anchor).toEqual({[prefix+'a']:v('row#'),[prefix+'b']:v('value')});expect(p!.sourceKeyReconstructed).toBe(false)
  expect(p!.ignoredCounterpartCoordinates).toEqual([{binder:prefix+'a',retained:v('row#'),counterpart:v('inputRow')}])
  expect(p!.premise).toEqual(assumed([law],{[law.name]:wanted})[0]!);expect(p!.sourceKind).toBe('write')
  expect(prepared.seedCount).toBeLessThanOrEqual(64);expect((prepared.at[law.name]?.length??0)/3).toBeLessThanOrEqual(4)
  // The emitted law is still conditional on its two actual cells, never on an added row equality.
  const gs=countedObligations(m,[own,law],{[own.name]:prepared.at},0)
  expect(gs[1]!.goal.hyps).toContainEqual(p!.premise)
  expect(gs[1]!.goal.hyps).not.toContainEqual(same(v('row#'),v('inputRow')))
  const boundStep:Machine={...m,step:{maps:{[prefix+'cells']:{each:prefix+'local',value:get(prefix+'cells',pack(v('inputRow'),v('local')))}}}}
  expect(prepareSupport(boundStep,[own,law],own,{},1).termAdmissions).toHaveLength(0)
 }
})

test('full source occupancy replaces only structurally true slots; substantive slots refuse',()=>{
 const n=(value:number):E=>({op:'const',value}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:23,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const own:Law={name:'root',forall:'u',keys:['v'],holds:le(n(1),get('cells',pack(x('u'),x('v'))))}
 const law:Law={name:'unique',forall:'a',keys:['b','c'],holds:{op:'or',xs:[not(not(same(x('b'),x('c')))),not({op:'and',xs:[le(n(1),get('cells',pack(x('a'),x('b')))),le(n(1),get('cells',pack(x('a'),x('c'))))]})]}}
 const fillers:Law[]=Array.from({length:14},(_,i)=>({name:'filler'+i,forall:'z',holds:le(get('other',x('z')),n(1))}))
 const laws=[own,law,...fillers],m:Machine={name:'full generic',params:[],inputs:['row','value'],state:{},maps:{cells:0,other:0},step:{maps:{cells:{key:pack(x('row'),x('value')),value:n(1)}}}}
 const full=(diagonal:boolean)=>Object.fromEntries([[own.name,Array.from({length:4},(_,i)=>[n(i),n(i+1)]).flat()],[law.name,Array.from({length:4},(_,i)=>[n(i),n(i+1),n(i+(diagonal?1:2))]).flat()],...fillers.map(l=>[l.name,[n(0),n(1),n(2),n(3)]])])
 const original=full(true),prepared=prepareSupport(m,laws,own,original,1)
 expect(prepared.seedCount).toBe(prepared.replacements.length);expect(prepared.replacements.length).toBeGreaterThan(0)
 for(const r of prepared.replacements){expect(r.law).toBe(law.name);expect(r.tuple[1]).toEqual(r.tuple[2]);expect(r.reason).toBe('structurally-true');expect(r.origin).toBe('initial');expect(r.admissionDebit).toBe(1);expect(r.replacement.coherentReadMatch).toBe(false)}
 for(const l of laws)expect((prepared.at[l.name]?.length??0)/(1+(l.keys?.length??0))).toBe(4)
 for(const l of fillers)expect(prepared.at[l.name]).toEqual(original[l.name])
 const substantive=full(false),refused=prepareSupport(m,laws,own,substantive,1)
 expect(refused.seedCount).toBe(0);expect(refused.replacements).toHaveLength(0);expect(refused.at).toEqual(substantive)
 const expired=withWall(performance.now()-1,()=>prepareSupport(m,laws,own,original,1))
 expect(expired.replacements).toHaveLength(0);expect(expired.at).toEqual(original);expect(expired.generationWork.deadline).toBe(true)
})

test('replacement reuses a cold source debit without exceeding the reserved initial cap',()=>{
 const n=(value:number):E=>({op:'const',value}),le=(a:E,b:E):C=>({op:'<=',a,b}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:29,a},b})
 const own:Law={name:'root',forall:'u',keys:['v'],holds:le(n(1),get('cells',pack(x('u'),x('v'))))}
 const law:Law={name:'unique',forall:'a',keys:['b','c'],holds:{op:'or',xs:[same(x('b'),x('c')),not({op:'and',xs:[le(n(1),get('cells',pack(x('a'),x('b')))),le(n(1),get('cells',pack(x('a'),x('c'))))]})]}}
 const countLaws:Law[]=Array.from({length:64},(_,i)=>({name:'budget'+i,forall:'unused',holds:{op:'or',xs:[same(n(0),n(0)),le(get('T',x('unused')),n(3))]}}))
 const m:Machine={name:'debit provenance',params:[],inputs:['row','value'],state:{},maps:{cells:0},step:{maps:{cells:{key:pack(x('row'),x('value')),value:n(1)}}},counts:{T:{j:'j',key:'k',below:n(3),body:n(0)}}}
 const laws=[...countLaws,law,own],produced=prepareSupport(m,laws,own,{},1)
 expect(produced.seedCount).toBe(32);expect(produced.replacements.length).toBeGreaterThan(0)
 expect(produced.replacements.every(r=>r.origin==='new-source'&&r.admissionDebit===0)).toBe(true)
 const tupleCount=laws.reduce((s,l)=>s+(produced.at[l.name]?.length??0)/(1+(l.keys?.length??0)),0)
 expect(tupleCount).toBe(32)
 const initial={[law.name]:Array.from({length:4},(_,i)=>[n(i),n(i),n(i)]).flat()},blocked=prepareSupport(m,laws,own,initial,1)
 expect(blocked.seedCount).toBe(32);expect(blocked.at[law.name]).toEqual(initial[law.name]);expect(blocked.replacements).toHaveLength(0)
})

test('pre-existing CTI tuples do not consume the new source-proposal budget or trigger a new global refusal',()=>{
 const n=(value:number):E=>({op:'const',value}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const m:Machine={name:'CTI compatibility',params:[],inputs:[],state:{},maps:{cells:0},step:{}},own:Law={name:'target',holds:le(n(0),n(1))}
 const laws:Law[]=Array.from({length:18},(_,i)=>({name:'source'+i,forall:'key',holds:le(get('cells',x('key')),n(i+1))}))
 const initial=Object.fromEntries(laws.map(l=>[l.name,[n(0),n(1),n(2),n(3)]])),prepared=prepareSupport(m,[...laws,own],own,initial,1)
 expect(Object.values(initial).reduce((n,ts)=>n+ts.length,0)).toBe(72)
 expect(prepared.at).toEqual(initial);expect(prepared.seedCount).toBe(0);expect(prepared.replacements).toHaveLength(0)
 const overfull={...initial,[laws[0]!.name]:[n(0),n(1),n(2),n(3),n(4)]}
 expect(prepareSupport(m,[...laws,own],own,overfull,1).at).toEqual(overfull)
})

test('selection covers both concrete root keys before redundant and keyless differences',()=>{
 const n=(value:number):E=>({op:'const',value}),le=(a:E,b:E):C=>({op:'<=',a,b}),keys=[x('rootA#'),x('rootB')]
 const ds:CountDecl[]=['A','B','C','fixedA','fixedB'].map(map=>({map,j:'outer',key:'cell',below:n(11),body:get('cells',map.startsWith('fixed')?x('cell'):{op:'add',a:x('outer'),b:x('cell')})}))
 const g:Goal={name:'two root keys',hyps:[not({op:'and',xs:keys.map(k=>le(n(1),get('primitive',k)))})]},reads:CountCert['reads']=[]
 for(const key of keys)for(const d of ds)reads.push(['read'+reads.length,d.map,key])
 const insts:CountCert['insts']=[],add=(a:number,b:number)=>insts.push({wit:'wit'+insts.length,below:n(11),unit:0,terms:[[1,reads[a]![0]],[-1,reads[b]![0]]]})
 for(let j=0;j<4;j++)add(3,4)
 add(0,1);add(0,2);add(1,0);add(1,2);add(2,0);add(2,1);add(5,6);add(5,7)
 const full={reads,insts,wits:insts.map(i=>i.wit),picks:[],loose:false},selected=smallSelection(g,ds,full,[x('rootA'),keys[1]!],{reads:[],picks:[]})
 expect(selected.insts.slice(0,2)).toEqual([insts[4]!,insts[10]!])
 expect(selected.insts.length).toBeLessThanOrEqual(10)
 const stable=selectedCertificate(g,ds,selected,stableState([g,ds]),false)
 expect(stable.reads.length).toBeLessThanOrEqual(30);expect(new Set(stable.insts.map(i=>i.wit)).size).toBe(stable.insts.length)
 expect(mcGoal(g.hyps,ds,stable)).toBeDefined()
 expect(stable.insts.every(i=>full.insts.includes(i)||full.insts.some(j=>JSON.stringify(j)===JSON.stringify(i)))).toBe(true)
 expect(()=>selectedCertificate(g,ds,{...selected,insts:selected.insts.map(i=>({...i,below:n(12)}))},stableState([g,ds]),false)).toThrow()
})

test('definition-linked PRE candidates, reservation and ten/1000 limits', () => {
 const k=(value:number):E=>({op:'const',value}),cell=(map:string,key:E):E=>({op:'get',map,key})
 const ds:CountDecl[]=[
  {map:'base',j:'j',key:'node',below:k(9),body:cell('members',x('node'))},
  {map:'missing',j:'j',key:'node',below:k(9),body:{op:'if',c:{op:'and',xs:[same(cell('members',x('node')),k(1)),same(cell('relation',x('node')),k(0))]},then:k(1),else:k(0)}},
  {map:'target',j:'j',key:'node',below:k(9),body:cell('relation',{op:'add',a:x('node'),b:x('j')})},
  {map:'target#',j:'j',key:'node',below:k(9),body:cell('relation#',{op:'add',a:x('node'),b:x('j')})},
 ]
 const g:Goal={name:'lower target',hyps:[{op:'<=',a:cell('base',k(0)),b:cell('missing',k(0))},not({op:'<=',a:k(3),b:cell('target#',k(0))})]}
 const pool=grammarPool(g,ds,1000), selected=polaritySelection(g,ds,pool)
 expect(pool.full.insts.length).toBeLessThanOrEqual(1000)
 expect(selected.pick.insts.length).toBeLessThanOrEqual(10)
 expect(pool.added.some(p=>p.reason==='definition-linked PRE triple')).toBe(true)
 const previous={...pool.full,insts:[pool.added.find(p=>p.reason==='definition-linked PRE triple')!.instance],picks:[]}
 const chosen=new Set(ids(previous)), truncated={...pool,full:{...pool.full,insts:[],wits:[]}}
 const restored=reservePool(g,ds,truncated,previous,ds,chosen,{next:1000,inserted:new Map()},1000)
 expect(ids(restored.full).filter(id=>id.startsWith('i'))).toEqual([...chosen])
 expect(mcGoal(g.hyps,ds,{...restored.full,picks:[]})).toBeDefined()
 expect(()=>reservePool(g,ds.map(d=>d.map==='missing'?{...d,body:k(0)}:d),truncated,previous,ds,chosen,{next:1000,inserted:new Map()},1000)).toThrow()
 const large:Goal={name:'large pool',hyps:Array.from({length:55},(_,i)=>same(cell('target',k(i)),k(0)))}
 expect(grammarPool(large,ds,1000).full.insts.length).toBe(1000)
})

test('regenerated cold binders cannot steal a selected witness owner',()=>{
 const z:E={op:'const',value:0},one:E={op:'const',value:1},five:E={op:'const',value:5},g:Goal={name:'owned pool',hyps:[same(z,z)]},ds:CountDecl[]=[{map:'count',j:'j',key:'k',below:five,body:get('cells',x('k'))}]
 const reads:CountCert['reads']=[['a','count',z],['b','count',one]],selected:CountCert['insts'][number]={wit:'leased',below:five,terms:[[1,'a']],unit:0},cold:CountCert['insts'][number]={wit:'leased',below:five,terms:[[1,'b']],unit:0},previous={reads:[reads[0]!],insts:[selected],picks:[]},chosen=new Set(ids(previous)),base=grammarPool(g,ds),pool={...base,full:{...base.full,reads,insts:[cold],wits:['leased'],picks:[]}}
 const state=reservationState(g,[g,ds],1000),r=reservePool(g,ds,pool,previous,ds,chosen,state)
 expect(r.record.renamed).toHaveLength(1);expect(r.full.insts.find(i=>i.terms[0]?.[1]==='a')?.wit).toBe('leased');expect(r.full.insts.find(i=>i.terms[0]?.[1]==='b')?.wit).not.toBe('leased');expect(pool.full.insts[0]!.wit).toBe('leased');expect(mcGoal(g.hyps,ds,r.full)).toBeDefined()
 const dependent={...pool,full:{...pool.full,picks:[['b',[x('leased')]]] as [string,E[]][]}}
 const safelyDropped=reservePool(g,ds,dependent,previous,ds,chosen,reservationState(g,[g,ds],1000))
 expect(safelyDropped.record.quarantined).toEqual([cold]);expect(safelyDropped.full.insts).toEqual([selected]);expect(mcGoal(g.hyps,ds,safelyDropped.full)).toBeDefined()
 const twoOwners={...previous,reads,insts:[selected,{...cold,wit:'secondOwner'}]}
 const canonical=reservePool(g,ds,dependent,twoOwners,ds,new Set(ids(twoOwners)),reservationState(g,[g,ds],1000))
 expect(canonical.full.insts.map(i=>i.wit)).toEqual(['leased','secondOwner']);expect(mcGoal(g.hyps,ds,canonical.full)).toBeDefined()
 const duplicate={...previous,reads,insts:[selected,cold]}
 expect(()=>reservePool(g,ds,pool,duplicate,ds,new Set(ids(duplicate)),reservationState(g,[g,ds],1000))).toThrow(UnsupportedCountProposal)
 expect(()=>reservePool(g,ds,pool,previous,ds,chosen,reservationState(g,[g,ds,x('leased')],1000))).toThrow('owned witness capture/source')
})

test('present vacuous source survives an idempotent second seed',()=>{
 const m:Machine={name:'present source',params:['N'],inputs:[],state:{},maps:{cells:0},step:{},counts:{query:{j:'j',key:'k',below:x('N'),body:get('cells',x('k'))}}}
 const l:Law={name:'bound',forall:'q',holds:{op:'<=',a:get('query',x('q')),b:x('N')}}
 const first=seedVacuousCounts(m,[l],{},64),second=seedVacuousCounts(m,[l],first.at,64)
 expect(second.added).toEqual([])
 expect([...sourceBoundMaps(m,[l],second.at)]).toEqual(['query'])
 expect([...sourceBoundMaps(m,[l],{})]).toEqual([])
})
test('picked selected view falls back without renaming or extending a budget; captured views reject',()=>{
 const z:E={op:'const',value:0},ds:CountDecl[]=[{map:'count',j:'j',key:'k',below:{op:'const',value:5},body:get('cells',x('k'))}],g:Goal={name:'picked',hyps:[same(z,z)]}
 const view={reads:[['r','count',z]] as CountCert['reads'],insts:[{wit:'selected',below:{op:'const',value:5} as E,terms:[[1,'r']] as [number,string][],unit:0}],picks:[['r',[z]]] as [string,E[]][]}
 const result=selectedCertificate(g,ds,view,stableState([ds,g]),false)
 expect(result.reads).toEqual(view.reads);expect(result.insts).toEqual(view.insts);expect(result.picks).toEqual(view.picks)
 expect(()=>selectedCertificate(g,ds,{...view,reads:[['r','count',x('selected')]]},stableState([ds,g]),false)).toThrow(UnsupportedCountProposal)
 expect(()=>selectedCertificate(g,ds,view,stableState([ds,g,x('selected')]),false)).toThrow(UnsupportedCountProposal)
})
test('cold range reads cannot fill count-pass slots before current selected-body reads',()=>{
 const k=(value:number):E=>({op:'const',value}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const m:Machine={name:'priority control',params:['N'],inputs:[],state:{},maps:{cells:0,other:0},step:{},counts:{query:{j:'j',key:'node',below:x('N'),body:get('cells',x('node'))},peer:{j:'j',key:'node',below:x('N'),body:get('other',x('node'))}}}
 const kind:Law={name:'range',forall:'cell',holds:le(get('cells',x('cell')),k(7))},bound:Law={name:'bound',forall:'ignored',holds:le(get('peer',x('ignored')),x('N'))},own:Law={name:'goal',holds:{op:'and',xs:[...Array.from({length:6},(_,i)=>le(get('cells',k(i)),k(7))),le(get('query',k(0)),x('N'))]}}
 const prepared=prepareSupport(m,[kind,bound,own],own,{},1)
 expect(prepared.at[kind.name]??[]).toEqual([])
 const decls:CountDecl[]=[...Object.entries(m.counts!).map(([map,d])=>({map,...d})),{map:'query#',...m.counts!.query!}],cert={reads:[['r','query',k(0)],['s','peer',k(0)]] as CountCert['reads'],insts:[{wit:'hot',below:x('N'),terms:[[1,'r'],[1,'s']] as [number,string][],unit:-1}]},post=not(le(get('query#',k(0)),x('N'))),g=mcGoal([post],decls,cert)!
 const selected=sparseReadInstances(m,[kind],own,prepared.at,g,cert,64-prepared.seedCount,post,decls,prepared.sourceMaps)
 expect(selected.at[kind.name]).toEqual([x('hot')])
 expect(selected.added.length+prepared.seedCount).toBeLessThanOrEqual(64)
})


test('sparse generation counts no-op read/read pairs and exits before cap-zero/full-source work',()=>{
 const n=(value:number):E=>({op:'const',value}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:17,a},b})
 const m:Machine={name:'read-only sparse stress',params:[],inputs:[],state:{},step:{}},own:Law={name:'target',holds:same(n(0),n(0))},l:Law={name:'two-coordinate relation',forall:'hi',keys:['lo'],holds:same(get('R',pack(x('hi'),x('lo'))),n(1))}
 const goal:Goal={name:'many reads with no current witness',hyps:Array.from({length:600},(_,i)=>same(get('R',pack(x('row'+i),x('column'+i))),n(1)))},cert={reads:[],insts:[]},budget=candidateWork()
 const first=sparseReadInstances(m,[l],own,{},goal,cert,64,undefined,[],new Set(),[],budget)
 expect(first.added).toHaveLength(0);expect(first.summary.livePairWork).toBe(0)
 expect(first.summary.generationWork.exhausted).toBe(true);expect(first.summary.generationWork.work).toBe(65536)
 const again=sparseReadInstances(m,[l],own,{},goal,cert,64,undefined,[],new Set(),[],budget)
 expect(again.summary.generationWork.work).toBe(65536);expect(again.added).toHaveLength(0)
 const zero=sparseReadInstances(m,[l],own,{},goal,cert,0)
 expect(zero.added).toHaveLength(0);expect(zero.summary.generationWork.work).toBe(0)
 const full=sparseReadInstances(m,[l],own,{[l.name]:Array.from({length:8},(_,i)=>n(i))},goal,cert,64)
 expect(full.added).toHaveLength(0);expect(full.summary.generationWork.work).toBe(0)
 const expired=withWall(performance.now()-1,()=>sparseReadInstances(m,[l],own,{},goal,cert,64))
 expect(expired.summary.generationWork.deadline).toBe(true);expect(expired.added).toHaveLength(0)
})

test('pool enumeration has finite work even when cubic candidates never admit',()=>{
 const k=(value:number):E=>({op:'const',value}),ds:CountDecl[]=[],hyps:C[]=[]
 for(let i=0;i<90;i++){
  const map='count'+i,body:E=i<30?get('A',k(0)):i<60?{op:'if',c:{op:'and',xs:[same(get('A',k(0)),k(1)),same(get('B',k(0)),k(1))]},then:k(1),else:k(0)}:{op:'add',a:get('B',k(0)),b:{op:'mul',k:0,a:x('j')}}
  ds.push({map,j:'j',key:'cell',below:k(i+1),body});hyps.push(same(get(map,k(0)),k(0)))
 }
 const out=grammarPool({name:'cubic no admission',hyps},ds)
 expect(out.work.exhausted).toBe(true);expect(out.work.work).toBeLessThanOrEqual(out.work.limit)
 expect(out.work.capReached).toBe(false);expect(out.added).toHaveLength(0)
 expect(out.proposed.length).toBeLessThanOrEqual(128);expect(out.full.insts.length).toBeLessThanOrEqual(1000)
 const expired=withWall(performance.now()-1,()=>grammarPool({name:'expired',hyps},ds))
 expect(expired.work.deadline).toBe(true);expect(expired.work.work).toBe(0);expect(expired.proposed).toHaveLength(0)
})
test('affine-alias picks unconditionally select one kernel-valid representative',()=>{
 const z:E={op:'const',value:0},alias:E={op:'add',a:z,b:z},g:Goal={name:'pick alias',hyps:[{op:'<',a:z,b:z}]}
 const ds:CountDecl[]=[{map:'T',j:'j',key:'k',below:{op:'const',value:5},body:get('cells',x('k'))}]
 const full={reads:[['r0','T',z],['r1','T',alias]] as CountCert['reads'],insts:[] as CountCert['insts'],picks:[['r0',[z]],['r1',[alias]]] as [string,E[]][]}
 expect(full.picks).toHaveLength(2)
 expect(ids(full)[0]).toBe(ids(full)[1])
 const chosen=new Set(ids(full)),view=chosenView(full,chosen),cert=selectedCertificate(g,ds,view,stableState([g,ds]),false)
 expect(cert.picks).toHaveLength(1);expect(cert.insts).toHaveLength(0);expect(ids(cert)).toEqual([...chosen])
 const proof=grow(mcGoal(g.hyps,ds,cert)!,new Map(),{nodes:0,until:clock()+500})
 expect('tree' in proof).toBe(true);if('tree' in proof)expect(checkMC(g.hyps,ds,{...cert,tree:proof.tree})).toBe(true)
 const reordered=chosenView({...full,picks:[...full.picks].reverse(),reads:[...full.reads].reverse()},chosen)
 expect(ids(reordered)).toEqual(ids(view));expect(reordered.picks).toHaveLength(1)
})

function selectorV2Fixture(base=37,reverseRoots=false,reverseSources=false,reversePatterns=false){
 const n=(value:number):E=>({op:'const',value}),pack=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:base,a},b}),le=(a:E,b:E):C=>({op:'<=',a,b})
 const rootTerms=[[x('a'),x('b')],[x('c'),x('d')]],roots=rootTerms.map(([a,b])=>le(n(1),get('owned',pack(a!,b!))))
 const own:Law={name:'root pair',forall:'a',keys:['b','c','d'],holds:{op:'and',xs:reverseRoots?[...roots].reverse():roots}}
 const cells=[le(n(1),get('relay',pack(x('row'),x('left')))),le(n(1),get('relay',pack(x('row'),x('right'))))]
 const law:Law={name:'unique relay',forall:'row',keys:['left','right'],holds:{op:'or',xs:[same(x('left'),x('right')),not({op:'and',xs:reversePatterns?[...cells].reverse():cells})]}}
 const sourceKeys=[pack(x('otherRow'),x('otherValue')),pack(x('inputRow'),x('inputValue'))],reads=sourceKeys.map(key=>get('relay',key))
 const m:Machine={name:'two roots with unrelated source',params:[],inputs:['inputRow','inputValue','otherRow','otherValue'],state:{sample:n(0)},maps:{owned:0,relay:0},step:{maps:{owned:{key:sourceKeys[1]!,value:n(1)}},state:{sample:{op:'add',a:reads[reverseSources?1:0]!,b:reads[reverseSources?0:1]!}}}}
 const anchors=[[x('a#'),x('b')],[x('c'),x('d')]].map(([a,b])=>same(get('relay',pack(a!,b!)),n(1))),pre=reverseRoots?[...anchors].reverse():anchors
 return {m,own,law,pre,pack,writeKey:sourceKeys[1]!,sourceKeys}
}

test('per-law slots cover distinct real roots without symmetric or unrelated-value backfill',()=>{
 for(const base of [37,83])for(const reverseRoots of [false,true])for(const reverseSources of [false,true])for(const reversePatterns of [false,true]){
  const f=selectorV2Fixture(base,reverseRoots,reverseSources,reversePatterns),budget=candidateWork()
  const result=sparseReadInstances(f.m,[f.law,f.own],f.own,{}, {name:'root coverage',hyps:f.pre},{reads:[],insts:[]},4,undefined,[],new Set(),f.pre,budget)
  const emitted=result.added.filter(p=>p.law===f.law.name),tuples=emitted.map(p=>JSON.stringify(p.tuple))
  expect(emitted).toHaveLength(2)
  expect(tuples).toContain(JSON.stringify([x('a#'),x('b'),x('inputValue')]))
  expect(tuples).toContain(JSON.stringify([x('c'),x('d'),x('inputValue')]))
  expect(new Set(emitted.slice(0,2).map(p=>JSON.stringify(p.tuple[0]))).size).toBe(2)
  for(const e of emitted){
   const p=result.termProposals.find(p=>JSON.stringify(p.tuple)===JSON.stringify(e.tuple))!
   expect(p.rootLinked).toBe(true);expect(p.ownWriteKeyMatch).toBe(true);expect(p.sourceKind).toBe('read')
   expect(p.sourceRead).toEqual(['relay',f.writeKey]);expect(p.coherentReadMatch).toBe(false);expect(p.sourceKeyReconstructed).toBe(false)
   expect(p.ignoredCounterpartCoordinates).toHaveLength(1)
   expect(p.premise).toEqual(assumed([f.law],{[f.law.name]:p.tuple})[0]!)
   expect(p.premise).not.toEqual(same(p.ignoredCounterpartCoordinates[0]!.retained,p.ignoredCounterpartCoordinates[0]!.counterpart))
  }
  expect(result.summary.generationWork.exhausted).toBe(false);expect(result.summary.generationWork.limit).toBe(65536)
 }
})

test('v2 pattern reuse saves actual work only within the same bounded attempt',()=>{
 const f=selectorV2Fixture(),n=(value:number):E=>({op:'const',value})
 const unrelated:Law[]=Array.from({length:12},(_,i)=>({name:'unrelated'+i,forall:'row',keys:['left','right'],holds:{op:'and',xs:Array.from({length:12},(_,j)=>same(get('unused'+i,f.pack(x('row'),{op:'add',a:x('left'),b:n(j)})),x('right')))}}))
 const laws=[f.law,...unrelated],meter=candidateWork(),run=(b:ReturnType<typeof candidateWork>)=>remainingCoordinateProposals(f.m,laws,[],{reads:[],insts:[]},undefined,new Set(),f.pre,b.tick,f.own)
 const before=JSON.stringify(laws),first=run(meter),firstWork=meter.state.work,second=run(meter),secondWork=meter.state.work-firstWork
 expect(second).toEqual(first);expect(secondWork).toBeLessThan(firstWork);expect(meter.state.exhausted).toBe(false);expect(JSON.stringify(laws)).toBe(before)
 const independent=candidateWork();expect(run(independent)).toEqual(first);expect(independent.state.work).toBe(firstWork)
 const expired=withWall(performance.now()-1,()=>run(meter));expect(expired).toEqual([]);expect(meter.state.deadline).toBe(true)
 const exhausted=candidateWork();while(exhausted.tick()){};expect(run(exhausted)).toEqual([]);expect(exhausted.state.work).toBe(65536)
})

test('v2 no-POST pools skip only impossible narrow triples and retain one shared meter',()=>{
 const f=selectorV2Fixture(),budget=candidateWork(),prepared=prepareSupport(f.m,[f.own,f.law],f.own,{},1,budget),start=budget.state.work,n=(value:number):E=>({op:'const',value})
 const decls:CountDecl[]=Array.from({length:6},(_,i)=>({map:'T'+i,j:'outer',key:'cell',below:n(11),body:get('cells',{op:'add',a:x('outer'),b:x('cell')})}))
 const goal:Goal={name:'all PRE reads',hyps:decls.map(d=>same(get(d.map,x('root')),n(1)))},pool=grammarPool(goal,decls,1000,budget)
 expect(pool.base).toEqual(certFor(goal,decls,true,1000))
 const marks=budget.state.phases,base=marks.find(p=>p.phase==='pool:base')!,narrow=marks.find(p=>p.phase==='pool:narrow')!
 expect(base.work).toBe(narrow.work);expect(marks.find(p=>p.phase==='pool:begin')!.work).toBe(start)
 const selected=smallSelection(goal,decls,pool.full,[x('root')],{reads:[],picks:[]},budget)
 expect(selected.insts.length).toBeLessThanOrEqual(10);expect(budget.state.work).toBeGreaterThan(start);expect(budget.state.work).toBeLessThan(65536)
 expect(budget.state.phases.every((p,i,ps)=>i===0||p.work>=ps[i-1]!.work)).toBe(true)
 expect(budget.state.phases[0]!.phase).toBe('prepare:begin');expect(budget.state.phases.at(-1)!.phase).toBe('selection:end')
 expect(prepared.generationWork.phases.at(-1)!.phase).toBe('prepare:end')
})

function overlapSelectionFixture(prefix:string,base:number,reverse=false){
 const n=(value:number):E=>({op:'const',value}),add=(a:E,b:E):E=>({op:'add',a,b}),mul=(k:number,a:E):E=>({op:'mul',k,a}),pack=(a:E,b:E)=>add(mul(base,a),b),cell=x(prefix+'cell'),outer=prefix+'outer',low=prefix+'low',input=pack(x(prefix+'input'),x(prefix+'value'))
 const maps={plain:prefix+'plain',missing:prefix+'missing',column:prefix+'column',mirror:prefix+'mirror'},member=get(prefix+'member',cell),relation=(a:E,b:E)=>get(prefix+'relation',add(mul(base*base,cell),pack(a,b))),below=n(19)
 const ds:CountDecl[]=[{map:maps.plain,j:outer,key:prefix+'cell',below,body:member},{map:maps.missing,j:outer,key:prefix+'cell',below,body:{op:'if',c:{op:'and',xs:[same(member,n(1)),same(relation(x(prefix+'input'),x(prefix+'value')),n(0))]},then:n(1),else:n(0)}},...[maps.column,maps.mirror].map(map=>({map,j:outer,lo:low,base,key:prefix+'cell',below,body:map===maps.column?relation(x(outer),x(low)):{op:'if' as const,c:{op:'and' as const,xs:[same(get(prefix+'mark',add(cell,x(outer))),n(0)),same(relation(x(outer),x(low)),n(1))]},then:n(1),else:n(0)}}))]
 const keys=[pack(x(prefix+'left'),x(prefix+'leftValue')),pack(x(prefix+'right'),x(prefix+'rightValue')),input]
 const reads=[same(get(maps.plain,n(0)),n(0)),same(get(maps.missing,n(0)),n(0)),...keys.flatMap(k=>[same(get(maps.column,k),n(0)),same(get(maps.mirror,k),n(0))])]
 const g:Goal={name:prefix+'pair dominated',hyps:[...(reverse?[...reads].reverse():reads),not({op:'and',xs:[same(get(maps.missing,n(0)),n(0)),...keys.map(k=>same(get(prefix+'primitive',k),n(1)))]})]}
 const decls=reverse?[...ds].reverse():ds,pool=grammarPool(g,decls),full=reverse?{...pool.full,reads:[...pool.full.reads].reverse(),insts:[...pool.full.insts].reverse().map(i=>i.terms.length===3?{...i,terms:[...i.terms].reverse()}:i)}:pool.full
 return {n,maps,keys,g,ds:decls,pool,full}
}

test('v3 existing overlap and exact projection survive pair dominance with both root keys',()=>{
 for(const [prefix,base,reverse]of [['a_',13,false],['renamed_',29,true],['other_',7,false]] as const){
  const f=overlapSelectionFixture(prefix,base,reverse),before=JSON.stringify(f.full),meter=candidateWork(),pick=smallSelection(f.g,f.ds,f.full,f.keys,{reads:[],picks:[]},meter),byRead=new Map(f.full.reads.map(r=>[r[0],r])),semantic=(i:CountCert['insts'][number])=>instId(i,f.full.reads)
  expect(f.pool.added.filter(p=>p.reason==='definition-linked PRE triple')).toHaveLength(2)
  expect(pick.insts).toHaveLength(10);expect(new Set(pick.insts.map(semantic)).size).toBe(10)
  const coverage=pick.insts.slice(0,f.keys.length).map(i=>byRead.get(i.terms[0]![1])![2])
  expect(new Set(coverage.map(k=>JSON.stringify(k))).size).toBe(f.keys.length)
  for(const k of f.keys)expect(coverage).toContainEqual(k)
  const pair=pick.insts.find(i=>i.terms.length===2&&i.terms.every(([,id])=>[f.maps.plain,f.maps.missing].includes(byRead.get(id)![1]))&&byRead.get(i.terms[0]![1])![1]===f.maps.plain)
  expect(pair).toBeDefined()
  for(const added of f.pool.added)expect(pick.insts.map(semantic)).toContain(semantic(added.instance))
  const stable=selectedCertificate(f.g,f.ds,pick,stableState([f.g,f.ds]),false)
  expect(stable.reads.length).toBeLessThanOrEqual(30);expect(new Set(stable.insts.map(i=>i.wit)).size).toBe(10);expect(mcGoal(f.g.hyps,f.ds,stable)).toBeDefined()
  expect(JSON.stringify(f.full)).toBe(before);expect(meter.state.work).toBeLessThan(65536);expect(meter.state.exhausted).toBe(false)
 }
})

test('v3 first coverage of ten required root keys cannot be displaced by overlap triples',()=>{
 const f=overlapSelectionFixture('full_',17),keys=Array.from({length:10},(_,i)=>({op:'add',a:{op:'mul',k:17,a:x('key'+i)},b:x('value'+i)} as E)),reads:CountCert['reads']=[...f.full.reads],pairs:CountCert['insts']=[]
 for(const [j,key]of keys.entries()){
  const a='requiredA'+j,b='requiredB'+j;reads.push([a,f.maps.column,key],[b,f.maps.mirror,key]);pairs.push({wit:'required'+j,below:f.n(19),unit:0,terms:[[1,a],[-1,b]]})
 }
 const full={...f.full,reads,insts:[...pairs,...f.full.insts]},pick=smallSelection(f.g,f.ds,full,keys,{reads:[],picks:[]})
 expect(pick.insts).toEqual(pairs);expect(pick.insts).toHaveLength(10)
})

test('v3 irrelevant, wrong-bound, wrong-key and POST lifts do not outrank required differences',()=>{
 const f=overlapSelectionFixture('negative_',11),lift=f.pool.added.at(-1)!.instance,reads=new Map(f.full.reads.map(r=>[r[0],r])),extra=lift.terms.find(([,id])=>reads.get(id)![1]===f.maps.mirror)!
 const wrongKey=f.full.reads.find(r=>r[1]===f.maps.mirror&&JSON.stringify(r[2])===JSON.stringify(f.keys[0]))!
 for(const mode of ['bridge','bound','key','post','pair'] as const){
  const bad={...lift,wit:'badLift',below:mode==='bound'?f.n(20):lift.below,terms:mode==='key'?lift.terms.map(([k,id]):[number,string]=>[k,id===extra[1]?wrongKey[0]:id]):lift.terms}
  const ds=f.ds.map(d=>d.map===f.maps.mirror&&mode==='bridge'?{...d,body:get('unrelated',x('negative_cell'))}:d),full={...f.full,insts:[...f.full.insts.filter(i=>i.terms.length===2),bad]}
  if(mode==='post'){const row=full.reads.find(r=>r[0]===extra[1])!;full.reads=full.reads.map((r):CountCert['reads'][number]=>r===row?[r[0],r[1]+'#',r[2]]:r);ds.push({...ds.find(d=>d.map===f.maps.mirror)!,map:f.maps.mirror+'#'})}
  const g=mode==='pair'?{...f.g,hyps:[...f.g.hyps.slice(0,-1),not(same(get('unrelatedRoot',f.keys[0]!),f.n(1)))]}:f.g,pick=smallSelection(g,ds,full,f.keys,{reads:[],picks:[]})
  const baseline=smallSelection(g,ds,{...full,insts:full.insts.filter(i=>i.wit!=='badLift')},f.keys,{reads:[],picks:[]})
  expect(pick.insts.slice(0,baseline.insts.length)).toEqual(baseline.insts)
  if(baseline.insts.length===10)expect(pick.insts.some(i=>i.wit==='badLift')).toBe(false)
 }
})

test('v3 overlap priority retains exhausted/deadline refusal and the shared generation meter',()=>{
 const f=overlapSelectionFixture('budget_',23),meter=candidateWork();while(meter.tick()){}
 expect(smallSelection(f.g,f.ds,f.full,f.keys,{reads:[],picks:[]},meter).insts).toEqual([]);expect(meter.state.work).toBe(65536)
 const expired=candidateWork(),pick=withWall(performance.now()-1,()=>smallSelection(f.g,f.ds,f.full,f.keys,{reads:[],picks:[]},expired))
 expect(pick.insts).toEqual([]);expect(expired.state.deadline).toBe(true)
 const partial=candidateWork();partial.state.work=65530;smallSelection(f.g,f.ds,f.full,f.keys,{reads:[],picks:[]},partial)
 expect(partial.state.work).toBe(65536);expect(partial.state.exhausted).toBe(true)
})

test('count-pool invalidation follows only count-dependent flags, including quantified bodies and cycles',()=>{
 const n=(value:number):E=>({op:'const',value}),flag=(name:string):C=>({op:'flag',name})
 const m:Machine={name:'dependencies',params:[],inputs:[],state:{},counts:{total:{j:'unused',key:'cell',below:n(9),body:n(0)}},step:{flags:{direct:same(get('total',n(0)),n(0)),indirect:flag('direct'),primitive:{op:'all',key:'cell',c:same(get('cells',x('cell')),n(0))},quantified:{op:'all',key:'cell',c:same(get('total',x('cell')),n(0))},cycleA:flag('cycleB'),cycleB:flag('cycleA')}}}
 const laws:Law[]=[{name:'count law',holds:same(get('total',n(0)),n(0))},{name:'flag law',holds:flag('indirect')},{name:'primitive law',holds:flag('primitive')}]
 expect([...countedInstanceSources(m,laws)].sort()).toEqual(['?direct','?indirect','?quantified','count law','flag law'].sort())
})
test('seeded upper bound starts with nonincrease and one relevant overlap, not pool fillers',()=>{
 const n=(value:number):E=>({op:'const',value}),le=(a:E,b:E):C=>({op:'<=',a,b}),body=(map:string):E=>get(map,{op:'add',a:x('cell'),b:x('row')})
 const ds:CountDecl[]=[{map:'count',j:'row',key:'cell',below:n(9),body:body('votes')},{map:'count#',j:'row',key:'cell',below:n(9),body:body('votes#')},...['bound',...Array.from({length:14},(_,i)=>'noise'+i)].map(map=>({map,j:'unused',key:'cell',below:n(9),body:get(map+'Cells',x('cell'))}))]
 const goal:Goal={name:'upper bound',hyps:[le(n(0),get('count',x('a'))),...['bound',...Array.from({length:14},(_,i)=>'noise'+i)].map(map=>le(n(0),get(map,n(0)))),not(le(get('count#',x('a')),n(4)))]}
 const selected=polaritySelection(goal,ds,grammarPool(goal,ds),candidateWork(),new Set(['bound'])),reads=new Map(selected.pick.reads.map(r=>[r[0],r[1]]))
 expect(selected.record.initialPriorityOnly).toBe(true);expect(selected.pick.insts).toHaveLength(2)
 expect(selected.pick.insts.map(i=>i.terms.map(([co,id])=>[co,reads.get(id)]))).toContainEqual([[1,'count#'],[-1,'count']])
 expect(selected.pick.insts.some(i=>i.unit===-1&&i.terms.every(([,id])=>['bound','count'].includes(reads.get(id)!)))).toBe(true)
 expect(mcGoal(goal.hyps,ds,selected.pick)).toBeDefined()
})
test('selected affine remainder matching ignores unused pool reads and keeps the complete original law',()=>{
 const n=(value:number):E=>({op:'const',value}),plus=(a:E,b:E):E=>({op:'add',a,b}),times=(k:number,a:E):E=>({op:'mul',k,a})
 for(const radix of [17,64]){
  const def={j:'packed',key:'member',below:n(9),body:get('relation',plus(times(radix*radix,x('member')),x('packed')))}
  const m:Machine={name:'generic scan',params:[],inputs:[],state:{},maps:{relation:0},counts:{tally:def},step:{}}
  const own:Law={name:'root',holds:same(n(0),n(0))},law:Law={name:'guarded scan',forall:'node',keys:['tail'],holds:{op:'or',xs:[not({op:'<',a:x('node'),b:n(9)}),{op:'<=',a:n(0),b:get('relation',plus(times(radix*radix,x('node')),x('tail')))}]}}
  const tail=plus(times(radix,x('round')),x('value')),cert:Pick<CountCert,'reads'|'insts'>={reads:[['selected','tally',tail],...Array.from({length:100},(_,i):CountCert['reads'][number]=>['unused'+i,'tally',n(i)])],insts:[{wit:'currentWitness',below:n(9),terms:[[1,'selected']],unit:0}]}
  const found=completeReadMatches(m,[law],own,[{map:'tally',...def}],cert)
  expect(found).toHaveLength(1);expect(found[0]!.tuple).toEqual([x('currentWitness'),tail]);expect(found[0]!.source.kind).toBe('selected')
  expect(found[0]!.premise).toEqual(assumed([law],{[law.name]:found[0]!.tuple})[0]!)
  expect(completeReadMatches(m,[law],own,[{map:'tally',...def}],{...cert,insts:[{...cert.insts[0]!,terms:[[1,'missing']]}]})).toEqual([])
 }
})
test('keyless stored-copy bounds prioritize both retained and incoming counts',()=>{
 const n=(value:number):E=>({op:'const',value}),le=(a:E,b:E):C=>({op:'<=',a,b}),bit=(map:string):E=>({op:'if',c:le(n(1),get(map,x('cell'))),then:n(1),else:n(0)})
 const decl=(map:string,body:E):CountDecl=>({map,j:'unused',key:'cell',below:n(9),body})
 const ds=[decl('stored',bit('oldCells')),decl('stored#',{op:'if',c:same(x('copy'),n(1)),then:bit('incomingCells'),else:bit('oldCells')}),...Array.from({length:14},(_,i)=>decl('noise'+i,bit('unrelated'+i))),decl('incoming',bit('incomingCells'))]
 const goal:Goal={name:'stored bound',hyps:[same(get('stored',n(0)),n(5)),...Array.from({length:14},(_,i)=>le(n(0),get('noise'+i,n(0)))),same(get('incoming',n(0)),n(6)),not(le(n(3),get('stored#',x('arbitraryKey'))))]}
 const pool=grammarPool(goal,ds),selection=polaritySelection(goal,ds,pool),reads=new Map(selection.pick.reads.map(r=>[r[0],r[1]]))
 const edges=selection.pick.insts.slice(0,2).map(i=>i.terms.map(([sign,id])=>[sign,reads.get(id)]))
 expect(edges).toContainEqual([[1,'stored'],[-1,'stored#']]);expect(edges).toContainEqual([[1,'incoming'],[-1,'stored#']])
 expect(selection.pick.insts.length).toBeLessThanOrEqual(10);expect(mcGoal(goal.hyps,ds,selection.pick)).toBeDefined()
 const unrelated=ds.map(d=>d.map==='incoming'?{...d,body:bit('unrelatedIncoming')}:d),negative=polaritySelection(goal,unrelated,grammarPool(goal,unrelated))
 expect(negative.record.preferred.some(p=>p.reasons.some(r=>(r as {kind:string}).kind==='definition-linked source/post')&&p.instance.terms.some(([,id])=>reads.get(id)==='incoming'))).toBe(false)
})
test('semantic aliases select one live representative across PRE/POST and reordered keys',()=>{
 const k=(value:number):E=>({op:'const',value}),plus=(a:E,b:E):E=>({op:'add',a,b}),ds:CountDecl[]=['T','T#'].map(map=>({map,j:'j',key:'cell',below:k(5),body:get(map==='T'?'cells':'cells#',{op:'add',a:x('cell'),b:x('j')})}))
 const aliases=[x('key'),plus(k(0),x('key')),plus(x('key'),k(0)),plus(plus(x('key'),k(0)),k(0))]
 for(const post of [false,true]){
  const g:Goal={name:'alias selection',hyps:[{op:'<',a:k(0),b:k(0)},...aliases.map(key=>same(get('T',key),k(0))),...(post?aliases.map(key=>same(get('T#',key),k(0))):[])]}
  const pool=grammarPool(g,ds),pick=post?polaritySelection(g,ds,pool).pick:smallSelection(g,ds,pool.full,aliases,{reads:[],picks:[]})
  expect(new Set(ids(pick)).size).toBe(ids(pick).length)
  expect(pool.work.truncated).toBe(false);expect(pool.base).toEqual(certFor(g,ds,true,1000))
  expect(pool.base.reads.every(([id])=>id.startsWith('r$'))).toBe(true);expect(pool.base.insts.every(i=>i.wit.startsWith('w$'))).toBe(true)
  const chosen=new Set(ids(pick)),view=chosenView(pool.full,chosen),state=stableState([g,ds]),c=selectedCertificate(g,ds,view,state,false)
  expect(c.insts.length+c.picks.length).toBeLessThanOrEqual(10);expect(new Set(ids(c)).size).toBe(ids(c).length);expect(new Set(c.insts.map(i=>i.wit)).size).toBe(c.insts.length)
  const proof=grow(mcGoal(g.hyps,ds,c)!,new Map(),{nodes:0,until:clock()+500});expect('tree' in proof).toBe(true);if('tree' in proof)expect(checkMC(g.hyps,ds,{...c,tree:proof.tree})).toBe(true)
  const reversed={...pool.full,insts:[...pool.full.insts].reverse(),reads:[...pool.full.reads].reverse()},next=selectedCertificate(g,ds,chosenView(reversed,chosen),state,false)
  expect(next.insts.map(i=>[instId(i,next.reads),i.wit]).sort((a,b)=>JSON.stringify(a).localeCompare(JSON.stringify(b)))).toEqual(c.insts.map(i=>[instId(i,c.reads),i.wit]).sort((a,b)=>JSON.stringify(a).localeCompare(JSON.stringify(b))))
 }
})
