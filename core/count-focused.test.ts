import {expect,test} from 'bun:test'
import {all,any,atMost,get,ite,less,n,not,same,type E,type Machine,x} from './machine.ts'
import {type CountCert,type CountDecl} from '../kernel/kernel.ts'
import {countLawSeeds,countRowBridges,independentCountInstances,fieldLawBridges,focusCountCert,rowKeyNames} from './count-focused.ts'

test('focused comparisons follow carried sets and indicator bodies, not names',()=>{
  const member=x('member'), row=x('row'), cell=get('Members',row)
  const base={j:'row',key:'member',below:n(4)}, at=get('Members',x('requestRow'))
  const decls:CountDecl[]=[
    {...base,map:'ParcelTotal',body:ite({op:'<=',a:n(1),b:get('Parcel',member)},n(1),n(0))},
    {...base,map:'Viewed',body:at},
    {...base,map:'RowTotal',body:ite(same(cell,n(1)),n(1),n(0))},
    {...base,map:'Qualified',body:ite(all(same(cell,n(1)),less(get('Terms',member),n(3))),n(1),n(0))},
  ]
  const m:Machine={name:'renamed sets',params:[],inputs:['requestRow'],inputMaps:['Parcel'],state:{},maps:{Members:0,Terms:0},step:{}}
  const reads:CountCert['reads']=[['a','ParcelTotal',n(0)],['b','Viewed',n(0)],['c','RowTotal',x('requestRow')],['d','Qualified',x('requestRow')]]
  const ids=reads.map(([id])=>id), insts:CountCert['insts']=ids.flatMap(a=>ids.filter(b=>b!==a).map((b,i)=>({wit:`w${a}${i}`,below:n(4),terms:[[1,a],[-1,b]] as [number,string][],unit:0})))
  const full={reads,insts}, result=focusCountCert(m,decls,full)
  expect(result.insts.map(i=>i.terms.map(t=>t[1]).join(''))).toEqual(['ac','ad','bc','cb','db','dc'])
  expect(full.insts).toHaveLength(12)
  expect(result.reads).toBe(reads)
  expect(focusCountCert({...m,inputMaps:[]},decls,full).insts.map(i=>i.terms.map(t=>t[1]).join(''))).toEqual(['bc','cb','db','dc'])
})

test('algebraic selection reserves union bounds and their row identities within the same cap',()=>{
  const m:Machine={name:'late union',params:[],inputs:[],inputMaps:['Incoming'],state:{},maps:{Members:0},step:{}}
  const base={j:'row',key:'cell',below:n(4)},names=['Post#','Input','OutsideA','Both','OutsideB','SizeA','SizeB','Noise']
  const decls:CountDecl[]=names.map(map=>({...base,map,body:map==='Input'?get('Incoming',x('cell')):n(1)}))
  const reads:CountCert['reads']=names.map((map,i)=>[`r${i}`,map,n(0)])
  const make=(wit:string,terms:[number,string][]):CountCert['insts'][number]=>({wit,below:n(4),terms,unit:0})
  const noise=Array.from({length:20},(_,i)=>make(`noise${i}`,[[1,'r7'],[-1,'r5'],[-1,'r6']]))
  const identities=[make('partitionA',[[1,'r5'],[-1,'r2'],[-1,'r3']]),make('partitionB',[[1,'r6'],[-1,'r4'],[-1,'r3']]),make('requestPartition',[[1,'r1'],[-1,'r5'],[-1,'r6']])]
  const union=make('union',[[1,'r0'],[1,'r1'],[-1,'r2'],[-1,'r3'],[-1,'r4']])
  const full={reads,insts:[...noise,...identities,union]},selected=focusCountCert(m,decls,full,{algebraic:true,carried:'Incoming'})
  expect(selected.insts).toHaveLength(5)
  expect(selected.insts).toContain(union)
  for(const identity of identities)expect(selected.insts).toContain(identity)
  expect(full.insts).toHaveLength(24)
  expect(focusCountCert(m,decls,full).insts).toEqual([])
})

test('packed count coordinates are row keys but scalar comparison witnesses are not',()=>{
  const m:Machine={name:'row roles',params:[],inputs:[],state:{},maps:{Cells:0},counts:{Total:{j:'r',key:'k',below:n(4),body:n(1)}},step:{}}
  const holds=all(less(x('half'),get('Total',{op:'add',a:{op:'mul',k:64,a:x('left')},b:x('right')})),same(get('Cells',{op:'add',a:{op:'mul',k:64,a:x('left')},b:x('column')}),n(0)))
  expect([...rowKeyNames(m,{name:'roles',forall:'left',keys:['right','half','column'],holds})].sort()).toEqual(['left','right'])
})

test('equal Boolean views survive the narrow selector despite duplicated conjuncts',()=>{
  const m:Machine={name:'equivalent views',params:[],inputs:[],state:{},maps:{A:0,B:0},step:{}}
  const a=same(get('A',x('k')),n(1)),b=same(get('B',x('k')),n(1)),base={j:'row',key:'k',below:n(4)}
  const ds=[{...base,map:'Size',body:ite(a,n(1),n(0))},{...base,map:'Self',body:ite(all(a,a),n(1),n(0))},{...base,map:'Other',body:ite(all(a,b),n(1),n(0))}]
  const cert={reads:[['size','Size',n(0)],['self','Self',n(0)],['other','Other',n(0)]] as [string,string,ReturnType<typeof n>][],insts:[
    {wit:'same',below:n(4),unit:0,terms:[[1,'size'],[-1,'self']] as [number,string][]},
    {wit:'different',below:n(4),unit:0,terms:[[1,'size'],[-1,'other']] as [number,string][]},
  ]}
  expect(focusCountCert(m,ds,cert,{structural:false}).insts.map(i=>i.wit)).toEqual(['same'])
})

test('new count keys remain independent of certificate witnesses',()=>{
  const m:Machine={name:'independent counts',params:[],inputs:[],state:{},maps:{},counts:{Sum:{j:'r',key:'k',below:n(4),body:n(1)}},step:{}}
  const law={name:'bounded',forall:'row',keys:['half'],holds:less(x('half'),get('Sum',x('row')))}
  const before={bounded:[x('kept'),n(0)]},next={bounded:[...before.bounded,x('witness'),n(0),x('newRow'),x('witness')]}
  expect(independentCountInstances(m,[law],before,next,['witness'])).toEqual({bounded:[...before.bounded,x('newRow'),x('witness')]})
  expect(independentCountInstances(m,[law],before,{bounded:[...before.bounded,x('witness'),n(0)]},['witness'])).toBeUndefined()
  expect(before.bounded).toEqual([x('kept'),n(0)])
})

test('counted row bridges preserve half-cardinality witnesses',()=>{
  const m:Machine={name:'row bridges',params:[],inputs:['source'],state:{},maps:{},counts:{Total:{j:'r',key:'k',below:n(4),body:n(1)}},step:{}}
  const law={name:'overlap',forall:'a',keys:['b','halfA','halfB'],holds:less(x('halfA'),get('Total',{op:'add' as const,a:{op:'mul' as const,k:64,a:x('a')},b:x('b')}))}
  const own=[x('a#'),x('b'),x('halfA'),x('halfB')],at={overlap:own}
  const result=countRowBridges(m,law,at,own,[x('source')])
  expect(result.overlap).toEqual([...own,x('source'),x('b'),x('halfA'),x('halfB'),n(0),x('b'),x('halfA'),x('halfB'),x('a#'),x('source'),x('halfA'),x('halfB'),x('a#'),n(0),x('halfA'),x('halfB')])
  expect(countRowBridges(m,law,result,own,[x('source')])).toBe(result)
  expect(at.overlap).toBe(own)
})

test('targeted carried-set comparisons omit unrelated row reads',()=>{
  const m:Machine={name:'target rows',params:[],inputs:['other'],inputMaps:['Incoming'],state:{},maps:{Rows:0},step:{}}
  const base={j:'row',key:'cell',below:n(4)},decls:CountDecl[]=[{...base,map:'InputSize',body:get('Incoming',x('cell'))},{...base,map:'RowSize',body:get('Rows',{op:'add',a:{op:'mul',k:64,a:x('row')},b:x('cell')})}]
  const full:Pick<CountCert,'reads'|'insts'>={reads:[['s','InputSize',n(0)],['a','RowSize',x('wanted')],['b','RowSize',x('other')]],insts:[{wit:'w0',below:n(4),unit:0,terms:[[1,'s'],[-1,'a']]},{wit:'w1',below:n(4),unit:0,terms:[[1,'s'],[-1,'b']]}]}
  expect(focusCountCert(m,decls,full,{structural:false,targets:[x('wanted')]}).insts).toEqual([full.insts[0]!])
})

test('algebraic focus keeps equivalent pre-count views but not different rows',()=>{
  const at=(row:ReturnType<typeof x>)=>get('Cells',{op:'add',a:{op:'mul',k:64,a:row},b:x('cell')})
  const m:Machine={name:'equivalent views',params:[],inputs:['source'],state:{},maps:{Cells:0},step:{}},base={j:'row',key:'cell',below:n(4)}
  const decls:CountDecl[]=[{...base,map:'InputView',body:at(x('source'))},{...base,map:'RowView',body:at(x('row'))}]
  const instance={wit:'point',below:n(4),unit:0,terms:[[1,'input'],[-1,'row']] as [number,string][]},full:Pick<CountCert,'reads'|'insts'>={reads:[['input','InputView',n(0)],['row','RowView',x('source')]],insts:[instance]}
  expect(focusCountCert(m,decls,full,{structural:false,algebraic:true}).insts).toEqual([instance])
  expect(focusCountCert(m,decls,{...full,reads:[full.reads[0]!,['row','RowView',x('other')]]},{structural:false,algebraic:true}).insts).toEqual([])
})

test('a carried subset can target its declared input-keyed row view',()=>{
  const cell=x('cell'),key={op:'add' as const,a:{op:'mul' as const,k:64,a:x('source')},b:cell},body=get('Rows',key)
  const m:Machine={name:'input-keyed view',params:[],inputs:['source'],inputMaps:['Incoming'],state:{},maps:{Rows:0},step:{flags:{subset:{op:'all',key:'cell',c:any(not(same(get('Incoming',cell),n(1))),same(body,n(1)))}}}}
  const base={j:'unused',key:'cell',below:n(4)},decls:CountDecl[]=[{...base,map:'Carried',body:get('Incoming',cell)},{...base,map:'SourceSize',body}]
  const instance={wit:'point',below:n(4),unit:0,terms:[[1,'carried'],[-1,'view']] as [number,string][]},full:Pick<CountCert,'reads'|'insts'>={reads:[['carried','Carried',n(0)],['view','SourceSize',n(0)]],insts:[instance]}
  expect(focusCountCert(m,decls,full,{structural:false}).insts).toEqual([instance])
})

test('request frames propose only same-shaped carried-region comparisons',()=>{
  const m:Machine={name:'request frame',params:[],inputs:[],inputMaps:['Incoming'],state:{},maps:{Stored:0},step:{}}
  const base={j:'row',key:'cell',below:n(4)},decls:CountDecl[]=[{...base,map:'Size',body:get('Stored',x('cell'))},{...base,map:'Size#',body:get('Stored',x('cell'))},{...base,map:'ProposedSize',body:get('Incoming',x('cell'))}]
  const full:Pick<CountCert,'reads'|'insts'>={reads:[['old','Size',n(0)],['next','Size#',n(0)],['request','ProposedSize',n(0)]],insts:[]}
  expect(focusCountCert(m,decls,full,{structural:false}).insts).toEqual([])
  const insts=focusCountCert(m,decls,full,{structural:false,requestFrames:true}).insts
  expect(insts.map(i=>i.terms)).toEqual([[[1,'next'],[-1,'request']],[[1,'request'],[-1,'next']]])
  expect(insts.every(i=>i.unit===0&&i.wit&&i.below.op==='const')).toBe(true)
})

test('request frames normalize equality and threshold membership indicators',()=>{
  const m:Machine={name:'mixed indicators',params:[],inputs:[],inputMaps:['Incoming'],state:{},maps:{Stored:0},step:{}}
  const base={j:'row',key:'cell',below:n(4)},stored=ite(same(get('Stored',x('cell')),n(1)),n(1),n(0)),incoming=ite(atMost(n(1),get('Incoming',x('cell'))),n(1),n(0))
  const decls:CountDecl[]=[{...base,map:'Size',body:stored},{...base,map:'Size#',body:stored},{...base,map:'ProposedSize',body:incoming}]
  const full:Pick<CountCert,'reads'|'insts'>={reads:[['old','Size',n(0)],['next','Size#',n(0)],['request','ProposedSize',n(0)]],insts:[]}
  const insts=focusCountCert(m,decls,full,{structural:false,requestFrames:true}).insts
  expect(insts.map(i=>i.terms)).toEqual([[[1,'next'],[-1,'request']],[[1,'request'],[-1,'next']]])
})

test('frames retain a structural range bound between two post counts',()=>{
  const m:Machine={name:'post range',params:[],inputs:[],state:{},maps:{Members:0,Ready:0},step:{}}
  const a=same(get('Members',x('cell')),n(1)),b=same(get('Ready',x('cell')),n(1)),base={j:'row',key:'cell',below:n(4)}
  const decls:CountDecl[]=[{...base,map:'Small#',body:ite(all(a,b),n(1),n(0))},{...base,map:'Large#',body:ite(a,n(1),n(0))}]
  const forward={wit:'w0',below:n(4),unit:0,terms:[[1,'small'],[-1,'large']] as [number,string][]},back={...forward,wit:'w1',terms:[[1,'large'],[-1,'small']] as [number,string][]}
  const full:Pick<CountCert,'reads'|'insts'>={reads:[['small','Small#',n(0)],['large','Large#',n(0)]],insts:[forward,back]}
  expect(focusCountCert(m,decls,full,{structural:false}).insts).toEqual([])
  const selected=focusCountCert(m,decls,full,{structural:false,frames:true}).insts
  expect(selected).toContainEqual(forward)
  expect(selected).not.toContainEqual(back)
})

test('request partition identities outrank misleading triples within sixteen algebraic slots',()=>{
  const cell=x('cell'),a=same(get('Members',cell),n(1)),b=same(get('Incoming',cell),n(1)),base={j:'row',key:'cell',below:n(4)}
  const m:Machine={name:'partition priority',params:[],inputs:[],inputMaps:['Incoming','Quorum'],state:{},maps:{Members:0},step:{}}
  const bodies:Record<string,E>={X:ite(a,n(1),n(0)),S:get('Incoming',cell),Q:get('Quorum',cell),OutsideX:ite(all(a,not(b)),n(1),n(0)),Both:ite(all(a,b),n(1),n(0)),OutsideS:ite(all(b,not(a)),n(1),n(0))}
  for(let i=0;i<2;i++)bodies[`Alias${i}`]=bodies.X!
  for(let i=0;i<8;i++)bodies[`Post${i}#`]=n(1)
  for(let i=0;i<20;i++)bodies[`Bad${i}`]=bodies.OutsideX!
  const decls:CountDecl[]=Object.entries(bodies).map(([map,body])=>({...base,map,body}))
  const reads:CountCert['reads']=decls.map(d=>[d.map,d.map,n(0)]),make=(wit:string,terms:[number,string][])=>({wit,below:n(4),unit:0,terms})
  const unions=Array.from({length:8},(_,i)=>make(`union${i}`,[[1,`Post${i}#`],[1,'Q'],[-1,'OutsideX'],[-1,'Both'],[-1,'OutsideS']]))
  const falseTriples=Array.from({length:20},(_,i)=>make(`wrong${i}`,[[1,'S'],[-1,`Bad${i}`],[-1,'Both']]))
  const identities=[make('S+',[[1,'S'],[-1,'OutsideS'],[-1,'Both']]),make('S-',[[ -1,'S'],[1,'OutsideS'],[1,'Both']]),make('X+',[[1,'X'],[-1,'OutsideX'],[-1,'Both']]),make('X-',[[-1,'X'],[1,'OutsideX'],[1,'Both']]),...['Alias0','Alias1'].flatMap(id=>[make(`${id}+`,[[1,id],[-1,'OutsideX'],[-1,'Both']]),make(`${id}-`,[[-1,id],[1,'OutsideX'],[1,'Both']])])]
  const longer=[make('long+',[[1,'X'],[-1,'S'],[-1,'OutsideX'],[1,'OutsideS']]),make('long-',[[-1,'X'],[1,'S'],[1,'OutsideX'],[-1,'OutsideS']])]
  const selected=focusCountCert(m,decls,{reads,insts:[...unions,...falseTriples,...longer,...identities]},{structural:false,algebraic:true})
  expect(selected.insts).toHaveLength(16)
  for(const identity of identities)expect(selected.insts).toContainEqual(identity)
  for(const identity of longer)expect(selected.insts).not.toContainEqual(identity)
})

test('post remainder and carried set propose a three-term coverage certificate',()=>{
  const m:Machine={name:'complement cover',params:[],inputs:[],inputMaps:['Voters'],state:{},maps:{A:0},step:{}}
  const a=same(get('A',x('k')),n(1)),base={j:'row',key:'k',below:n(4)}
  const ds=[{...base,map:'Size',body:ite(a,n(1),n(0))},{...base,map:'Selected',body:get('Voters',x('k'))},{...base,map:'Remaining#',body:ite(a,n(1),n(0))}]
  const full:Pick<CountCert,'reads'|'insts'>={reads:[['size','Size',n(0)],['selected','Selected',n(0)],['left','Remaining#',n(0)]],insts:[{wit:'coverage',below:n(4),unit:0,terms:[[1,'left'],[1,'selected'],[-1,'size']]}]}
  expect(focusCountCert(m,ds,full,{structural:false}).insts).toEqual([])
  expect(focusCountCert(m,ds,full,{structural:false,frames:true}).insts).toContainEqual(full.insts[0]!)
})

test('post counts can propose a bound from the stored membership they read',()=>{
  const m:Machine={name:'post subset',params:[],inputs:[],state:{},maps:{A:0,V:0},step:{}}
  const a=same(get('A',x('k')),n(1)),v=same(get('V',x('k')),n(1)),base={j:'row',key:'k',below:n(4)}
  const ds=[{...base,map:'Size',body:ite(a,n(1),n(0))},{...base,map:'Active#',body:ite(same(x('mode'),n(1)),n(1),ite(all(a,v),n(1),n(0)))}]
  const full:Pick<CountCert,'reads'|'insts'>={reads:[['size','Size',n(0)],['active','Active#',n(0)]],insts:[{wit:'subset',below:n(4),unit:0,terms:[[1,'active'],[-1,'size']]}]}
  expect(focusCountCert(m,ds,full,{structural:false}).insts).toEqual([])
  const focused=focusCountCert(m,ds,full,{structural:false,frames:true})
  expect(focused.insts).toContainEqual(full.insts[0]!)
  expect(focused.insts[0]).toEqual(full.insts[0]!)
  const filtered=[{...ds[0]!,body:ite(all(a,v),n(1),n(0))},ds[1]!]
  expect(focusCountCert(m,filtered,full,{structural:false}).insts).toEqual([])
  expect(focusCountCert(m,filtered,full,{structural:false,frames:true}).insts).toContainEqual(full.insts[0]!)
})

test('post-state frame comparisons are opt-in witness-bearing proposals',()=>{
  const m:Machine={name:'frames',params:[],inputs:[],state:{'frame$0':n(0)},maps:{Cells:0},step:{}}
  const decls:CountDecl[]=[{map:'Total',j:'row',key:'k',below:n(4),body:get('Cells',x('k'))},{map:'Total#',j:'row',key:'k',below:n(4),body:get('Cells',x('k'))}]
  const full:Pick<CountCert,'reads'|'insts'>={reads:[['before','Total',n(0)],['after','Total#',n(0)]],insts:[]}
  expect(focusCountCert(m,decls,full).insts).toEqual([])
  const framed=focusCountCert(m,decls,full,{frames:true})
  expect(framed.insts.map(i=>i.terms)).toEqual([[[1,'after']],[[1,'after'],[-1,'before']],[[1,'before'],[-1,'after']]])
  expect(new Set(framed.insts.map(i=>i.wit)).size).toBe(3)
  expect(framed.insts.some(i=>i.wit==='frame$0')).toBe(false)
  expect(full.insts).toEqual([])
})

test('field bridges preserve the goal column independently of row-key aliases',()=>{
  const m:Machine={name:'renamed rows',params:[],inputs:[],state:{},maps:{Rows:0},counts:{Total:{j:'a',key:'k',below:n(4),body:n(1)}},step:{}}
  const laws=[{name:'row',forall:'a',keys:['b','column'],holds:same(x('a'),x('b'))},{name:'count',forall:'a',keys:['b'],holds:same(get('Total',x('a')),n(0))}]
  const own=[x('left'),x('right')],request=[x('sender')],column=x('cell'),at={}
  const next=fieldLawBridges(m,laws,at,own,request,column)
  expect(next.row!.slice(0,3)).toEqual([own[0]!,request[0]!,column])
  expect(next.row!.slice(6,9)).toEqual([own[0]!,n(0),column])
  expect(next.row).toHaveLength(24)
  expect(next.count).toBeUndefined()
  expect(at).toEqual({})
  expect(fieldLawBridges(m,laws,next,own,request,column)).toBe(next)
  expect(fieldLawBridges(m,laws,at,own,request).row).toBeUndefined()
})

test('count-law bridges seed only unary/binary count laws and preserve input',()=>{
  const c={j:'a',key:'k',below:n(4),body:n(1)}, m:Machine={name:'bridge',params:[],inputs:[],state:{},maps:{},counts:{Count:c},step:{}}
  const body=same(get('Count',x('a')),n(1)), laws=[
    {name:'one',forall:'a',keys:[],holds:body},
    {name:'two',forall:'a',keys:['b'],holds:body},
    {name:'three',forall:'a',keys:['b','c'],holds:body},
    {name:'field',forall:'a',holds:same(x('a'),n(1))},
  ], at={}, own=[x('left'),x('right')], request=[x('input')]
  const seeded=countLawSeeds(m,laws,at,own,request)
  expect(seeded.one).toEqual([...own,...request])
  expect(seeded.two).toEqual([own[0]!,request[0]!,request[0]!,own[0]!,own[1]!,request[0]!,request[0]!,own[1]!])
  expect(seeded.three).toBeUndefined()
  expect(seeded.field).toBeUndefined()
  expect(at).toEqual({})
  expect(countLawSeeds(m,laws,seeded,own,request)).toBe(seeded)
  expect(countLawSeeds(m,laws,{},own,request,true).two).toEqual([request[0]!,own[0]!,request[0]!,own[1]!])
})
