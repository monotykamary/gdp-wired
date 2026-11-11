import {expect,spyOn,test} from 'bun:test'
import {type C,type E,type Machine,all,any,atMost,evalC,evalE,get,ite,less,minus,n,not,plus,same,times,walkOnce,x} from './machine.ts'
import {quorumLaws,quorumLawProvenance} from './quorum-laws.ts'
import {discoverLiftedCountGuard,discoverLiftedCountOperations,discoverLiftedCountOperation} from './count-lifted-shape.ts'
import {proveLiftedCountComposition,proveLiftedCountFrame,proveLiftedCountInitial} from './count-lifted-strategy.ts'
import {composeCountOperationProofs,type FixedOperationProof} from './count-case-compose.ts'
import {discoverLiftedCountPrerequisites,liftedCountBodySize} from './count-lifted-prerequisite.ts'
import {certFor} from './counts.ts'
import {check,checkMC,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,counted,fullRate,grow,inBudget,withBudget} from '../kernel/prove.ts'
import {coreMeter} from './meter.ts'
const bit = (c: C) => ite(c, n(1), n(0))
const fixture = (base = 8): Machine => {
  const cell = (r: E, k: E) => same(get('Rows', plus(times(base, r), k)), n(1)), member = (k: E) => atMost(n(1), get('Proposal', k))
  const cnt = (body: (k: E) => C) => ({j: 'j', key: 'k', below: x('size'), body: bit(body(x('k')))})
  const read = (name: string) => get(name, n(0))
  return {name: 'row-election fixture', params: ['size'], inputs: ['row', 'left', 'right'], state: {}, maps: {Rows: 0, Epoch: 0, Written: 0, Version: 0}, inputMaps: ['Proposal'],
    counts: {rowCount: cnt(k => cell(x('row'), k)), members: cnt(member), diff: cnt(k => all(cell(x('row'), k), not(member(k)))), reverse: cnt(k => all(member(k), not(cell(x('row'), k)))), meet: cnt(k => all(cell(x('row'), k), member(k)))},
    assume: all(less(x('row'), x('size')), less(read('rowCount'), times(2, read('members'))), atMost(times(2, x('left')), read('rowCount')), less(read('rowCount'), plus(times(2, x('left')), n(2))), atMost(times(2, x('right')), read('members')), less(read('members'), plus(times(2, x('right')), n(2)))),
    step: {flags: {
      eligible: {op: 'all', key: 'voter', c: any(not(member(x('voter'))), all(less(get('Epoch', x('voter')), plus(get('Epoch', x('row')), n(1))), atMost(get('Version', x('voter')), get('Version', x('row')))))},
      elect: {op: 'flag', name: 'eligible'},
      change: less(read('meet'), plus(minus(plus(x('left'), n(1)), read('diff')), minus(plus(x('right'), n(1)), read('reverse')))),
    }, maps: {
      Written: {each: 'z', value: ite(all({op: 'flag', name: 'elect'}, same(x('z'), x('row'))), plus(get('Epoch', x('row')), n(1)), get('Written', x('z')))},
      Rows: {each: 'z', value: ite(all({op: 'flag', name: 'change'}, atMost(times(base, x('row')), x('z')), less(x('z'), plus(times(base, x('row')), n(base)))), bit(member(minus(x('z'), times(base, x('row'))))), get('Rows', x('z')))},
    }},
  }
}
const generated=()=>{
 const original=fixture(),g=quorumLaws(original,true),m={...original,counts:{...original.counts,...g.counts}}
 const law=g.laws.find(l=>quorumLawProvenance(l)?.disabled)!
 return {original,m,g,law}
}
test('provenance is opt-in without changing generated formulas or the disabled meter path',()=>{
 const m=fixture(),start=coreMeter.astNodes,plain=quorumLaws(m,false),middle=coreMeter.astNodes,again=quorumLaws(m,false),end=coreMeter.astNodes
 expect(end-middle).toBe(middle-start);expect(again).toEqual(plain)
 expect(plain.laws.every(law=>quorumLawProvenance(law)===undefined)).toBe(true)
 const tagged=quorumLaws(m,true);expect(tagged).toEqual(plain)
 expect(tagged.laws.some(law=>quorumLawProvenance(law)!==undefined)).toBe(true)
})
test('lifted discovery follows candidate provenance without serialised changes',()=>{
 const {m,g,law}=generated(),before=JSON.stringify(law),shape=discoverLiftedCountGuard(m,law,g.laws)
 expect(shape).toBeDefined();expect(shape?.origin.halves).toHaveLength(2);expect(shape?.countMaps.length).toBeGreaterThanOrEqual(3)
 expect(JSON.stringify(law)).toBe(before);expect(discoverLiftedCountOperations(m,shape!)).toBeUndefined()
 law.name='arbitrary candidate';m.name='unrelated renamed system'
 expect(discoverLiftedCountGuard(m,law,g.laws)).toBeDefined()
})
test('untagged, changed and non-disabling candidates decline cleanly',()=>{
 const {m,g,law}=generated()
 expect(discoverLiftedCountGuard(m,{...law},g.laws)).toBeUndefined()
 const plain=g.laws.find(l=>quorumLawProvenance(l)?.disabled===false)!
 expect(discoverLiftedCountGuard(m,plain,g.laws)).toBeUndefined()
 law.holds=all(law.holds,same(x('forged'),n(1)))
 expect(quorumLawProvenance(law)).toBeUndefined();expect(discoverLiftedCountGuard(m,law,g.laws)).toBeUndefined()
})
test('changed count definitions cannot reuse stale lifted provenance',()=>{
 const {m,g,law}=generated(),origin=quorumLawProvenance(law)!
 m.counts![origin.rowCount]={...m.counts![origin.rowCount]!,body:n(1)}
 expect(discoverLiftedCountGuard(m,law,g.laws)).toBeUndefined()
})
test('frame-only lifted cases compose and check the original INIT and STEP',()=>counted(fullRate,()=>{
 const {m,g,law}=generated();m.inputs.push('operation')
 m.pre=all(atMost(n(1),x('size')),atMost(x('size'),n(8)))
 m.assume=all(m.assume!,atMost(n(11),x('operation')),less(x('operation'),n(14)),any(...[11,12,13].map(value=>same(x('operation'),n(value)))))
 m.step={...m.step,maps:{}}
 const request:Parameters<typeof proveLiftedCountComposition>[4]=(goal,decls)=>certFor(goal,decls,false,0,()=>true)
 const events:Record<string,unknown>[]=[]
 const proof=proveLiftedCountComposition(m,g.laws,law,clock()+2000,request,event=>events.push(event))
 if(!proof)console.error('LIFTED_CASE_EVENTS '+JSON.stringify(events))
 expect(proof).toBeDefined()
 if(!proof)return
 expect(proof.premises).toEqual([law.name])
 for(const packet of countedObligations(m,g.laws,{[law.name]:proof.instances},g.laws.indexOf(law))){
  expect(proof.certs[packet.goal.name]).toBeDefined()
  expect(checkMC(packet.goal.hyps,packet.decls,proof.certs[packet.goal.name]!)).toBe(true)
 }
 const again=proveLiftedCountComposition(m,g.laws,law,clock()+2000,request)
 expect(again).toEqual(proof)
},true))
test('lifted discovery, exhaustive composition and native replay inherit a clock-free scope',()=>{
 const mock=spyOn(performance,'now').mockImplementation(()=>{throw Error('lifted path read raw wall clock')})
 try{
  for(const observed of [false,true])withBudget(2000*fullRate,()=>{
   const {m,g,law}=generated();m.inputs.push('operation')
   m.pre=all(atMost(n(1),x('size')),atMost(x('size'),n(8)))
   m.assume=all(m.assume!,atMost(n(11),x('operation')),less(x('operation'),n(14)),any(...[11,12,13].map(value=>same(x('operation'),n(value)))))
   m.step={...m.step,maps:{}}
   const events:Record<string,unknown>[]=[]
   const proof=proveLiftedCountComposition(m,g.laws,law,clock()+2000,(goal,decls)=>certFor(goal,decls,false,0,()=>true),observed?event=>events.push(event):undefined)
   expect(proof).toBeDefined();if(!proof)return
   if(observed)expect(events.filter(event=>'wallMs'in event).every(event=>event.wallMs===0)).toBe(true)
   expect(proof.premises).toEqual([law.name])
   for(const packet of countedObligations(m,g.laws,{[law.name]:proof.instances},g.laws.indexOf(law)))expect(checkMC(packet.goal.hyps,packet.decls,proof.certs[packet.goal.name]!)).toBe(true)
  })
  expect(inBudget()).toBe(false)
 }finally{mock.mockRestore()}
})

const withoutVersionBump=()=>{
 const original=fixture();original.inputs.push('operation')
 original.assume=all(original.assume!,any(same(x('operation'),n(2)),same(x('operation'),n(7)),same(x('operation'),n(11))))
 original.step.flags!.elect=all(same(x('operation'),n(2)),original.step.flags!.elect!)
 original.step.flags!.change=all(same(x('operation'),n(7)),original.step.flags!.change!)
 const g=quorumLaws(original,true),m={...original,counts:{...original.counts,...g.counts}},law=g.laws.find(candidate=>quorumLawProvenance(candidate)?.disabled)!
 return {m,g,law}
}
test('provenance selects a renamed replacement that does not bump a version field',()=>{
 const {m,g,law}=withoutVersionBump(),shape=discoverLiftedCountGuard(m,law,g.laws)!
 const events:Record<string,unknown>[]=[]
 const plan=discoverLiftedCountOperations(m,shape,event=>events.push(event))
 if(!plan)console.error('F10_DECLINE '+JSON.stringify(events))
 expect(plan).toBeDefined()
 const replacement=plan?.find(operation=>operation.value===7)
 expect(replacement?.kind).toBe('threshold-replace')
 expect(replacement&&'replacement'in replacement?replacement.replacement:undefined).toEqual({guard:'change',input:'Proposal'})
 expect(replacement&&'write'in replacement?replacement.write:undefined).toBeUndefined()
})
test('fixed-case discovery does not reclassify contradictory unrelated operations',()=>{
 const {m,g,law}=withoutVersionBump(),shape=discoverLiftedCountGuard(m,law,g.laws)!
 m.assume=all(m.assume!,same(x('operation'),n(11)))
 expect(discoverLiftedCountOperations(m,shape)).toBeUndefined()
 expect(discoverLiftedCountOperation(m,shape,11)?.kind).toBe('frame-or-phase')
 expect(discoverLiftedCountOperation(m,shape,99)).toBeUndefined()
})
test('a carried-row write outside the provenance action declines with both classifications',()=>{
 const {m,g,law}=withoutVersionBump(),shape=discoverLiftedCountGuard(m,law,g.laws)!
 const row=m.step.maps!.Rows!
 if(!('each'in row)||row.value.op!=='if')throw Error('fixture row write')
 row.value={...row.value,c:all({op:'flag',name:'elect'},atMost(times(8,x('row')),x('z')),less(x('z'),plus(times(8,x('row')),n(8))))}
 const events:Record<string,unknown>[]=[]
 expect(discoverLiftedCountOperations(m,shape,event=>events.push(event))).toBeUndefined()
 expect(events[0]?.reason).toBe('replacement-write-disagreement')
 expect(events[0]?.replacement).toBe(7)
 expect(events[0]?.value).toBe(2)
 expect(events[0]?.kind).toBe('replacement')
})
test('marked row agreement is preferred without dropping an unmarked alternative',()=>{
 const {m,g,law}=generated(),u=x('u'),v=x('v'),column=x('column')
 for(const field of ['Epoch','Version'])m.step.maps![field]={each:'z',value:ite({op:'flag',name:'change'},get(field,x('row')),get(field,x('z')))}
 const row=(r:E)=>get('Rows',plus(times(8,r),column)),guard=all(less(u,x('size')),less(v,x('size')),less(column,x('size')),same(get('Epoch',u),get('Epoch',v)),same(get('Version',u),get('Version',v)))
 const plain={name:'unmarked alternative',forall:'u',keys:['v','column'],holds:any(not(guard),same(row(u),row(v)))},marked={...plain,name:'marked preferred',holds:any(not(all(guard,same(get('Written',u),n(1)),same(get('Written',v),n(1)))),same(row(u),row(v)))}
 const shape=discoverLiftedCountGuard(m,law,[...g.laws,plain,marked])
 expect(shape?.rowAgreements.map(row=>row.law)).toEqual([marked,plain])
 expect(shape?.rowAgreement?.markers).toEqual([{map:'Written',value:1}])
})
test('a stored-guard-shaped clone reports lost provenance instead of silently guessing',()=>{
 const {m,g,law}=generated(),events:Record<string,unknown>[]=[]
 expect(discoverLiftedCountGuard(m,{...law},g.laws,event=>events.push(event))).toBeUndefined()
 expect(events).toEqual([{stage:'lifted-decline',reason:'no provenance',message:'lifted-decline: no provenance'}])
 events.length=0
 expect(discoverLiftedCountGuard(m,law,g.laws,event=>events.push(event))).toBeDefined()
 expect(events).toEqual([])
})

test('F15 discovers a guarded disabling factor without law or map names',()=>{
 const {m,g,law}=generated(),matches=discoverLiftedCountPrerequisites(m,law,g.laws)
 expect(matches.some(match=>match.kind==='threshold-factor')).toBe(true)
 expect(matches.every(match=>g.laws.includes(match.law))).toBe(true)
 for(const match of matches)expect(liftedCountBodySize(match.disabled.body)).toBe(liftedCountBodySize(JSON.parse(JSON.stringify(match.disabled.body))))
 for(const [i,candidate]of g.laws.entries())candidate.name='renamed '+i
 m.name='a different fixture name'
 expect(discoverLiftedCountPrerequisites(m,law,g.laws).map(match=>match.voteMap)).toEqual(matches.map(match=>match.voteMap))
 expect(discoverLiftedCountPrerequisites(m,{...law},g.laws)).toEqual([])
 const offered=g.laws.filter(candidate=>!matches.some(match=>match.law===candidate))
 expect(discoverLiftedCountPrerequisites(m,law,offered)).toEqual([])
})
test('F15 guarded factors replay natively but are not unconditional count identities',()=>counted(fullRate,()=>{
 const {m,g,law}=generated(),match=discoverLiftedCountPrerequisites(m,law,g.laws).find(match=>match.kind==='threshold-factor')!
 expect(match).toBeDefined();if(!match?.threshold)return
 const mismatch=not(same(match.disabled.body,match.votes.body)),goal={name:'guarded factor',hyps:[match.threshold,mismatch]}
 const proof=grow(goal,new Map(),{nodes:0,until:clock()+500})
 expect('tree'in proof).toBe(true)
 if('tree'in proof){expect(check(goal,proof.tree)).toBe(true);expect(check({name:'unguarded factor',hyps:[mismatch]},proof.tree)).toBe(false)}
 const unguarded=grow({name:'unguarded factor',hyps:[mismatch]},new Map(),{nodes:0,until:clock()+500})
 expect('stuck'in unguarded?unguarded.stuck:'proven').toBe('sat')
 const vars:Record<string,number>={},membership=discoverLiftedCountGuard(m,law,g.laws)!.origin.membershipMap
 for(const body of [match.disabled.body,match.votes.body])walkOnce(body,node=>{if('op'in node&&node.op==='var'&&'name'in node&&typeof node.name==='string')vars[node.name]=0})
 const state={scalars:{},maps:Object.fromEntries(Object.keys(m.maps??{}).map(name=>[name,new Map([[0,name===membership?1:0]])]))}
 expect(evalC(match.threshold,vars,state,m)).toBe(false)
 expect(evalE(match.disabled.body,vars,state,m)).toBe(1);expect(evalE(match.votes.body,vars,state,m)).toBe(0)
},true))

test('W-relative frame composition preserves its smaller absolute parent and native acceptance',()=>withBudget(1_000_000_000,()=>{
 const {m,g,law}=generated(),W=4_000_000
 m.pre=all(atMost(n(1),x('size')),atMost(x('size'),n(8)))
 m.inputs.push('operation');m.assume=all(m.assume!,any(...[11,12,13].map(value=>same(x('operation'),n(value)))));m.step={...m.step,maps:{}}
 const until=clock()+50_000,proof=proveLiftedCountComposition(m,g.laws,law,until,(goal,decls)=>certFor(goal,decls,false,0,()=>true),undefined,W)
 expect(proof).toBeDefined();if(!proof)return
 expect(clock()).toBeLessThan(until)
 const packets=countedObligations(m,g.laws,{[law.name]:proof.instances},g.laws.indexOf(law))
 expect(packets).toHaveLength(2)
 for(const packet of packets){const cert=proof.certs[packet.goal.name]!;expect(checkMC(packet.goal.hyps,packet.decls,cert)).toBe(true)}
 expect(packets.some(packet=>!checkMC(packet.goal.hyps,packet.decls,{...proof.certs[packet.goal.name]!,tree:{leaf:[]}}))).toBe(true)
}))

test('frame composition records implicit scalar family assumptions',()=>counted(fullRate,()=>{
 const {m,g,law}=generated(),scalar={name:'scalar premise',holds:same(n(0),n(0))},family=[...g.laws,scalar]
 m.pre=all(atMost(n(1),x('size')),atMost(x('size'),n(8)))
 m.inputs.push('operation');m.assume=all(m.assume!,any(...[11,12,13].map(value=>same(x('operation'),n(value)))));m.step={...m.step,maps:{}}
 const proof=proveLiftedCountComposition(m,family,law,clock()+2000,(goal,decls)=>certFor(goal,decls,false,0,()=>true))
 expect(proof).toBeDefined();if(!proof)return
 expect(proof.instances[scalar.name]).toBeUndefined();expect(proof.premises).toContain(scalar.name)
 for(const packet of countedObligations(m,family,{[law.name]:proof.instances},family.indexOf(law)))expect(checkMC(packet.goal.hyps,packet.decls,proof.certs[packet.goal.name]!)).toBe(true)
},true))
test('composition refutes an excluded case and does not certify the unrestricted machine',()=>counted(fullRate,()=>{
 const {m,g,law}=generated();m.inputs.push('operation')
 m.pre=all(atMost(n(1),x('size')),atMost(x('size'),n(8)))
 m.assume=all(m.assume!,any(...[11,12,13].map(value=>same(x('operation'),n(value)))));m.step={...m.step,maps:{}}
 const restricted={...m,assume:all(m.assume,not(same(x('operation'),n(12))))},until=clock()+2000,shape=discoverLiftedCountGuard(restricted,law,g.laws)!
 const request:Parameters<typeof proveLiftedCountFrame>[4]=(goal,decls)=>certFor(goal,decls,false,0,()=>true),cases:FixedOperationProof[]=[]
 for(const value of [11,12,13]){
  const fixed={...restricted,assume:all(restricted.assume,same(x('operation'),n(value)))}
  if(value!==12){const proof=proveLiftedCountFrame(fixed,g.laws,law,until,request);expect(proof).toBeDefined();if(!proof)return;cases.push({value,proof});continue}
  const packet=countedObligations(fixed,g.laws,{[law.name]:{}},g.laws.indexOf(law)).at(-1)!,base={reads:[],insts:[],picks:[]},goal=mcGoal(packet.goal.hyps,packet.decls,base)!
  const result=grow(goal,new Map(),{nodes:0,until});expect('tree'in result).toBe(true);if(!('tree'in result))return
  const cert={...base,tree:result.tree};expect(checkMC(packet.goal.hyps,packet.decls,cert)).toBe(true)
  cases.push({value,proof:{instances:{},certs:{[packet.goal.name]:cert}}})
 }
 const initial=proveLiftedCountInitial(restricted,g.laws,law,cases[0]!.proof.instances,until,request);expect(initial).toBeDefined();if(!initial)return
 const context={original:m,machine:restricted,shape:shape.countShape,restrictions:[],inputCounts:{}},events:Record<string,unknown>[]=[]
 const control=composeCountOperationProofs(context,g.laws,law,cases,until,request,undefined,{initial})
 const mock=spyOn(performance,'now').mockImplementation(()=>{throw Error('composer trace read raw wall clock')})
 let proof:ReturnType<typeof composeCountOperationProofs>
 try{proof=withBudget(2000*fullRate,()=>composeCountOperationProofs(context,g.laws,law,cases,until,request,undefined,{initial,trace:event=>events.push(event)}))}finally{mock.mockRestore()}
 expect(proof).toEqual(control)
 // K3 also emits tail-ledger records; preserve F's exact native-stage projection.
 const nativeEvents=events.filter(event=>String(event.stage).startsWith('compose-'))
 expect(nativeEvents.map(event=>event.stage)).toEqual(['compose-reindex','compose-native-step','compose-native-initial'])
 expect(events.every(event=>typeof event.wallMs==='number'&&event.wallMs>=0&&typeof event.units==='number')).toBe(true)
 expect(nativeEvents.filter(event=>event.stage!=='compose-reindex').every(event=>event.checked===true)).toBe(true)
 expect(proof).toBeDefined();if(!proof)return
 for(const packet of countedObligations(restricted,g.laws,{[law.name]:proof.instances},g.laws.indexOf(law)))expect(checkMC(packet.goal.hyps,packet.decls,proof.certs[packet.goal.name]!)).toBe(true)
 const originalStep=countedObligations(m,g.laws,{[law.name]:proof.instances},g.laws.indexOf(law)).at(-1)!
 expect(checkMC(originalStep.goal.hyps,originalStep.decls,proof.certs[originalStep.goal.name]!)).toBe(false)
},true))
