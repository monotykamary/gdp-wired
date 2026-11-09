import {mkdirSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {type C,type E,type Machine,type Law,interpret,evalC} from '../../core/machine.ts'
import {type CountCert,checkCountedLaws,countedObligations,checkMC,mcGoal} from '../../kernel/kernel.ts'
import {grow,withWall} from '../../kernel/prove.ts'
import {cmachineToLean} from '../../lean-kernel/emit.ts'
const dir='/tmp/paxos-law12-probe-v2/';mkdirSync(dir,{recursive:true})
const k=(value:number):E=>({op:'const',value}),v=(name:string):E=>({op:'var',name}),get=(map:string,name:string):E=>({op:'get',map,key:v(name)})
const le=(a:E,b:E):C=>({op:'<=',a,b}),eq=(a:E,b:E):C=>({op:'=',a,b})
const sha=(s:string)=>createHash('sha256').update(s).digest('hex')
const make=(binder:string):Machine=>({name:'law12 synthetic copy',params:[],inputs:[],state:{},maps:{B:0},inputMaps:['Q'],step:{flags:{good:{op:'all',key:binder,c:le(get('Q',binder),k(1))}},maps:{B:{each:'copyKey',value:{op:'if',c:{op:'flag',name:'good'},then:get('Q','copyKey'),else:k(0)}}}}})
const laws:Record<string,Law>={bounded:{name:'audit',forall:'a',keys:['g'],holds:{op:'and',xs:[le(get('B','a'),k(1)),le(get('B','g'),k(1))]}},zero:{name:'audit',forall:'a',keys:['g'],holds:{op:'and',xs:[eq(get('B','a'),k(0)),eq(get('B','g'),k(0))]}},uniform:{name:'audit',forall:'a',keys:['g'],holds:eq(get('B','a'),get('B','g'))}}
const strategies:Record<string,E[]>={none:[],primary:[v('a#')],further:[v('g')],both:[v('a#'),v('g')]}
const all:any[]=[];const kept:Record<string,any>={};const parts:string[]=[]
for(const [mode,binder] of [['collision','g'],['fresh','qFresh']] as const){
 const m=make(binder),runtime=interpret(m),s0=runtime.init({}),s1=runtime.step({},s0,{Q:new Map([[0,1]])}),s2=runtime.step({},s1,{Q:new Map([[0,2]])})
 console.log('LEGAL_TRACE',JSON.stringify({mode,machine:m,params:{},requests:[{Q:[[0,1]]},{Q:[[0,2]]}],states:[s0,s1,s2]},(_key,z)=>z instanceof Map?{__map:[...z]}:z))
 for(const [kind,law] of Object.entries(laws)){
  const values=[s0,s1,s2].map(st=>evalC(law.holds,{a:0,g:1},st,m));console.log('INTERPRETER_LAW',JSON.stringify({mode,kind,keys:{a:0,g:1},values}))
  if(kind==='bounded'&&!values.every(Boolean))throw Error('positive control false')
  if(kind!=='bounded'&&values[1]!==false)throw Error('negative control not refuted')
  for(const [strategy,qs] of Object.entries(strategies)){
   const instances={audit:{'?good':qs,audit:[v('a#'),v('g')]}},certs:Record<string,CountCert>={},outcomes:any[]=[]
   for(const {goal,decls} of countedObligations(m,[law],instances)){
    const empty={reads:[],insts:[]},goal0=mcGoal(goal.hyps,decls,empty)!,until=performance.now()+1500
    const out=withWall(until,()=>grow(goal0,new Map(),{nodes:0,until}));if('tree'in out){certs[goal.name]={...empty,tree:out.tree};outcomes.push({goal:goal.name,tree:true,checkMC:checkMC(goal.hyps,decls,certs[goal.name]!)})}else outcomes.push({goal:goal.name,tree:false,stuck:out.stuck,why:out.why,witness:out.witness})
   }
   const proof={instances,certs},accepted=checkCountedLaws(m,[law],proof),record={mode,kind,strategy,accepted,outcomes};all.push(record);console.log('PROOF_SEARCH',JSON.stringify(record))
   if(accepted&&kind!=='bounded')throw Error('ACCEPTED_FALSE_LAW: preserve and investigate')
   if(accepted&&kind==='bounded'&&strategy==='both')kept[mode]={m,law,proof}
  }
 }
 if(!kept[mode])throw Error('missing positive proof '+mode)
 for(const kind of ['zero','uniform'])console.log('REUSED_POSITIVE_CERT',JSON.stringify({mode,kind,accepted:checkCountedLaws(m,[laws[kind]!],kept[mode].proof)}))
 const source=cmachineToLean('probe_'+mode,m,[laws.bounded!],kept[mode].proof)
 console.log('NEW_POSITIVE_PROOF_SHA',mode,sha(JSON.stringify(kept[mode])))
 if(mode==='fresh')parts.push(source)
 else {
  parts.push(source.split('theorem probe_collision_check :')[0]!+'\ntheorem probe_collision_entry_rejected : cEntryOk probe_collision_machine probe_collision_decls (probe_collision_proof.map (·.e)) probe_collision_proof[0].e = false := by decide +kernel\ntheorem probe_collision_start : checkMC (cStartGoal probe_collision_machine [] probe_collision_proof[0].e) [] probe_collision_proof[0].start = true := by decide +kernel\ntheorem probe_collision_step : checkMC (cStepGoal probe_collision_machine [] (probe_collision_proof.map (·.e)) probe_collision_proof[0].e) [] probe_collision_proof[0].step = true := by decide +kernel\n')
  // Negative controls are checked for rejection, not emitted as safety theorems.
 }
}
const lean='import CountMachine\nopen Kern Cert\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n'+parts.join('\n')+'\n#print axioms probe_collision_entry_rejected\n#print axioms probe_collision_start\n#print axioms probe_collision_step\n#print axioms probe_fresh_check\n#print axioms probe_fresh_laws\n'
writeFileSync(dir+'probe-check.lean',lean);writeFileSync(dir+'results.json',JSON.stringify({all,kept},null,2));console.log('PROBE_LEAN_SHA',sha(lean));console.log('PROBE_RESULT_SHA',sha(JSON.stringify({all,kept},null,2)))
