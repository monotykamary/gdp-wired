// D's 9b7485e5 controls, adapted only to the common factory's query event.
// This tests the optional active plan seam; it does not install A's dispatcher.
import {test,expect} from 'bun:test'
import {countedAttempts,countsDump} from './counts.ts'
import {countTierBudget,isLocalCountExpiration} from './count-tier-budget.ts'
import {BudgetExpired,budgetEnd,checkBudget,clock,counted,fullRate,fullWork,withinDeadline,withBudget,withDeadline} from '../kernel/prove.ts'
import {eprMeter} from '../kernel/epr.ts'
import {completeWorkProfile} from './work-profile.ts'
import {costs} from './solver.ts'
import {type Machine,type Law,n,x} from './machine.ts'
const phase=(event:object)=>'phase'in event?event.phase:undefined
const fullTest=completeWorkProfile.enabled?test:test.skip
const m:Machine={name:'independent expiry',params:[],inputs:[],state:{},maps:{A:0},counts:{Total:{j:'row',key:'key',below:n(2),body:{op:'get',map:'A',key:x('key')}}},step:{maps:{A:{key:n(0),value:n(1)}}}}
const law:Law={name:'empty count',holds:{op:'=',a:{op:'get',map:'Total',key:n(0)},b:n(0)}}
function isolate(f:()=>void){const fm=costs.fm,epr=eprMeter.n,dump=countsDump.on;try{counted(fullRate,f,true)}finally{costs.fm=fm;eprMeter.n=epr;countsDump.on=dump}}
function chargePast(end:number){costs.fm+=Math.max(1,Math.ceil((end-clock())*fullRate/2.33)+2)}
function factory(active=true,end=clock()+1000){return countedAttempts(m,[law],new Set(),end,true,true,countTierBudget(clock()-4000,end,active?1:0))}
for(const active of [true,false])test('independent query local expiry active='+active,()=>isolate(()=>withBudget(1e7,()=>{
 // A genuine plan after its strategy endpoint targets the NEW traced catch.
 const a=factory(active);let seen=false
 countsDump.on=e=>{if(phase(e)==='query'&&!seen){seen=true;chargePast(withinDeadline(Infinity));checkBudget('independent local');throw new BudgetExpired('independent local')}}
 if(active)expect(a.traced(law,[law],0,10)).toEqual({stuck:'unknown'});else expect(()=>a.traced(law,[law],0,10)).toThrow(BudgetExpired)
 expect(seen).toBe(true);expect(clock()).toBeLessThan(budgetEnd())
})))
test('independent public exhaustion propagates and restores deadline',()=>isolate(()=>{
 const outer=withinDeadline(Infinity);let seen=false,tracedThrew=false
 expect(()=>withBudget(1e7,()=>{const a=factory();countsDump.on=e=>{if(phase(e)==='query'&&!seen){seen=true;chargePast(budgetEnd());checkBudget('independent public')}};try{a.traced(law,[law],0,10)}catch(e){tracedThrew=true;throw e}})).toThrow(BudgetExpired)
 expect(seen).toBe(true);expect(tracedThrew).toBe(true);expect(withinDeadline(Infinity)).toBe(outer)
}))
fullTest('independent shorter phase captured before factory propagates',()=>isolate(()=>withBudget(1e7,()=>{
 withDeadline(clock()+5,()=>{const a=factory(),outer=withinDeadline(Infinity);let seen=false;countsDump.on=e=>{if(phase(e)==='query'&&!seen){seen=true;chargePast(outer);checkBudget('independent phase')}};expect(()=>a.traced(law,[law],0,100)).toThrow(BudgetExpired);expect(seen).toBe(true);expect(withinDeadline(Infinity)).toBe(outer)})
})))
test('independent unrelated exception identity preserved',()=>isolate(()=>withBudget(1e7,()=>{
 const a=factory(),error=new Error('unrelated independent');let seen=false;countsDump.on=e=>{if(phase(e)==='query'){seen=true;throw error}};try{a.traced(law,[law],0,10);throw Error('swallowed')}catch(e){expect(e).toBe(error)}expect(seen).toBe(true)
})))
for(const pass of [0,1] as const)test('nested per-law/subset local deadline restores pass='+pass,()=>isolate(()=>withBudget(1e7,()=>{
 const a=factory(),outer=withinDeadline(Infinity);let seen=false
 withDeadline(clock()+50,()=>{const perLaw=withinDeadline(Infinity);countsDump.on=e=>{if(phase(e)==='query'&&!seen){seen=true;withDeadline(clock()+.01,()=>{chargePast(withinDeadline(Infinity));checkBudget('nested subset');throw new BudgetExpired('subset')})}};expect(a.traced(law,[law],pass,10)).toEqual({stuck:'unknown'});expect(withinDeadline(Infinity)).toBe(perLaw)})
 expect(seen).toBe(true);expect(withinDeadline(Infinity)).toBe(outer);checkBudget('restored outer')
})))
test('EPR drift helper classification with actual profile and actual checkBudget',()=>isolate(()=>withBudget(1e7,()=>withDeadline(clock()+10,()=>{
 const saved=withinDeadline(Infinity),before=clock(),w=fullWork();eprMeter.n+=3000
 let error:unknown;try{checkBudget('epr enclosing')}catch(e){error=e}
 console.log('EPR_CLASSIFICATION '+JSON.stringify({full:completeWorkProfile.enabled,saved,before,now:clock(),current:withinDeadline(Infinity),rawDelta:fullWork()-w,throws:!!error,helper:error?isLocalCountExpiration(error,saved):null,syntheticHelper:isLocalCountExpiration(new BudgetExpired('synthetic'),saved)}))
 if(completeWorkProfile.enabled){expect(clock()).toBeGreaterThan(saved);expect(isLocalCountExpiration(error,saved)).toBe(false)}else{expect(clock()).toBe(before);expect(withinDeadline(Infinity)).toBeLessThan(clock());expect(error).toBeUndefined();expect(isLocalCountExpiration(new BudgetExpired('synthetic'),saved)).toBe(true)}
}))))
fullTest('later external shorter scope diagnostic (not production call shape)',()=>isolate(()=>withBudget(1e7,()=>{
 const savedEnd=withinDeadline(clock()+1000),a=factory();let seen=false,result:unknown,nativeError:unknown,snapshot:unknown
 withDeadline(clock()+5,()=>{countsDump.on=e=>{if(phase(e)==='query'&&!seen){seen=true;chargePast(withinDeadline(Infinity));try{checkBudget('late external phase')}catch(error){nativeError=error;snapshot={clock:clock(),currentEnd:withinDeadline(Infinity),savedEnd,publicEnd:budgetEnd(),error:String(error)};throw error}}};result=a.traced(law,[law],0,100)})
 console.log('LATE_EXTERNAL_SCOPE '+JSON.stringify({seen,result,snapshot}));expect(seen).toBe(true);expect(nativeError).toBeInstanceOf(BudgetExpired);expect(result).toEqual({stuck:'unknown'})
})))
