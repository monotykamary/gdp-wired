import {expect,test} from 'bun:test'
import {type CountCert,type Goal,canon,checkGoalLemmas} from '../kernel/kernel.ts'
import {countedCertificateHyps} from './count-cert-transport.ts'
import {countedScopeHyps} from './count-scope-hyps.ts'
import {completeWorkProfile} from './work-profile.ts'
import {BudgetExpired,workLedger,withWorkAdmissionTrace,type WorkAdmissionEvent} from './work-admission.ts'
import {workAdd,workAmount,workMultiply,workShare} from './work-amount.ts'

const full=completeWorkProfile.enabled?test:test.skip
let serial=0
function coldLegacyFixture():{goal:Goal,cert:CountCert}{
 // Fresh variable names prevent the prover's structural row/fact caches from
 // bypassing native construction. No row building or proof search warms them.
 const name=`r1_legacy_${++serial}`,cut={}
 canon(cut) // Only warm the empty cut's canonical text, outside the test grant.
 return {
  goal:{name:'legacy hard stop',hyps:[{op:'<',a:{op:'var',name},b:{op:'const',value:0}}]},
  cert:{reads:[],insts:[],tree:{leaf:[{kind:'input',index:1},{kind:'input',index:2},{kind:'combine',a:0,b:1,ma:1,mb:1}]},
   lemmas:[{when:[],cut,slice:[],tree:{leaf:[{kind:'input',index:0}]}}]},
 }
}

test('the cold hard-stop fixture has an ordinary valid lemma certificate',()=>{
 const {goal,cert}=coldLegacyFixture()
 expect(checkGoalLemmas(goal,cert.tree,cert.lemmas)).toBe(true)
})

// These cases require GDP_WORK_FULL=1 and GDP_ROWS_SHARED=1 (or its default).
// They must not be reported as covered when the FULL-only tests are skipped.
for(const mode of ['legacy','scope'] as const)full(`${mode} extraction propagates a genuine refusal inside legacy rowsAt`,()=>{
 expect(process.env.GDP_ROWS_SHARED).not.toBe('0')
 const {goal,cert}=coldLegacyFixture(),events:WorkAdmissionEvent[]=[]
 // lemmaPath canonicalizes the empty cut once, and proverRows' path key once.
 // Fund both table reads, plus the new collector's entry tick if present, but
 // only half of the FIRST native facts tick. Thus entry and the legacy path
 // succeed; the original allocator must refuse inside rowsAt -> kernel facts.
 let grant=workAdd(workMultiply(workLedger.weights.tableCells,workAmount(2n)),workShare(workLedger.weights.ticks,1n,2n))
 if(mode==='scope')grant=workAdd(grant,workLedger.weights.ticks)
 let returned=false,caught:unknown
 workLedger.withBudget(grant,()=>withWorkAdmissionTrace(event=>{
  if(event.kind==='start'||event.kind==='refuse')events.push(event)
 },()=>{
  // Observe before leaving the active budget. A scope-completion exception
  // must not mask the old helper swallowing the original native exception.
  try{(mode==='legacy'?countedCertificateHyps:countedScopeHyps)(goal,cert);returned=true}
  catch(error){caught=error}
 }))
 expect(returned).toBe(false)
 expect(caught).toBeInstanceOf(BudgetExpired)
 expect((caught as BudgetExpired).phase).toBe('kernel facts')
 // Only the identical error minted by this ledger has this receipt; a copied
 // or manually constructed BudgetExpired cannot satisfy this assertion.
 expect(workLedger.capacityRefusal(caught)?.reason).toBe('quantum')
 expect(events.filter(e=>e.kind==='start'&&e.site==='pair-scope:entry')).toHaveLength(mode==='scope'?1:0)
 expect(events.filter(e=>e.kind==='start'&&e.sink==='tableCells')).toHaveLength(2)
 expect(events.some(e=>e.kind==='refuse'&&e.site==='kernel facts'&&e.sink==='ticks')).toBe(true)
 expect(events.some(e=>e.site==='pair-scope:legacy-reference')).toBe(false)
})

test('ordinary malformed legacy metadata still declines without cancellation',()=>{
 const goal:Goal={name:'malformed legacy metadata',hyps:[]}
 const cert={reads:[],insts:[],tree:{leaf:[]},lemmas:[null]} as unknown as CountCert
 expect(countedCertificateHyps(goal,cert)).toBeUndefined()
 expect(countedScopeHyps(goal,cert)).toBeUndefined()
})
