import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {fileURLToPath} from 'node:url'
import {bool,upTo,rule,when,proveRule,proveSteps} from './dsl.ts'
import {CountAttemptTickets} from './count-retry-budget.ts'
const model=(broken=false)=>rule('initial and retry attempt tickets').params({fuel:upTo(6)})
 .inputs({start:bool,finish:bool,unfinished:bool}).state({used:0,active:bool.from(false),terminal:bool.from(false)})
 .step(({fuel,start,finish,unfinished,used,active,terminal})=>{
  const take=start.and(active.not()).and(terminal.not()).and(broken?used.atLeast(0):used.lt(fuel.plus(1)))
  const end=start.not().and(finish).and(active)
  return {used:when(take,used.plus(1),used),active:take.or(active.and(end.not())),
   terminal:terminal.or(end.and(unfinished.not().or(used.atLeast(fuel.plus(1)))))}
 })
// The mathematical model has no profile dependency. Its proof is isolated from
// FULL's separately reported optional cyclic-translation local-cutoff issue
// (T324). This is NOT a successful FULL verifier or source-correspondence claim.
const sourceDigest=()=>createHash('sha256').update(readFileSync(fileURLToPath(import.meta.url))).digest('hex')
const proofChild=process.env.GDP_TICKET_MODEL_PROOF_CHILD==='1'
if(proofChild)test('isolated ticket model has checked bound and any-state terminal proofs',()=>{
 expect(process.env.GDP_WORK_FULL).toBe('0');expect(process.env.GDP_WORK_STEPS).toBe('0')
 const expectedSource=process.env.GDP_TICKET_MODEL_SHA256
 if(expectedSource===undefined)throw Error('missing proof source identity')
 expect(sourceDigest()).toBe(expectedSource)
 const r=model(),bound=r.law('at most one initial plus fuel attempts',({used,fuel})=>used.atMost(fuel.plus(1)))
 const law=proveRule(r,[bound],{search:false})
 expect(law.proven).toBe(true);expect(law.checked).toBe(true);expect(law.assumes).toBeUndefined()
 const terminal=r.stepLaw('terminal never reopens',({terminal},after)=>terminal.implies(after.terminal))
 const step=proveSteps(r,[],[terminal],{from:'any',search:false})
 expect(step.proven,JSON.stringify(step)).toBe(true);expect(step.checked).toBe(true);expect(step.assumes).toBeUndefined()
 const bad=model(true),rejected=proveRule(bad,[bad.law('attempts stay within tickets',({used,fuel})=>used.atMost(fuel.plus(1)))],{search:false})
 expect(rejected.proven).toBe(false)
 expect(sourceDigest()).toBe(expectedSource)
 console.log('TICKET_MODEL_PROOF '+JSON.stringify({format:'count-attempt-ticket-proof/v1',sourceSha256:sourceDigest(),domain:{fuelMin:0,fuelMax:6},profile:{FULL:'0',STEPS:'0'},terminalFrom:'any',bound:{proven:law.proven,checked:law.checked,assumes:law.assumes??null},terminal:{proven:step.proven,checked:step.checked,assumes:step.assumes??null},brokenAccepted:rejected.proven}))
})
else{
 test('ticket mathematical proof is native checked in an explicitly isolated OFF profile',()=>{
  const env=Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_'))),sourceSha256=sourceDigest()
  const child=spawnSync(process.execPath,['test',fileURLToPath(import.meta.url)],{env:{...env,GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0',GDP_TICKET_MODEL_PROOF_CHILD:'1',GDP_TICKET_MODEL_SHA256:sourceSha256},encoding:'utf8',timeout:120000})
  expect(child.error,child.stderr).toBeUndefined();expect(child.status,child.stderr).toBe(0)
  const lines=child.stdout.split('\n').filter(line=>line.startsWith('TICKET_MODEL_PROOF '))
  expect(lines).toHaveLength(1)
  const receipt:unknown=JSON.parse(lines[0]!.slice('TICKET_MODEL_PROOF '.length))
  expect(sourceDigest()).toBe(sourceSha256)
  expect(receipt).toEqual({format:'count-attempt-ticket-proof/v1',sourceSha256,domain:{fuelMin:0,fuelMax:6},profile:{FULL:'0',STEPS:'0'},terminalFrom:'any',bound:{proven:true,checked:true,assumes:null},terminal:{proven:true,checked:true,assumes:null},brokenAccepted:false})
  console.log(lines[0])
 })
 test('actual ticket class follows the checked model in the current runtime profile',()=>{
  const comparison=model().compare({
   init:():{used:number,active:boolean,terminal:boolean}=>({used:0,active:false,terminal:false}),
   step:({fuel},state,input)=>{
    const tickets=new CountAttemptTickets(Number(fuel))
    // Test-only reconstruction exercises shipped methods on model pre-states.
    const internal=tickets as unknown as {left:number,runs:number,active:boolean,ended:boolean}
    internal.left=Number(fuel)+1-Number(state.used);internal.runs=Number(state.used)
    internal.active=Boolean(state.active);internal.ended=Boolean(state.terminal)
    if(input.start)tickets.start()
    else if(input.finish&&internal.active)tickets.finish(input.unfinished?'unfinished':'decline')
    const next=tickets.snapshot();expect(next.remaining).toBe(Number(fuel)+1-next.started)
    return {used:next.started,active:next.active,terminal:next.terminal}
   },
  })
  expect(comparison.failure).toBeUndefined()
 })
 test('the uncapped ticket variant is not accepted in the current runtime profile',()=>{
  const bad=model(true),rejected=proveRule(bad,[bad.law('attempts stay within tickets',({used,fuel})=>used.atMost(fuel.plus(1)))],{search:false})
  expect(rejected.proven).toBe(false)
 })
}
