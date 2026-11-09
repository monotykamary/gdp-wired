// Exact, independently fixed acceptance roster. Never derive it from submitted jobs or logs.
export const IC3SYN_IDS=['client_server_ae','client_server_db_ae','consensus','consensus_epr','consensus_forall','consensus_wo_decide','firewall','learning_switch','learning_switch_i4','lock_server','lockserv','lockserv_automaton','majorityset_leader_election','mldr','naive_consensus','paxos_epr','quorum_leader_election','sharded_kv','sharded_kv_no_lost_keys','simple','simple_decentralized_lock','simple_election','simple_regular','tcommit','toy_consensus','toy_consensus_epr','toy_consensus_forall','two_phase_commit','twophase'] as const
export const DUOAI_IDS=['consensus_wo_decide','decentralized_lock','distributed_lock','lock_server_async','lock_server_sync','ring_leader_election','sharded_key_value_store','ticket_lock','toy_consensus_forall','two_phase_commit'] as const
export type Suite='ic3syn'|'duoai'|'broken'
export const SUITES:Suite[]=['ic3syn','duoai','broken']
export type SourcePin={sha:string,archiveSha256:string}
export type Manifest={format:2,base:SourcePin,cand:SourcePin}
export type Expected={base:string,cand:string}
export type Case={suite:Suite,id:string,repeat:number,name:string}
export const casesFor=(suite:Suite):Case[]=>(suite==='duoai'?DUOAI_IDS:IC3SYN_IDS).flatMap(id=>Array.from({length:suite==='ic3syn'?3:1},(_,i)=>({suite,id,repeat:i+1,name:`${id}-r${i+1}`})))
export type Result={verdict:'proven'|'refuted'|'unknown',ms:number}
export type Outcome={exit?:number,result?:Result}
export type Pair={name:string,id:string,repeat:number,base:Outcome,cand:Outcome}
export type Evidence={logs:Record<string,string>,receipts:string}
const sha40=(x:unknown):x is string=>typeof x==='string'&&/^[0-9a-f]{40}$/.test(x)
const sha64=(x:unknown):x is string=>typeof x==='string'&&/^[0-9a-f]{64}$/.test(x)
const proved=(o:Outcome)=>o.exit===0&&o.result?.verdict==='proven'&&o.result.ms<=60000
const refuted=(o:Outcome)=>o.exit===0&&o.result?.verdict==='refuted'&&o.result.ms<=60000
export function validatePins(manifest:Manifest,expected:Expected):string[]{
 const errors:string[]=[]
 if(manifest?.format!==2)errors.push('missing version-2 source manifest')
 for(const side of ['base','cand'] as const){if(!sha40(expected[side]))errors.push(`invalid expected ${side} SHA`);if(!sha40(manifest?.[side]?.sha)||manifest[side].sha!==expected[side])errors.push(`${side} SHA is not bound to requested revision`);if(!sha64(manifest?.[side]?.archiveSha256))errors.push(`invalid ${side} archive hash`)}
 if(expected.base===expected.cand)errors.push('base and candidate must be distinct revisions')
 return errors
}
export function auditSuite(suite:Suite,evidence:Evidence,manifest:Manifest,expected:Expected){
 const errors=validatePins(manifest,expected),cases=casesFor(suite),wanted=new Set(cases.map(c=>c.name)),receipts=new Map<string,number>(),rows:Pair[]=[]
 const receiptLines=evidence.receipts.trim()?evidence.receipts.trim().split('\n'):[]
 for(const line of receiptLines){const [name,exit]=line.trim().split(/\s+/);if(!name||!/^\d+$/.test(exit??'')){errors.push('malformed worker receipt');continue}if(receipts.has(name))errors.push(`duplicate receipt ${name}`);if(!wanted.has(name))errors.push(`unexpected receipt ${name}`);receipts.set(name,Number(exit))}
 for(const file of Object.keys(evidence.logs))if(!wanted.has(file.replace(/\.log$/,''))||!file.endsWith('.log'))errors.push(`unexpected log ${file}`)
 if(receiptLines.length!==cases.length)errors.push(`expected ${cases.length} receipt rows, got ${receiptLines.length}`)
 if(Object.keys(evidence.logs).length!==cases.length)errors.push(`expected ${cases.length} logs, got ${Object.keys(evidence.logs).length}`)
 const phase=suite==='broken'?'broken':'search'
 for(const c of cases){
  const file=`${c.name}.log`,text=evidence.logs[file],row:Pair={name:c.name,id:c.id,repeat:c.repeat,base:{},cand:{}};rows.push(row)
  if(receipts.get(c.name)!==0)errors.push(`${c.name}: missing/failed worker receipt`)
  if(text===undefined){errors.push(`${file}: missing expected log`);continue}
  let active:'base'|'cand'|undefined,sourceSeen=false;const began=new Set<string>(),ended=new Set<string>(),results=new Set<string>()
  const identity=(gotSuite:string,gotId:string,repeat:string,base:string,cand:string)=>{if(gotSuite!==suite||gotId!==c.id||Number(repeat)!==c.repeat)errors.push(`${file}: pair identity mismatch`);if(base!==expected.base||cand!==expected.cand)errors.push(`${file}: pair revision mismatch`)}
  for(const line of text.split('\n')){
   const source=/^PAIR source base=([0-9a-f]{40}) cand=([0-9a-f]{40}) base_archive=([0-9a-f]{64}) cand_archive=([0-9a-f]{64})$/.exec(line)
   const begin=/^PAIR begin side=(base|cand) suite=(ic3syn|duoai|broken) id=([a-z0-9_]+) repeat=([1-3]) base=([0-9a-f]{40}) cand=([0-9a-f]{40})$/.exec(line)
   const end=/^PAIR end side=(base|cand) suite=(ic3syn|duoai|broken) id=([a-z0-9_]+) repeat=([1-3]) base=([0-9a-f]{40}) cand=([0-9a-f]{40}) exit=([0-9]+)$/.exec(line)
   if(source){if(sourceSeen||began.size)errors.push(`${file}: duplicate/late source binding`);sourceSeen=true;if(source[1]!==expected.base||source[2]!==expected.cand||source[3]!==manifest?.base?.archiveSha256||source[4]!==manifest?.cand?.archiveSha256)errors.push(`${file}: source binding mismatch`)}
   else if(begin){const side=begin[1] as 'base'|'cand';if(!sourceSeen)errors.push(`${file}: source was not bound before execution`);if(active||began.has(side))errors.push(`${file}: duplicate/nested begin`);identity(begin[2]!,begin[3]!,begin[4]!,begin[5]!,begin[6]!);began.add(side);active=side}
   else if(end){const side=end[1] as 'base'|'cand';identity(end[2]!,end[3]!,end[4]!,end[5]!,end[6]!);if(active!==side||ended.has(side))errors.push(`${file}: unmatched/duplicate end`);row[side].exit=Number(end[7]);ended.add(side);active=undefined}
   else if(line.startsWith('PAIR '))errors.push(`${file}: malformed unbound pair marker`)
   else if(line.startsWith('{')){
    if(!active){errors.push(`${file}: result outside a paired execution`);continue}
    let parsed:unknown;try{parsed=JSON.parse(line)}catch{errors.push(`${file}: invalid JSON result`);continue}
    if(!parsed||typeof parsed!=='object'){errors.push(`${file}: invalid result object`);continue}
    const record=parsed as Record<string,unknown>,result=record[phase]
    if(record.id!==c.id)errors.push(`${file}: result protocol mismatch`)
    if(record.error!==undefined)errors.push(`${file}: harness error`)
    if(results.has(active))errors.push(`${file}: duplicate result for ${active}`);results.add(active)
    if(!result||typeof result!=='object'){errors.push(`${file}: missing ${phase} result`);continue}
    const value=result as Record<string,unknown>
    if(!['proven','refuted','unknown'].includes(String(value.verdict))||typeof value.ms!=='number'||!Number.isFinite(value.ms)||value.ms<0){errors.push(`${file}: invalid verdict/units`);continue}
    row[active].result={verdict:value.verdict as Result['verdict'],ms:value.ms}
    if(value.verdict==='proven'&&value.ms>60000)errors.push(`${file}: proof exceeds strict budget`)
   }
  }
  if(!sourceSeen||active||began.size!==2||ended.size!==2)errors.push(`${file}: incomplete source/pair envelope`)
  for(const side of ['base','cand'] as const){const o=row[side];if(o.exit===undefined||![0,124,137].includes(o.exit)||o.exit===0&&!o.result)errors.push(`${file}/${side}: incomplete outcome`)}
 }
 const lost=rows.filter(r=>proved(r.base)&&!proved(r.cand)).map(r=>r.name),gained=rows.filter(r=>!proved(r.base)&&proved(r.cand)).map(r=>r.name),falseProofs=suite==='broken'?rows.filter(r=>r.cand.result?.verdict==='proven').map(r=>r.name):[],lostRefutations=suite==='broken'?rows.filter(r=>refuted(r.base)&&!refuted(r.cand)).map(r=>r.name):[]
 return {suite,pass:errors.length===0&&!lost.length&&!falseProofs.length&&!lostRefutations.length,errors,pairs:rows.length,baseProven:rows.filter(r=>proved(r.base)).length,candidateProven:rows.filter(r=>proved(r.cand)).length,lost,gained,falseProofs,lostRefutations,rows}
}
