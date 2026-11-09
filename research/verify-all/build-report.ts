import {readFileSync,readdirSync,existsSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join,relative,resolve} from 'node:path'
const root=process.argv[2]??'evidence', read=(p:string)=>readFileSync(p,'utf8'), sha=(t:string)=>createHash('sha256').update(t).digest('hex')
const js=(t:string):any[]=>t.split('\n').flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}})
const table=(s:string,start:string,end:string)=>{const i=s.indexOf(start),j=s.indexOf(end,i);if(i<0||j<0)throw Error('missing section '+start);return s.slice(i,j)}
const model=read('research/verify-all/model-source-audit.md'),engine=read('research/verify-all/engine-trust-audit.md'),tlc=read('research/verify-all/tlc-audit.md')
if(/^.*IN PROGRESS.*$/im.test(tlc.split('\n')[0]!))throw Error('TLC report is not final')
const relink=(text:string)=>text.replace(/\]\(([^)]+)\)/g,(all,target:string)=>/^(?:[a-z]+:|#|\/)/i.test(target)?all:`](${relative('runs',resolve('research/verify-all',target))})`)
let report=read('research/verify-all/report-intro.md')
const production=read(join(root,'report-base-final/report-base.log')), appendix=production.indexOf('### Original-run evidence hashes')
report+=production.slice(0,appendix)+'\n### Broken-run replay\n\n'
const replay=js(read(join(root,'recheck-replay-final/recheck-replay.log'))).filter(r=>r.replay)
report+='| Protocol | Legal replay steps | Failed stated law | Captured run SHA-256 |\n|---|---:|---|---|\n'
for(const r of replay)report+=`| ${r.id} | ${r.replay.steps} | ${r.replay.failedLaw} | \`${r.replay.runSha256}\` |\n`
report+='\nAll replayed traces met the initial precondition and every interpreter step checked the request assumption. The small-instance `p.bad` helper is diagnostic only: it misses some valid production-domain counterexamples outside its fixed 0..2 domain. Early audit-helper failures caused by treating it as authoritative were retained in `replay/` and `recheck-replay/`; the corrected `recheck-replay-final/` checks the actual stated law. No new production search was used for these rechecks. The witness packets themselves came from the separate instrumented broken-run repetitions: the primary harness printed only trace lengths. Exact replay of the original primary witness bytes is therefore not established; the retained repeats provide legal counterexamples for the same eleven refuted IDs.\n\n'
report+='## 2. Safety clauses and supplied knowledge\n\n'+table(model,'| Protocol |','All source clauses')
report+='\nSource hash ledger, complete assumption inventory and judgments: [model-source-audit.md](../research/verify-all/model-source-audit.md). Runtime inventory: 29 models, 33 explicit safety laws, 29 request assumptions, 20 parameter preconditions, no supplied facts/functions/human invariant families, two check-only constraints. Kind laws are additional generated obligations, not handwritten protocol invariants. Switch reflexivity is structural; seven arbitrary-quorum sources are specialized to majorities; no unrestricted source equivalence/cutoff proof was established.\n\n'
report+='## 3. Fresh TLC correspondence\n\n'+relink(tlc).replace(/^# .*\n/, '')+'\n\n'
if(!tlc.includes('| ID |'))report+='### Per-protocol state/edge receipts\n\n'+table(read('research/verify-all/tlc-results-20261109.md'),'| ID |','\n\n')+'\n\n'
report+='## 4. Accepted certificates checked independently in Lean\n\nThe exact captured proof objects are re-exported; no replacement invariant family is supplied. Ordinary certificates seed the emitter with their retained trees; sum cover trees also come from that packet. Existential substitutions are recovered structurally from the captured law, with fresh logical binders, then validated by Lean’s ghost-extension and `forall_some_of_ghostsubst` rules. Original-model projection is checked up to bound-variable alpha-renaming. All accepted Lean results require process exit 0 and only `propext`, `Classical.choice`, `Quot.sound`, never `native_decide` or `sorryAx`.\n\n'
const metadata=js(read(join(root,'capture-metadata-final/capture-metadata.log'))).filter(r=>r.captureSha256), captureDir=join(root,'capture-all')
const captures=readdirSync(captureDir).filter(f=>f.endsWith('.log')).sort()
if(metadata.length!==captures.length || new Set(metadata.map(r=>r.id)).size!==captures.length)throw Error('incomplete or duplicated final metadata')
report+='| Protocol | Captured certificate | Laws | Lean result | Original-claim connection | Packet SHA-256 | Lean-file SHA-256 |\n|---|---|---:|---|---|---|---|\n'
let leanPass=0, accepted=0
for(const file of captures){
 const text=read(join(captureDir,file)), base=js(text).find(r=>r.captureSha256)!,r=metadata.find(r=>r.id===base.id)
 if(!r || r.captureSha256!==base.captureSha256)throw Error('capture packet mismatch '+file)
 let status=text.match(/LEAN_EXIT (\d+)/)?.[1],checkedSha=base.leanSha256,checkedPacket=base.captureSha256,where='capture-all/'+file
 for(const batch of ['recheck-capture','recheck-final']){const path=join(root,batch,'recheck-'+base.id+'.log');if(existsSync(path)){const rr=js(read(path)),out=rr.find(x=>x.captureSha256),lean=rr.find(x=>x.leanExit!==undefined);if(lean){status=String(lean.leanExit);checkedSha=out?.leanSha256;checkedPacket=out?.captureSha256;where=batch+'/recheck-'+base.id+'.log'}}}
 let result=!r.accepted?'no accepted certificate':r.exportError?'export error':status&&(checkedSha!==r.leanSha256||checkedPacket!==r.captureSha256)?'hash mismatch / not established':status==='0'?'PASS':status==='1'?'REJECTED':'not established'
 if(r.accepted)accepted++;if(result==='PASS')leanPass++
 const connection=r.existentialBridge?'checked existential/ghost bridge':r.sumBridge?'checked sum bridge':r.countedProjectionAlphaEquivalent?'same model plus derived count views; caller law included':r.sourceLawEquality&&r.machineAlphaEquivalent?'same laws/model modulo bound names':'not established'
 report+=`| ${r.id} | ${r.kind??'—'} | ${r.laws??'—'} | [${result}](verify-all/${where}) | ${connection} | \`${r.captureSha256}\` | ${r.leanSha256?'`'+r.leanSha256+'`':'—'} |\n`
}
report+=`\n**Independent Lean summary: ${leanPass}/${accepted} accepted captured families passed the original-model export check.** MLDR has no accepted family. Initial failures and every retry are retained, not replaced. The ordinary/counted/ghost/sum kinds all have existing Lean machinery; a rejected supported certificate is not an “unsupported exporter” result.\n\n`
report+=relink(read('research/verify-all/paxos-diagnostic.md'))+'\n\n'
report+='## 5. Engine answer-encoding audit\n\n'+table(engine,'| Baseline file:line(s) |','All remaining fragment hits')
report+='\nFull generic-template, tuned-constant, environment and I/O inventories: [engine-trust-audit.md](../research/verify-all/engine-trust-audit.md). The scan covered all 303 core/kernel files; the conservative DSL import closure had 36 files and zero I/O/dynamic-loading scan hits. It found 86 distinct environment accesses in that closure (110 repository-wide). No per-protocol dispatch or loaded protocol-specific law family was found, but this does not establish the absence of benchmark-shaped knowledge: scan-prefix/carry/future-writer templates and benchmark-shaped gates remain live. `GDP_STRICT` is currently on by default for non-usual decisions despite a stale adjacent comment.\n\n'
report+=read('research/verify-all/report-conclusion.md')+'\n\n'+production.slice(appendix)
console.log('REPORT_BEGIN\n'+report+'\nREPORT_END')
console.log('REPORT_META '+JSON.stringify({bytes:Buffer.byteLength(report),sha256:sha(report),leanPass,accepted,replayed:replay.length}))
