import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const root=process.argv[2]??'evidence', sha=(s:string)=>createHash('sha256').update(s).digest('hex')
const file=join(root,'paxos-feature-census/paxos-feature-census.log'), text=readFileSync(file,'utf8')
const rows:any[]=text.split('\n').filter(l=>l.startsWith('CENSUS_ROW ')).map(l=>JSON.parse(l.slice(11)))
const sum=JSON.parse(text.split('\n').find(l=>l.startsWith('CENSUS_SUMMARY '))!.slice(15))
if(rows.length!==29||new Set(rows.map(r=>r.id)).size!==29||sha(JSON.stringify(rows))!==sum.censusSha256)throw Error('bad census identity')
for(const r of rows)if(sha(readFileSync(join(root,r.receipt),'utf8'))!==r.receiptSha256)throw Error('changed Lean receipt '+r.id)
const others=rows.filter(r=>r.accepted&&r.id!=='paxos_epr'), p=rows.find(r=>r.id==='paxos_epr')
if(others.length!==27||others.some(r=>!r.leanChecked)||sum.otherScanPrefix.length||sum.otherCarryCoWrite.length||sum.otherCollisions.length)throw Error('unexpected feature coverage')
let md='## (c) Coverage in the other 27 accepted certificates\n\n'
md+='**None of the other 27 accepted families contains either a `scan-prefix:*` law with further keys or a `carry:co-write:*` law.** Only the retained Paxos family contains these generated families: law 12 has the scan-prefix/further-key collision with `rowOk`; law 20 is the carry co-write step. Thus the other 27 successful Lean checks do not test either of these specific generated families.\n\n'
md+='Some other certificates contain multi-key laws. Their exact exported families passed Lean, and the census found no collision between any of their further keys and a quantified flag binder. That is coverage of those concrete proofs, not a proof that every possible further-key use is sound.\n\n'
md+='Classification is tied to the constructors in `core/carry.ts:94-95,168,387-390`: `carry:${family}:...` with family `co-write`, and `scan-prefix:...` with `keys:[row.key]`. It inspects retained law objects, not only the user-facing `found` text. Prior `checkCMachine` success checks every entry, its side conditions and both certificates (`lean-kernel/CountMachine.lean:751-774`); ordinary families use their existing whole-family/exported original-law checks. The table links exact original receipts, rather than rerunning proof search or silently replacing trees.\n\n'
md+='| Protocol | Scan-prefix + further keys | Carry co-write | Other multi-key laws | Prior exact-family Lean check | Packet SHA-256 | Lean file SHA-256 |\n|---|---:|---:|---:|---|---|---|\n'
for(const r of others)md+=`| ${r.id} | ${r.scanPrefixFurtherKeys.length} | ${r.carryCoWrite.length} | ${r.otherFurtherKeys.length} | [PASS](../../runs/verify-all/${r.receipt}) | \`${r.packetSha256}\` | \`${r.leanSha256}\` |\n`
md+='\nPaxos comparison: `'+p.scanPrefixFurtherKeys.map((l:any)=>l.name).join('`, `')+'`; `'+p.carryCoWrite.map((l:any)=>l.name).join('`, `')+'`. Its original Lean check remains rejected. MLDR is excluded from the accepted-family denominator because it had no accepted family.\n\n'
md+='Census: [raw log](../../runs/verify-all/paxos-feature-census/paxos-feature-census.log), SHA-256 `'+sha(text)+'`; row-array SHA-256 `'+sum.censusSha256+'`. The generator verifies all receipt hashes again before producing this table.\n\n'
md+='```sh\nsupercomputer run --jobs research/verify-all/paxos-feature-census.jobs.json --out runs/verify-all/paxos-feature-census --class interactive --backend boat --data runs/verify-all:evidence\nsupercomputer run --jobs research/verify-all/paxos-census-report.jobs.json --out runs/verify-all/paxos-census-report --class interactive --backend boat --data runs/verify-all:evidence\n```\n'
console.log('CENSUS_REPORT_BEGIN\n'+md+'\nCENSUS_REPORT_END')
console.log('CENSUS_REPORT_META '+JSON.stringify({sha256:sha(md),bytes:Buffer.byteLength(md),rows:others.length,priorChecks:27}))
