// Supplemental receipt checks only. This cannot grant Lane D's final-gate admission.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gunzipSync,gzipSync} from 'node:zlib'
import {join} from 'node:path'
const [root,receipts,decoded,expected]=process.argv.slice(2)
if(!root||!receipts||!decoded||!expected||!/^[a-f0-9]{40}$/.test(expected))throw Error('usage: e0-verify.ts EXACT_SOURCE RECEIPTS DECODED_DIR FULL_EXPECTED_SHA')
const identity=Bun.spawnSync(['git','-C',root,'rev-parse','HEAD'],{stdout:'pipe',stderr:'pipe'})
if(identity.exitCode!==0||identity.stdout.toString().trim()!==expected)throw Error('collector source identity mismatch')
const hash=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex')
const required=new Set(['generator-roster-and-p2','twenty-private-laws-replay-on','build-exports-original-runtime',...['optional-choice','ci-audit','law-crosscheck','ci-sibling'].map(n=>'mutants-'+n),...[0,1,31,4294967295].flatMap(seed=>Array.from({length:8},(_,shard)=>`fuzz-${seed}-${shard}-of-8`))])
const rows=readFileSync(join(receipts,'summary.tsv'),'utf8').trim().split('\n').filter(s=>s&&!s.startsWith('name\t')).map(s=>s.split('\t'))
if(rows.length!==required.size||new Set(rows.map(r=>r[0])).size!==required.size||rows.some(r=>!required.has(r[0]!)||r[1]!=='0'||r[3]!=='boat'))throw Error('supplement missing, duplicate, failed or non-Boat job')
mkdirSync(decoded,{recursive:true})
const files:string[]=[],logs=new Map<string,string>(),evidence:Record<string,string>={}
for(const [name] of rows){
 const raw=readFileSync(join(receipts,name+'.log'),'utf8');evidence[name!]=hash(raw);let text=raw
 if(name!.startsWith('fuzz-')){
  const packs=raw.split('\n').filter(s=>s.startsWith('FUZZ_RECEIPT '));if(packs.length!==1)throw Error('fuzz archive cardinality '+name)
  const p=JSON.parse(packs[0]!.slice(13)),bytes=gunzipSync(Buffer.from(p.gzip,'base64'))
  if(p.exit!==0||bytes.length!==p.bytes||hash(bytes)!==p.sha256)throw Error('fuzz archive integrity '+name)
  text=bytes.toString();const path=join(decoded,name+'.log');writeFileSync(path,text);files.push(path)
  const summaries=text.split('\n').filter(s=>s.startsWith('FUZZ_SUMMARY '));if(summaries.length!==1)throw Error('fuzz summary cardinality')
  const s=JSON.parse(summaries[0]!.slice(13)),match=name!.match(/^fuzz-(\d+)-(\d+)-of-8$/)!
  if(s.seed!==Number(match[1])||s.shard!==Number(match[2])||s.shards!==8||s.start!==0||s.count!==52||s.generated!==52||s.replay!=='default'||s.errors||s.findings||s.falseRejections||s.unsafeVerdicts)throw Error('fuzz scope or outcome '+name)
  const cases=text.split('\n').filter(s=>s.startsWith('FUZZ_CASE ')).map(s=>JSON.parse(s.slice(10)))
  if(cases.length!==52||new Set(cases.map(c=>c.id)).size!==52||cases.some((c,i)=>c.id!==`${s.seed}:${s.shard+i*8}`||c.root!==s.api))throw Error('fuzz case identity '+name)
 }
 const heads=text.split('\n').filter(s=>s.startsWith('CLEAN_CHECKOUT_HEAD ')).map(s=>s.slice(20))
 if(heads.length!==1||heads[0]!==expected)throw Error('source identity '+name)
 logs.set(name!,text)
}
const parse=(name:string,prefix:string)=>logs.get(name)!.split('\n').filter(s=>s.startsWith(prefix+' ')).map(s=>JSON.parse(s.slice(prefix.length+1)))
const laws=parse('twenty-private-laws-replay-on','REPLAY_LAWS'),native=parse('twenty-private-laws-replay-on','REPLAY_EXHAUSTIVE'),flat=laws.flatMap(x=>x.rows)
if(laws.length!==2||flat.length!==20||new Set(flat.map(x=>x.id)).size!==20||laws.some(x=>x.exit!==0)||flat.some(x=>x.verdict!=='proven')||native.length!==4||native.some(x=>!x.matched||x.requests<1)||native.reduce((n,x)=>n+x.cases,0)!==212)throw Error('private replay incomplete or changed')
const legacyNames=['drop-equality-context','drop-both-recursive-contexts','drop-calendar-optional-guard','N1-drop-qualified-result-fields','C1-drop-plain-data-contract','B2-class-falsy-is-absent','P2-shared-record-identity','B1-standalone-only-guard','N1-silent-method-rebinding','B1-nested-optional-erased','P2-lazy-argument-root-shared','P2-lazy-key-concatenated','P2-lazy-event-key-unbound']
const legacy=['optional-choice','ci-audit','ci-sibling'].flatMap(n=>logs.get('mutants-'+n)!.split('\n').filter(s=>s.startsWith('{')).map(s=>JSON.parse(s)).filter(x=>'status' in x))
if(legacy.length!==13||new Set(legacy.map(x=>x.name??x.mutant)).size!==13||legacy.some(x=>x.status!=='caught'||!legacyNames.includes(x.name??x.mutant)))throw Error('legacy mutant missing or survived')
for(const [name,marker] of [['optional-choice','MUTATIONS_PASS restored=true'],['ci-audit','CI_AUDIT_MUTATIONS_PASS restored=true'],['ci-sibling','CI_SIBLING_MUTANTS_PASS restored=true']])if(!logs.get('mutants-'+name)!.includes(marker!))throw Error('mutation restore not confirmed')
const cross=parse('mutants-law-crosscheck','CROSSCHECK_MUTANTS')
if(cross.length!==1||!cross[0].passed||cross[0].mutants.length!==13||cross[0].mutants.some((m:any)=>!m.caught))throw Error('source mutant missing or survived')
const aggregated=Bun.spawnSync(['bun',join(root,'research/translation-fuzz/aggregate.ts'),...files.sort()],{stdout:'pipe',stderr:'pipe'})
if(aggregated.exitCode!==0)throw Error(aggregated.stderr.toString())
const line=aggregated.stdout.toString().split('\n').find(s=>s.startsWith('FUZZ_AGGREGATE '));if(!line)throw Error('missing aggregate')
const differential=JSON.parse(line.slice(15)),total=differential.byRevision[expected]
if(Object.keys(differential.byRevision).length!==1||total?.cases!==1664||total.findings||total.errors||total.falseRejections||total.unsafeVerdicts)throw Error('aggregate mismatch')
const result={candidate:expected,jobs:39,mutantsCaught:26,privateLaws:20,privateNativeRows:212,evidence,differential}
const bytes=Buffer.from(JSON.stringify(result)),packed=gzipSync(bytes)
console.log('SUPPLEMENT_RECEIPT '+JSON.stringify({bytes:bytes.length,sha256:hash(bytes),gzip:packed.toString('base64')}))
console.log('SUPPLEMENT_VERIFIED '+JSON.stringify({candidate:expected,jobs:39,mutantsCaught:26,privateLaws:20,privateNativeRows:212,...total}))
