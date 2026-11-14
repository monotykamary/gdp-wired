// Synthetic local-only controls. No production imports, model/proof runs or jobs.
import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {encode} from './io.ts'
import {checkSingle} from './single-checks.ts'
import {projectCountEvent,COUNT_PROJECTION} from './count-projection.ts'
import {comparePair as compareWithRoot,recomputeDeltas,WORK_KEYS} from './pair-checks.ts'
import {boundRate,estimatedRootRaw,requireRootRaw,validateRootPlan} from './root-policy.ts'
import {MeasurementRows,referenceSeconds} from './measurement-rows.ts'
import {infrastructureStop} from './infrastructure-stop.ts'
import {validateTraceResult,validateHeader,TRACE_SCHEMA,TRACE_RESULT_SCHEMA,SERIALIZATION} from './trace-contract.ts'
import {validateResourcePair} from './resource-checks.ts'
const FIXTURE_ROOT_RAW='123456789' // synthetic only; never a production root
const comparePair=(a:any,b:any,replay:any)=>compareWithRoot(a,b,replay,FIXTURE_ROOT_RAW)
const names:string[]=[]
function check(name:string,f:()=>void){f();names.push(name)}
const copy=<T>(x:T):T=>structuredClone(x)
const q=(n:number)=>({numerator:String(n),denominator:'1'})
function fixture(n=1):any{
 const zeros=Object.fromEntries(WORK_KEYS.map(k=>[k,'0'])),weights=Object.fromEntries(WORK_KEYS.map(k=>[k,q(1)])),rootBaseline={actual:q(0),counters:copy(zeros)}
 const initial={rootEpoch:1,counterEpoch:0,actual:q(0),reserved:q(0),activeEndpoints:[{id:1,kind:'root',end:q(Number(FIXTURE_ROOT_RAW))}],rootBaseline,weights,counters:copy(zeros)}
 const final={...copy(initial),counterEpoch:n>0?1:0,actual:q(n),counters:{...zeros,fm:String(n)}}
 return {schema:'mldr-3g-diagnostic/v2',identity:{serialization:SERIALIZATION,sourceCommit:'9eb09b8326fc2670fad6725f774ab1b252c4d343',sourceTree:'20e56881dd613158a5ac53b3633bd8b3e3db8ed5',profileSHA256:'a5f077dc8156a7bb550dc0ed279de96b20aa3a167c32fbaaaaad925fc9f8a272',mode:'timed',protocol:'mldr',rootRaw:FIXTURE_ROOT_RAW,runtime:{version:'1.4.3',sha256:'1'.repeat(64)}},modelSHA256:'1'.repeat(64),lawsSHA256:'2'.repeat(64),mode:'timed',observerInstalled:false,diagnosticComplete:true,rawVerdict:{proven:false,checked:false},verdict:'unknown',originalRootRaw:FIXTURE_ROOT_RAW,initial,final,settled:{activeEndpoints:[],rootBaseline:null,effectiveEnd:null,reserved:q(0)},counterDeltas:{...zeros,fm:String(n)},trace:null}
}
const instrumented=(n=1)=>{const b=fixture(n);b.mode=b.identity.mode='instrumented';b.observerInstalled=true;b.trace={complete:true,oracle:{passed:true}};return b}
check('distinct Map contents both refuse, never collapse to equal objects',()=>{for(const m of [new Map([[1,2]]),new Map([[1,3]])])assert.throws(()=>encode({maps:m},4096),/unsupported record container: Map/)})
check('distinct Sets both refuse',()=>{for(const s of [new Set([1]),new Set([2])])assert.throws(()=>encode({set:s},4096),/unsupported record container: Set/)})
check('function fields in proof/model/verdict refuse',()=>assert.throws(()=>encode({proof:()=>true},4096),/unsupported record scalar: function/))
check('scalar tags avoid bigint/string and undefined/null collisions',()=>{assert.notEqual(encode(1n,4096).toString(),encode('1',4096).toString());assert.notEqual(encode(undefined,4096).toString(),encode(null,4096).toString());assert.throws(()=>encode({$mldr:'bigint',value:'1'},4096),/reserved record key/)})
check('cycles, dates, sparse arrays and oversized records refuse',()=>{const v:any={};v.v=v;for(const x of [v,new Date(),Array(2)])assert.throws(()=>encode(x,4096));assert.throws(()=>encode({x:'x'.repeat(100)},10),/byte limit/)})
check('declared counts callback projection never invokes callback',()=>{let called=false;const p=projectCountEvent({phase:'count-rejection-result',replayEvidence:()=>{called=true;return []}});assert.equal(called,false);assert.deepEqual(p.omittedCallbacks,['replayEvidence']);assert.equal(p.projection,COUNT_PROJECTION);assert.doesNotThrow(()=>encode(p,4096));assert.throws(()=>projectCountEvent({other:()=>0}),/unsupported counts callback/)})
check('positive advancing-epoch pair uses recomputed 26 counters',()=>{const r=comparePair(fixture(),instrumented(),{complete:true,oraclePassed:true});assert.equal(r.status,'EQUAL_OBSERVED_PAIR');assert.equal(Object.keys(r.recomputedCounterDeltas.timed).length,26)})
check('batched positive work advances generation once, not by units',()=>{const a=fixture(5),b=instrumented(5);for(const v of [a,b]){v.initial.counterEpoch=7;v.final.counterEpoch=8}b.final.counterEpoch=10;assert.equal(comparePair(a,b,{complete:true,oraclePassed:true}).status,'EQUAL_OBSERVED_PAIR');assert.equal(a.final.counterEpoch-a.initial.counterEpoch,1);assert.equal(recomputeDeltas(a).fm,'5')})
check('zero work permits unchanged valid counter epoch',()=>assert.equal(comparePair(fixture(0),instrumented(0),{complete:true,oraclePassed:true}).status,'EQUAL_OBSERVED_PAIR'))
check('counter epoch regression refuses',()=>{const v=fixture();v.initial.counterEpoch=2;v.final.counterEpoch=1;assert.throws(()=>recomputeDeltas(v),/counter epoch regressed/)})
check('invalid initial or final counter epochs refuse',()=>{for(const field of ['initial','final'])for(const bad of [-1,0.5,Number.MAX_SAFE_INTEGER+1,NaN,Infinity,'1',null,undefined]){const v=fixture();v[field].counterEpoch=bad;assert.throws(()=>recomputeDeltas(v),/invalid counter epoch/)}})
check('positive counters require some epoch advance',()=>{const v=fixture();v.final.counterEpoch=v.initial.counterEpoch;assert.throws(()=>recomputeDeltas(v),/positive counters without epoch advance/)})
check('root epoch remains fixed even while counter epoch advances',()=>{const v=fixture();v.final.rootEpoch++;assert.throws(()=>recomputeDeltas(v),/root baseline\/epoch changed/)})
check('same echoed vector cannot hide distinct native final counters',()=>{const a=fixture(1),b=instrumented(2);b.counterDeltas=copy(a.counterDeltas);const r=comparePair(a,b,{complete:true,oraclePassed:true});assert.equal(r.status,'PAIR_REJECTED');assert.equal(r.checks.counters,false);assert.equal(r.checks.echoedDeltas,false)})
check('forged matching echoes refuse even with equal underlying vectors',()=>{const a=fixture(),b=instrumented();a.counterDeltas.fm=b.counterDeltas.fm='7';assert.equal(comparePair(a,b,{complete:true,oraclePassed:true}).status,'PAIR_REJECTED')})
check('root baseline changes refuse independent derivation',()=>{const b=instrumented();b.final.rootBaseline.counters.fm='9';assert.throws(()=>recomputeDeltas(b),/baseline\/epoch changed/)})
check('matching oracle failures are a distinct non-PASS result',()=>{const b=instrumented();b.trace.oracle.passed=false;assert.equal(comparePair(fixture(),b,{complete:true,oraclePassed:false}).status,'ORACLE_VIOLATION')})
function syntheticBasis(root=FIXTURE_ROOT_RAW):any{
 const ref={sourcePath:'synthetic.json',sourceSHA256:'0'.repeat(64)}
 const b:any={status:'MEASUREMENT_CEILING',label:'PLANNING_ASSUMPTION_NOMINAL_2H',basisType:'PLANNING_ASSUMPTION',referenceSeconds:7200,acceptanceReferenceSeconds:600,estimated:true,frozenCalibration:false,verdictAuthority:false,rhoNew:null,boundProven:false,acceptedCalibration:false,oldRate:{numerator:root,denominator:'14400',assumed:true,...ref},assumedInflation:{numerator:'1',denominator:'1',assumed:true,...ref},margin:{numerator:'2',denominator:'1',...ref}}
 b.upperUnitsPerReferenceSecond=boundRate(b);return b
}
function traceFixture(){
 const verdict=instrumented(),limits={compressedBytes:1073741824,rawBytes:8589934592,records:1000000,recordBytes:4194304,bufferBytes:2097152,shardBytes:33554432,files:32}
 const config={serialization:{schema:SERIALIZATION},source:{commit:verdict.identity.sourceCommit,tree:verdict.identity.sourceTree},profileSHA256:verdict.identity.profileSHA256,rootRaw:FIXTURE_ROOT_RAW,runtime:{bun:verdict.identity.runtime},trace:limits,rootBasis:syntheticBasis()}
 const trace={schema:TRACE_RESULT_SCHEMA,serialization:SERIALIZATION,countsProjection:COUNT_PROJECTION,identity:verdict.identity,limits:copy(limits),complete:true,limit:null,records:3,events:0,rawBytes:70,compressedBytes:1,shards:[{path:'trace-000.jsonl.gz',bytes:1}],oracle:{passed:true}};verdict.trace=trace
 const header={kind:'header',schema:TRACE_SCHEMA,serialization:SERIALIZATION,countsProjection:COUNT_PROJECTION,identity:verdict.identity,limits:copy(limits)}
 return {config,verdict,trace,header}
}
check('nominal reference ceiling rounds upward',()=>assert.equal(estimatedRootRaw({numerator:'1',denominator:'7'}),'1029'))
check('pending calibration cannot authorize this nominal packet',()=>assert.throws(()=>requireRootRaw({rootRaw:null,rootBasis:{status:'PENDING_RHO_NEW'}}),/measurement-only/))
check('nominal assumptions are disclosed and not calibration',()=>{const config={rootRaw:FIXTURE_ROOT_RAW,rootBasis:syntheticBasis()};assert.equal(validateRootPlan(config),FIXTURE_ROOT_RAW);config.rootBasis.boundProven=true;assert.throws(()=>validateRootPlan(config));config.rootBasis.boundProven=false;config.rootBasis.acceptedCalibration=true;assert.throws(()=>validateRootPlan(config))})
check('altered ceiling or margin refuses',()=>{const c={rootRaw:FIXTURE_ROOT_RAW,rootBasis:syntheticBasis()};c.rootRaw='1';assert.throws(()=>validateRootPlan(c));c.rootRaw=FIXTURE_ROOT_RAW;c.rootBasis.margin.numerator='3';assert.throws(()=>validateRootPlan(c))})
check('per-law spans reconcile with explicit unattributed work and cannot upgrade public verdict',()=>{const v=fixture(5),m=new MeasurementRows(v.initial,['safety']);m.observe({phase:'count-component-attempt',law:'helper'},v.initial);const partial=copy(v.final);partial.actual=q(3);partial.counters.fm='3';m.observe({phase:'count-component-result',law:'helper',held:true},partial);m.observe({phase:'closed-family',checked:true,laws:[{name:'helper'},{name:'safety'}]},v.final);const report=m.finish(v);assert.deepEqual(report.attributedCountedUnits,q(3));assert.deepEqual(report.sharedOrUnattributedUnits,q(2));assert.equal(report.publicProvenAndChecked,false);assert.equal(report.rows.find(r=>r.name==='helper').status,'CHECKED_NATIVE_FAMILY_MEMBER')})
check('qualified-rate arithmetic remains separate from nominal ceiling',()=>assert.deepEqual(referenceSeconds(q(1200),q(2)),q(600)))
check('infrastructure guard has no semantic verdict and retains received code',()=>{const r=infrastructureStop({'mldr-3g-timed':{code:124,seconds:64800}},{effectivePayloadGuardSeconds:64800});assert(r,'expected infrastructure receipt');assert(r.affected[0],'expected affected native row');assert.equal(r.status,'INFRA_HANG_GUARD');assert.equal(r.verdict,null);assert.equal(r.affected[0].rawNativeRow.code,124)})
check('kill or early timeout alone does not establish the external guard',()=>{for(const code of [137,-9,124]){const r=infrastructureStop({'mldr-3g-timed':{code,seconds:120}},{effectivePayloadGuardSeconds:64800});assert(r,'expected infrastructure receipt');assert.equal(r.status,'INFRASTRUCTURE_TERMINATION_UNATTRIBUTED')}})
check('a second synthetic root works without a hardcoded 3G constant',()=>{const raw='77000000',a=fixture(),b=instrumented();for(const v of [a,b]){v.identity.rootRaw=raw;v.originalRootRaw=raw;v.initial.activeEndpoints[0].end=q(Number(raw));v.final.activeEndpoints[0].end=q(Number(raw))}assert.equal(compareWithRoot(a,b,{complete:true,oraclePassed:true},raw).status,'EQUAL_OBSERVED_PAIR')})
check('header matches sealed identity/limits/schema',()=>{const f=traceFixture(),a=validateTraceResult(f.config,f.verdict,f.trace);validateHeader(f.header,a)})
check('changed header identity/schema/limits refuse',()=>{for(const field of ['identity','schema','limits']){const f=traceFixture(),a=validateTraceResult(f.config,f.verdict,f.trace);if(field==='identity')f.header.identity={...f.header.identity,sourceCommit:'0'.repeat(40)};else if(field==='schema')f.header.schema='other';else f.header.limits.rawBytes++;assert.throws(()=>validateHeader(f.header,a))}})
check('widened self-described limits refuse',()=>{const f=traceFixture();f.trace.limits.rawBytes++;assert.throws(()=>validateTraceResult(f.config,f.verdict,f.trace),/sealed authority/)})
check('shard count and shard size limits independently refuse',()=>{const a=traceFixture();a.trace.shards=Array.from({length:33},(_,i)=>({path:'trace-'+String(i).padStart(3,'0')+'.jsonl.gz',bytes:1}));a.trace.compressedBytes=33;assert.throws(()=>validateTraceResult(a.config,a.verdict,a.trace),/shard count/);const b=traceFixture();b.trace.shards[0]!.bytes=b.config.trace.shardBytes+1;b.trace.compressedBytes=b.trace.shards[0]!.bytes;assert.throws(()=>validateTraceResult(b.config,b.verdict,b.trace),/shard name\/size/)})
function resources(phase:string):any{
 const limit={raw:'unlimited unlimited bytes',soft:'unlimited',hard:'unlimited',units:'bytes'}
 return {format:'mldr-3g-resource-observation/v1',phase,mode:'timed',workerPid:10,valid:true,observationOnly:true,collectorInvokedCandidateCode:false,platform:'linux',pidNamespace:{status:'OBSERVED',value:'pid:[100]'},affinity:{status:'OBSERVED',value:{count:16,cpuIds:Array.from({length:16},(_,i)=>i)}},memory:{requestedMiB:28672,requestedMeaning:'scheduler placement request, not an observed hard cap',perJobEnforcement:false,rlimits:{status:'OBSERVED',value:{addressSpace:limit,dataSize:limit,residentSet:limit}},cgroup:{status:'OBSERVED',value:{version:2,outsideVisibleMount:'UNKNOWN',limits:[{path:'/sys/fs/cgroup/memory.max',raw:'max'}]}}}}
}
check('observed unlimited memory is valid without a per-job cap',()=>assert.equal(validateResourcePair(resources('before'),resources('after'),'timed',10).perJobMemoryEnforcement,false))
check('missing observations or false enforcement claim refuse',()=>{const a=resources('before'),b=resources('after');a.memory.perJobEnforcement=true;assert.throws(()=>validateResourcePair(a,b,'timed',10));a.memory.perJobEnforcement=false;b.memory.cgroup.status='UNKNOWN';assert.throws(()=>validateResourcePair(a,b,'timed',10))})
check('protected-source check is after install and before driver import',()=>{const w=readFileSync(join(import.meta.dir,'worker.sh'),'utf8'),install=w.indexOf('install --frozen-lockfile'),guard=w.indexOf('> "$out/source-postinstall.json"'),driver=w.indexOf('"$entry/driver.ts"');assert(install>=0&&guard>install&&driver>guard)})

function oneConfig(v:any){return {source:{commit:v.identity.sourceCommit,tree:v.identity.sourceTree},profileSHA256:v.identity.profileSHA256,rootRaw:FIXTURE_ROOT_RAW,originalModelSHA256:v.modelSHA256,originalLawsSHA256:v.lawsSHA256}}
function oneFixture(){const v=fixture();v.error=null;v.phase='returned';return v}
function oneMeasurement(v:any){return {mode:'timed',rootCeilingRaw:FIXTURE_ROOT_RAW,totalCountedUnits:q(1),counterDeltas:copy(v.counterDeltas),observedWallNs:v.wallNs,wallMeaning:'OBSERVATION_ONLY',referenceConversion:{rhoNew:null},qualification:false,WClaim:false}}
check('S51 timed-only unknown is a measurement, not a proved pair',()=>{const v=oneFixture(),r=checkSingle(v,oneMeasurement(v),oneConfig(v),v.initial.weights);assert.equal(r.status,'VALID_TIMED_MEASUREMENT');assert.equal(r.verdict,'unknown');assert.equal(r.pairComparison,false)})
check('S51 changed public model/source and forged totals refuse',()=>{for(const field of ['modelSHA256','source']){const v=oneFixture(),c=oneConfig(v);if(field==='modelSHA256')v.modelSHA256='0'.repeat(64);else v.identity.sourceCommit='0'.repeat(40);assert.equal(checkSingle(v,oneMeasurement(v),c,v.initial.weights).status,'TIMED_MEASUREMENT_REJECTED')}const v=oneFixture(),m=oneMeasurement(v);m.totalCountedUnits=q(2);assert.equal(checkSingle(v,m,oneConfig(v),v.initial.weights).status,'TIMED_MEASUREMENT_REJECTED')})
check('S51 instrumented or changed frozen weights cannot masquerade as timed',()=>{const v=oneFixture();v.observerInstalled=true;assert.equal(checkSingle(v,oneMeasurement(v),oneConfig(v),v.initial.weights).status,'TIMED_MEASUREMENT_REJECTED');v.observerInstalled=false;const w=copy(v.initial.weights);w.fm=q(2);assert.equal(checkSingle(v,oneMeasurement(v),oneConfig(v),w).status,'TIMED_MEASUREMENT_REJECTED')})

console.log(JSON.stringify({syntheticControls:names.length,names,productionImports:false,nativeProofCalls:0,jobs:0}))
