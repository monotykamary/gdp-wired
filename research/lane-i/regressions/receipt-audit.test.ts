import {test,expect} from 'bun:test'
import {gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {auditPair,baseline,candidate,parseReceipts,type Pair} from './receipt-audit.ts'
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
function fixture():Pair{
 const results=[{id:'consensus_forall',search:{verdict:'proven',ms:9}}],profile=[{event:'result'}],stdout=JSON.stringify(results[0]),stderr='LANE_I_PROFILE '+JSON.stringify(profile[0])
 const outcome={exit:0,wallMs:10,results,profile,attempts:[],stdoutSha256:hash(stdout),stderrSha256:hash(stderr),traceGzipBase64:gzipSync(stdout+'\n---stderr---\n'+stderr).toString('base64')}
 return{group:1,repeat:1,cpu:'AMD Ryzen 9 9950X 16-Core Processor',strictMs:60000,meta:{base:{revision:baseline,clean:true},candidate:{revision:candidate,clean:true}},outcomes:{base:structuredClone(outcome),candidate:structuredClone(outcome)}}
}
test('explicit source identities are required and do not relax historical defaults',()=>{const pair=fixture(),sources={baseline:'a'.repeat(40),candidate:'b'.repeat(40)};pair.meta.base.revision=sources.baseline;pair.meta.candidate.revision=sources.candidate;expect(auditPair(pair,'strict',1,sources).issues).toEqual([]);expect(auditPair(pair,'strict',1).issues).toContain('base: source mismatch');pair.meta.candidate.revision=baseline;expect(auditPair(pair,'strict',1,sources).issues).toContain('candidate: source mismatch')})
test('an intact strict pair passes, but wrong CPU, source, or original budget fails',()=>{
 const pair=fixture();expect(auditPair(pair,'strict',1).issues).toEqual([])
 pair.cpu='another CPU';pair.strictMs=120000;pair.meta.candidate.revision=baseline
 expect(auditPair(pair,'strict',1).issues).toEqual(expect.arrayContaining(['wrong strict CPU','non-original time budget','candidate: source mismatch']))
})
test('compressed trace corruption and semantic omissions cannot pass',()=>{
 const pair=fixture();pair.outcomes.base.stderrSha256='0'.repeat(64);pair.outcomes.candidate.results=[]
 expect(auditPair(pair,'strict',1).issues).toEqual(expect.arrayContaining(['base: stderr hash mismatch','candidate: missing/duplicate semantic result']))
 pair.outcomes.base.traceGzipBase64='not gzip';expect(auditPair(pair,'strict',1).issues).toContain('base: invalid compressed trace')
})
test('an unmodified trace cannot support a changed semantic summary',()=>{
 const pair=fixture();pair.outcomes.candidate.results![0]!.search.verdict='unknown'
 expect(auditPair(pair,'strict',1).issues).toContain('candidate: semantic result differs from trace')
 pair.outcomes.base.attempts=[{law:'invented',units:3,wallMs:1}]
 expect(auditPair(pair,'strict',1).issues).toContain('base: per-law work differs from trace')
})
test('bar answers are derived from the retained raw stages',()=>{
 const pair=fixture();pair.index=0;pair.view='its';pair.strictSeconds=60
 for(const side of ['base','candidate'] as const){
  const out=pair.outcomes[side],stages=[{stage:'answer',answer:'terminates'}],stdout=JSON.stringify(stages[0])
  out.answer='terminates';out.stages=stages;out.trackedChanges='';out.stdoutSha256=hash(stdout);out.stderrSha256=hash('');out.traceGzipBase64=gzipSync(stdout+'\n---stderr---\n').toString('base64')
 }
 expect(auditPair(pair,'bar',0).issues).toEqual([])
 pair.outcomes.candidate.answer='unknown'
 expect(auditPair(pair,'bar',0).issues).toContain('candidate: answer differs from trace')
})
test('nonmatching CPU skips never become paired runs',()=>{
 const parsed=parseReceipts('STRICT_CPU_SKIP '+JSON.stringify({group:1,cpu:'another CPU'}),'strict',1)
 expect(parsed.issues).toEqual([]);expect(parsed.pairs).toHaveLength(0);expect(parsed.skips).toHaveLength(1)
 expect(parseReceipts('','strict',1).issues).toContain('expected exactly three paired repeats')
})
test('missing, duplicate and mixed skip/result records are rejected',()=>{
 const rows=[1,2,3].map(repeat=>'STRICT_PAIR '+JSON.stringify({...fixture(),repeat})).join('\n')
 expect(parseReceipts(rows,'strict',1).issues).toEqual([])
 expect(parseReceipts(rows+'\nSTRICT_PAIR '+JSON.stringify(fixture()),'strict',1).issues).toContain('duplicate repeat 1')
 expect(parseReceipts(rows+'\nSTRICT_CPU_SKIP '+JSON.stringify({group:1,cpu:'another CPU'}),'strict',1).issues).toContain('mixed or duplicate CPU skip')
})
