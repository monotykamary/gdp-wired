// Static audit only: no model imports, proof calls, TLC, or external solver.
import {readdirSync, readFileSync, statSync, existsSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {resolve, dirname} from 'node:path';
import {gzipSync} from 'node:zlib';
const output: string[] = []; const print = console.log; console.log = (...xs: unknown[]) => { output.push(xs.map(String).join(' ')); };
const sha = (s: string | Buffer) => createHash('sha256').update(s).digest('hex');
const files: string[] = [];
function walk(p: string) { for (const n of readdirSync(p).sort()) { const f = `${p}/${n}`; if (statSync(f).isDirectory()) walk(f); else files.push(f); } }
walk('core'); walk('kernel');
const texts = new Map(files.map(f => [f,readFileSync(f,'utf8')]));
const models = readFileSync('research/protocols/ic3syn/models.ts','utf8');
// Includes both arms of conditional identifiers and every file/ic3syn literal, without executing models.
const region = models.slice(models.indexOf('export const protocols'));
const tokens = new Set<string>(['paxos','mldr','mongo','raft','quorum','leader','election','consensus','tcommit','twophase','two_phase','lockserv','lock_server','sharded','firewall','learning_switch','client_server']);
for (const m of region.matchAll(/(?:id|ic3syn|file):\s*([^,\n]+)/g)) for (const v of m[1]!.matchAll(/'([^']+)'/g)) { tokens.add(v[1]!); tokens.add(v[1]!.replace(/\.(tla|pyv)$/,'')); for(const t of v[1]!.split(/[_\-.]/)) if(t.length>=4) tokens.add(t); }
const esc=(x:string)=>x.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
const nameRe = new RegExp([...tokens].sort((a,b)=>b.length-a.length).map(esc).join('|'),'ig');
const groups: Record<string, RegExp> = {
  names: nameRe,
  knobs: /(?:process\??\.?|Bun\.)env|\b(?:env|knobs)\s*(?:\.|\[)|GDP_[A-Z_0-9]+/g,
  io: /readFile|readText|Bun\.file|node:fs|from ['"]fs|require\(['"]fs|fetch\(|Deno\.|child_process|spawn\(|execSync\(|import\(|require\(/g,
  shape: /scan.prefix|carry law|hand.writ|hard.cod|special.cas|protocol|\b(?:OneA|OneB|Left|Proposal|Vote|Decision|CfgT|Config|CT|St|Primary|Secondary|QuorumsOverlap)\b|majority|intersection|overlap|support.*(?:bound|const)|(?:bound|const).*support/ig,
  laws: /\.law\(|\blaws\s*[:=]|\b(?:candidate|template|seed|lemma|invariant|name)\b.*(?:===|includes\(|startsWith\(|endsWith\(|test\()|(?:===|includes\(|startsWith\(|endsWith\(|test\().*\b(?:name|map)\b/g,
};
const imports: Record<string,string[]> = {};
for(const [f,t] of texts) { imports[f]=[]; for(const m of t.matchAll(/(?:from\s*|import\s*\(|import\s*)['"]([^'"]+)['"]/g)) if(m[1]!.startsWith('.')) { const p=resolve(dirname(f),m[1]!).replace(resolve('.')+'/',''); if(existsSync(p)) imports[f].push(p); } }
const reach=new Set<string>(); function visit(f:string) {if(reach.has(f))return;reach.add(f); for(const p of imports[f]??[])visit(p)} visit('core/dsl.ts');
console.log('AUDIT_STATIC_V1'); console.log('SCRIPT_SHA256',sha(readFileSync(import.meta.path))); console.log('MODELS_SHA256',sha(models)); console.log('TOKENS',JSON.stringify([...tokens].sort())); console.log('MANIFEST',JSON.stringify([...texts].map(([f,t])=>[f,sha(t)]))); console.log('REACHABLE_IMPORT_GRAPH',JSON.stringify([...reach].sort().map(f=>[f,imports[f]??[]])));
for(const [group,re] of Object.entries(groups)) {if(process.env.AUDIT_SECTION && process.env.AUDIT_SECTION!==group)continue;console.log('\nSECTION',group); let count=0;for(const [f,t] of texts) for(const [i,l] of t.split('\n').entries()){re.lastIndex=0;if(!re.test(l))continue;count++; console.log(`${f}:${i+1}:${reach.has(f)?'IMPORT-CLOSURE':'OUTSIDE-CLOSURE'}:${l.slice(0,600)}`)} console.log('COUNT',group,count)}
console.log('\nSECTION proof-path-anchors');
for(const f of ['research/protocols/ic3syn/run.ts','core/counts.ts','core/infer.ts','core/solver.ts','core/check.ts','kernel/prove.ts','kernel/kernel.ts','kernel/epr.ts']) {const t=readFileSync(f,'utf8');console.log('FILE_SHA256',f,sha(t));for(const [i,l] of t.split('\n').entries())if(/certOn|checkReport|checked|checkCount|export (function|const) (prove|check)|GDP_|check\(|function proveSetFast|function proveLaws/.test(l))console.log(`${f}:${i+1}:${l}`)}
if(process.env.AUDIT_SECTION==='census') {
 console.log('SECTION CENSUS'); const knobs=new Map<string,string[]>(); const closures=[...reach].sort(); console.log('CLOSURE_FILES',JSON.stringify(closures));
 for(const [f,t]of texts)for(const [i,l]of t.split('\n').entries())for(const m of l.matchAll(/\b(?:env|knobs)\.([A-Z][A-Z_0-9]+)/g)){const key=m[1]!; const rows=knobs.get(key)??[];rows.push(`${f}:${i+1}:${reach.has(f)?'PATH':'OUTSIDE'}`);knobs.set(key,rows)}
 for(const [k,rs]of [...knobs].sort((a,b)=>a[0].localeCompare(b[0])))console.log('KNOB',k,[...new Set(rs)].join(','));
 const ownLaws=[...new Set([...models.matchAll(/(?:\.law|\bone)\('([^']+)'/g)].map(m=>m[1]!))]; console.log('LAW_NAMES',JSON.stringify(ownLaws));
 for(const [f,t]of texts)for(const [i,l]of t.split('\n').entries())if(ownLaws.some(n=>l.includes(n)))console.log('LAW_NAME_HIT',`${f}:${i+1}:${reach.has(f)?'PATH':'OUTSIDE'}`,l.slice(0,600));
 console.log('KNOB_COUNT',knobs.size,'PATH_KNOB_COUNT',[...knobs].filter(([,rs])=>rs.some(r=>r.endsWith(':PATH'))).length);
}
console.log('COMPLETE',files.length,'files');
print('AUDIT_GZIP_BASE64_BEGIN'); print(gzipSync(output.join('\n')+'\n').toString('base64')); print('AUDIT_GZIP_BASE64_END');
