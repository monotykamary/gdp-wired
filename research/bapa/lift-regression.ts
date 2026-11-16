// Regression custody only. No protocol selection, proof search or Lean generation.
import {createHash} from 'node:crypto'
import {lstatSync,readFileSync,readdirSync,realpathSync} from 'node:fs'
import {isAbsolute,join,resolve,sep} from 'node:path'
export const hash=(data:string|Uint8Array)=>createHash('sha256').update(data).digest('hex')
export function assert(ok:unknown,message:string):asserts ok {if(!ok)throw Error(message)}
export const hashFile=(path:string)=>hash(readFileSync(path))
export const json=<T>(path:string):T=>JSON.parse(readFileSync(path,'utf8')) as T
export type Evidence={path:string;sha256:string}
export type Input={id:string;capture:{path:string;origin:string;sha256:string};baselineDirectory:string;sourceScope:'frozen-capsule-original'|'current-accepted-source';familyTheorem?:string;sourceTheorems?:string[];baselineSource?:{machine:string;laws:string}|{combined:string}}
export type Entry=Input&{source:{path:string;sha256:string|null;publicLawNames:string[]|null;status:'PENDING'|'FROZEN';historicalEncodedSourceMatches?:boolean;provenance?:Evidence};baseline:{receipt:Evidence;emission:Evidence|null;logs:Evidence[];familyTheorem:string;sourceTheorems:string[];axioms:Record<string,string[]>};pending:string[]}
export type Manifest={schema:'gdp-lift-regression/v1';allSizesProven:false;scope:string;independentTlaVerification:false;entries:Entry[]}
export function sameSet(actual:string[],expected:string[],label:string){assert(new Set(actual).size===actual.length,label+': duplicate');assert(JSON.stringify([...actual].sort())===JSON.stringify([...expected].sort()),label+': exact set differs')}
export function checkEmission(e:Entry,m:any,sourceHash:string){
  assert(m.schema==='gdp-lift-emission/v1'&&m.status==='EMITTED_NOT_CHECKED','not a product emission')
  assert(m.capsuleSha256===e.capture.sha256&&m.sourceSha256===sourceHash&&m.sourceId===e.id,'emission input binding mismatch')
  assert(m.allSizesProven===false&&m.leanExecuted===false,'emission misstates acceptance')
  assert(m.familyTheorem===e.baseline.familyTheorem,'baseline family theorem changed')
  const actual:string[]=m.sourceProjection?.sourceTheorems??[]
  assert(actual.length===e.source.publicLawNames?.length&&new Set(actual).size===actual.length,'per-law source coverage differs')
  assert(actual.every(name=>e.baseline.sourceTheorems.includes(name)),'source theorem not in exact historical baseline')
  // Older alpha receipts counted the aggregate source_laws alongside per-law
  // theorems. Preserve its name and axiom check without pretending it is a law.
  for(const name of e.baseline.sourceTheorems)assert(m.requiredTheorems.includes(name),'missing historical source theorem '+name)
  assert(JSON.stringify(m.sourceProjection?.publicLawNames)===JSON.stringify(e.source.publicLawNames),'public law coverage changed')
  for(const name of [m.familyTheorem,...m.sourceProjection.sourceTheorems])assert(m.requiredTheorems.includes(name),'missing required theorem '+name)
}
export function verifyFiles(directory:string,files:Record<string,string>){
  assert(Object.keys(files).length>0,'empty emitted project')
  const root=realpathSync(directory)
  for(const [name,digest]of Object.entries(files)){
    const path=resolve(directory,name)
    assert(!isAbsolute(name)&&path.startsWith(resolve(directory)+sep)&&/^[a-f0-9]{64}$/.test(digest),'unsafe emitted file/hash')
    const stat=lstatSync(path)
    assert(stat.isFile()&&!stat.isSymbolicLink()&&realpathSync(path).startsWith(root+sep),'non-regular emitted file')
    assert(hashFile(path)===digest,'emitted file changed: '+name)
  }
}
// Hash the actual uploaded implementation, including untracked in-progress files.
// No inference that a commit ID alone contains the code that was checked.
export function implementationFiles(root:string):Record<string,string>{
  const files:Record<string,string>={}
  function walk(relative:string){for(const name of readdirSync(join(root,relative)).sort()){
    if(name==='node_modules'||name==='.lake'||name==='.git'||name==='runs')continue
    const rel=join(relative,name),stat=lstatSync(join(root,rel))
    assert(!stat.isSymbolicLink(),'symlink in implementation inventory: '+rel)
    if(stat.isDirectory())walk(rel)
    else if(stat.isFile()&&(/\.(ts|lean|json)$/.test(name)||name==='lean-toolchain'))files[rel]=hashFile(join(root,rel))
  }}
  walk('core');walk('kernel');walk('lean-kernel')
  for(const name of readdirSync(join(root,'research/bapa')).sort())if(/^lift-regression.*\.(ts|json)$/.test(name))files['research/bapa/'+name]=hashFile(join(root,'research/bapa',name))
  for(const path of ['package.json','bun.lock','bun.lockb','scripts/gen-lean-library.ts']){try{files[path]=hashFile(join(root,path))}catch(e){if((e as NodeJS.ErrnoException).code!=='ENOENT')throw e}}
  return files
}
