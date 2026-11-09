// Research-only observation. No proof or policy is decided here.
import {mkdirSync,writeFileSync,renameSync} from 'node:fs'
import {fullWork,fullRate} from '../../../kernel/prove.ts'
type Row=Record<string,unknown>
let active=false,started=0,work=0,lastWrite=0,meta:Row={},last:Row={},leaf:Row={},excluded:number[]=[]
const snapshot=()=>({...meta,wallMs:performance.now()-started,countedUnits:(fullWork()-work)/fullRate,peakRssKiB:process.resourceUsage().maxRSS,last,leaf,excluded,excludedCount:excluded.length})
const flush=(force=false)=>{if(!active||!force&&performance.now()-lastWrite<1000)return;lastWrite=performance.now();const row=snapshot();writeFileSync('upper-output/progress.tmp',JSON.stringify(row));renameSync('upper-output/progress.tmp','upper-output/progress.json');console.log('UPPER_PROGRESS '+JSON.stringify(row))}
export const upperControl={
 start(value:Row){mkdirSync('upper-output',{recursive:true});active=true;started=performance.now();work=fullWork();meta=value;flush(true)},
 event(value:unknown){if(!active||!value||typeof value!=='object')return;const raw=value as Row,e=Object.fromEntries(Object.entries(raw).filter(([k])=>['stage','phase','pass','law','goal','outcome','reason','active','index','round','scope','path','excluded','violated','pending','cuts','end','ms','checked','proposed'].includes(k)).map(([k,v])=>[k,k==='goal'&&v&&typeof v==='object'?(v as Row).name:v]));last=e;if(e.stage==='upper-leaf-enter'){leaf=e;excluded=[]}if(Array.isArray(e.excluded))excluded=e.excluded.filter((x):x is number=>typeof x==='number');flush(e.stage==='upper-excluded'||e.stage==='closure-final')},
 push<T>(array:T[],...values:T[]){array.push(...values);for(const value of values)this.event(value);return array.length},
 finish(){flush(true);active=false;return snapshot()},
}
