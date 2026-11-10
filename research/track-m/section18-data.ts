// Research comparison only: never rewrite proof goals or alpha-rename free keys.
// Canonical integer-linear comparison, including strict bounds and common factors.
export function inequalityKey(c:any):string{
 if(c.op!=='<'&&c.op!=='<=')throw Error('expected an integer inequality')
 const terms=new Map<string,number>()
 const add=(e:any,k:number):void=>{if(e.op==='add'){add(e.a,k);add(e.b,k)}else if(e.op==='mul')add(e.a,k*e.k);else{const key=e.op==='const'?'':JSON.stringify(e);terms.set(key,(terms.get(key)??0)+k*(e.op==='const'?e.value:1))}}
 add(c.a,1);add(c.b,-1);if(c.op==='<')terms.set('',(terms.get('')??0)+1)
 const entries=[...terms].filter(([,n])=>n!==0).sort(([a],[b])=>a.localeCompare(b))
 const gcd=(a:number,b:number):number=>b?gcd(b,a%b):Math.abs(a)
 if(entries.some(([,n])=>!Number.isSafeInteger(n)))throw Error('non-exact comparison coefficient')
 const divisor=entries.reduce((g,[,n])=>gcd(g,n),0)||1
 return JSON.stringify(entries.map(([a,n])=>[a,n/divisor]))
}
export function normalize(value:any,reads:any[]=[],decode:(s:string)=>any=()=>undefined):any{
 const map=new Map(reads.map(r=>[r[0],{op:'get',map:r[1],key:r[2]}]))
 const visit=(v:any,seen=new Set<string>()):any=>{
  if(!v||typeof v!=='object')return v
  if(Array.isArray(v))return v.map(x=>visit(x,seen))
  if(v.op==='var'&&!seen.has(v.name)){const e=map.get(v.name)??decode(v.name);if(e)return visit(e,new Set([...seen,v.name]))}
  const out=Object.fromEntries(Object.keys(v).sort().map(k=>[k,visit(v[k],seen)]))
  if(['and','or'].includes(v.op))out.xs.sort((a:any,b:any)=>JSON.stringify(a).localeCompare(JSON.stringify(b)))
  return out
 };return visit(value)
}
export function dependence(value:any,state:string[]=[]):{op:boolean,guard:boolean,postState:boolean}{
 const out={op:false,guard:false,postState:false};const go=(v:any)=>{if(!v||typeof v!=='object')return;if(v.op==='var'){out.op ||= v.name==='op';out.guard ||= v.name.startsWith('?');out.postState ||= state.some(s=>v.name===s+'#')}if(v.op==='flag')out.guard=true;if(v.op==='get')out.postState ||= v.map.endsWith('#');Object.values(v).forEach(go)};go(value);return out
}
export const independent=(x:{op:boolean,guard:boolean,postState:boolean})=>!x.op&&!x.guard&&!x.postState
