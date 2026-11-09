// Deduplicate shared Goal objects without changing certificate column names.
export function pack(data:any):string{
 const goals:any[]=[],ids=new Map<object,number>()
 const body=JSON.stringify(data,(_k,v)=>{if(v&&typeof v.name==='string'&&Array.isArray(v.hyps)){let id=ids.get(v);if(id===undefined){id=goals.length;goals.push(v);ids.set(v,id)}return {$goal:id}}return v})
 return '{"data":'+body+',"goals":'+JSON.stringify(goals)+'}\n'
}
export function unpack(text:string):any{const x=JSON.parse(text);if(!x.goals)return x;const go=(v:any):any=>{if(!v||typeof v!=='object')return v;if(Object.keys(v).length===1&&typeof v.$goal==='number'){if(!x.goals[v.$goal])throw Error('invalid goal reference');return x.goals[v.$goal]}if(Array.isArray(v))return v.map(go);return Object.fromEntries(Object.entries(v).map(([k,v])=>[k,go(v)]))};return go(x.data)}
