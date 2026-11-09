// Pure display normalization only. Never infer a lemma's missing proof scope.
export function statement(e:any):{text:string,mentions:{op:boolean,guard:boolean,postState:boolean}}|null{
 const mentions={op:false,guard:false,postState:false}
 const term=(v:any):string=>{
  if(!v)return '?'
  if(v.op==='var'){if(v.name==='op')mentions.op=true;if(v.name.startsWith('?'))mentions.guard=true;return v.name}
  if(v.op==='flag'){mentions.guard=true;return '?'+v.name}
  if(v.op==='const')return String(v.value)
  if(v.op==='get'){if(v.map.endsWith('#'))mentions.postState=true;return v.map+'['+term(v.key)+']'}
  if(v.op==='if')return 'if('+term(v.c)+', '+term(v.then)+', '+term(v.else)+')'
  if(v.op==='and'||v.op==='or')return '('+v.xs.map(term).sort().join(v.op==='and'?' && ':' || ')+')'
  if(v.op==='not')return '!('+term(v.x)+')'
  if(v.op==='mul')return v.k+'*'+term(v.a)
  if(v.a!==undefined&&v.b!==undefined)return '('+term(v.a)+' '+v.op+' '+term(v.b)+')'
  throw new Error('unsupported statement expression: '+v.op)
 }
 if(e.bound||e.domain)return {text:term(e.bound??e.domain),mentions}
 if(e.inst&&e.reads?.every((r:any)=>!!r)){
  const reads=new Map(e.reads.map((r:any)=>[r[0],r])),parts=e.inst.terms.map(([k,id]:[number,string])=>{const r:any=reads.get(id);if(!r)throw new Error('missing read');return k+'*'+term({op:'get',map:r[1],key:r[2]})})
  if(e.inst.unit)parts.push(e.inst.unit+'*'+term(e.inst.below))
  return {text:parts.sort().join(' + ')+' <= 0',mentions}
 }
 return null
}
