// Untrusted structural proposal only. A successful proposal must reindex the
// entire existing proof; native validation remains with the accepting caller.
export function pruneOwnedRoot<T,P>(input:readonly T[],proof:P,propose:(kept:T[],proof:P)=>P|undefined,more:()=>boolean=()=>true):{kept:T[],proof:P,attempts:number}{
 let kept=[...input],current=proof,attempts=0
 const visit=(group:T[]):void=>{
  if(!group.length||!more())return
  const live=group.filter(item=>kept.includes(item));if(!live.length)return
  const short=kept.filter(item=>!live.includes(item));attempts++
  const next=propose(short,current)
  if(next!==undefined){kept=short;current=next;return}
  if(live.length>1){const mid=Math.floor(live.length/2);visit(live.slice(0,mid));visit(live.slice(mid))}
 }
 visit([...input]);return {kept,proof:current,attempts}
}
