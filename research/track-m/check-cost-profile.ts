// Research-only synchronous check profiler. The measured call always executes.
export type CheckCost={calls:number,totalMs:number,selfMs:number,maxMs:number}
const rows=new Map<string,CheckCost>(),stack:{started:number,children:number}[]=[]
export function profileCheck<T>(name:string,run:()=>T):T{
 const frame={started:performance.now(),children:0};stack.push(frame)
 try{return run()}finally{
  const elapsed=performance.now()-frame.started
  if(stack.pop()!==frame)throw Error('check profile stack mismatch')
  const parent=stack.at(-1);if(parent)parent.children+=elapsed
  const row=rows.get(name)??{calls:0,totalMs:0,selfMs:0,maxMs:0}
  row.calls++;row.totalMs+=elapsed;row.selfMs+=Math.max(0,elapsed-frame.children);row.maxMs=Math.max(row.maxMs,elapsed);rows.set(name,row)
 }
}
export const readCheckProfile=():Record<string,CheckCost>=>Object.fromEntries([...rows].map(([k,v])=>[k,{...v}]))
