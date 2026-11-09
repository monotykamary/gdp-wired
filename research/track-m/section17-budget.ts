// Research-only pooled draw. Sizes are positive AST-node counts, not priorities.
export const proportionalDraw=(remaining:number,size:number,totalSize:number):number=>{
 const r=Math.max(0,remaining)
 return size>0&&totalSize>=size?Math.min(r/3,r*(size/totalSize)):0
}
export function goalSize(value:unknown):number{
 if(!value||typeof value!=='object')return 0
 if(Array.isArray(value))return value.reduce((n,x)=>n+goalSize(x),0)
 const o=value as Record<string,unknown>
 return (typeof o.op==='string'?1:0)+Object.values(o).reduce<number>((n,x)=>n+goalSize(x),0)
}
