// Research-only generation attribution. A missing final proof is not evidence
// that any generator is dispensable.
type Stat={calls:number,ms:number,produced:number,names:string[]}
export const generatorStats:Record<string,Stat>={}
export function generatorCall<T>(name:string,f:()=>T):T{
 if(process.env.TRACK_M_GENERATORS_PROFILE!=='1')return f()
 const start=performance.now(),out=f(),ms=performance.now()-start
 const values=Array.isArray(out)?out:[]
 const stat=generatorStats[name]??(generatorStats[name]={calls:0,ms:0,produced:0,names:[]})
 stat.calls++;stat.ms+=ms;stat.produced+=values.length
 stat.names.push(...values.flatMap(v=>typeof v?.name==='string'?[v.name]:[]).slice(0,500))
 return out
}
