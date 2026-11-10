// Hooks installed only into disposable research copies, never production.
export const shardControl:{mode:'off'|'capture'|'run',op:number,context:any,capture:(x:any)=>void,finish:(record:any,context:any)=>void,query:<T>(packet:any,run:()=>T)=>T}={mode:'off',op:-1,context:{},capture:()=>{},finish:()=>{},query:(_packet,run)=>run()}
