type Point={at:number,stack:string}
let polls=0,reads=0,last:Point|undefined,maxGap=0,max:any,firstAbove:any,lastWall:any,end=Infinity
const walls:Record<string,{n:number,first:number,last:number,above:number}>={}
;(globalThis as any).__hardCapRead=(at:number)=>{
 reads++
 const stack=new Error().stack??''
 if(!/at (clock|checkBudget) \(/.test(stack))return
 polls++
 const current={at,stack}
 if(last&&at-last.at>maxGap){maxGap=at-last.at;max={units:maxGap,from:last,to:current}}
 last=current
 if(at>end&&!firstAbove)firstAbove={...current,lastWall,end}
}
;(globalThis as any).__hardCapWall=(phase:string,at:number,limit:number)=>{
 end=limit;lastWall={phase,at,end}
 const row=walls[phase]??={n:0,first:at,last:at,above:0};row.n++;row.last=at;if(at>end)row.above++
}
process.on('exit',()=>console.log('HARD_CAP_PROBE '+JSON.stringify({polls,reads,end,maxGap,max,firstAbove,walls})))
