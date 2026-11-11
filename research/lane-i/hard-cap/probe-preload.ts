type Point={at:number,stack:string}
let polls=0,reads=0,last:Point|undefined,maxGap=0,max:any,firstAbove:any,lastWall:any,end=Infinity
const walls:Record<string,{n:number,first:number,last:number,above:number}>={}
let sampled=0,nextSample=0
const groups=new Map<string,number>()
;(globalThis as any).__hardCapEval=(at:number)=>{
 if(at<nextSample)return
 nextSample=at+8192
 const site=(new Error().stack??'').split('\n').filter(l=>/core\/(infer|fresh|dsl)\.ts/.test(l)).slice(0,3).join('\n')
 groups.set(site,(groups.get(site)??0)+at-sampled);sampled=at
}
;(globalThis as any).__hardCapRead=(at:number)=>{
 reads++
 const stack=new Error().stack??''
 if(!/at (clock|checkBudget) \(/.test(stack))return
 polls++
 const current={at,stack}
 if(last&&at-last.at>maxGap){maxGap=at-last.at;max={units:maxGap,from:last,to:current,sampledSites:[...groups]} }
 groups.clear()
 last=current
 if(at>end&&!firstAbove)firstAbove={...current,lastWall,end}
}
;(globalThis as any).__hardCapWall=(phase:string,at:number,limit:number)=>{
 end=limit;lastWall={phase,at,end}
 const row=walls[phase]??={n:0,first:at,last:at,above:0};row.n++;row.last=at;if(at>end)row.above++
}
process.on('exit',()=>console.log('HARD_CAP_PROBE '+JSON.stringify({polls,reads,end,maxGap,max,firstAbove,walls})))
