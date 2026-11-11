// Disposable diagnostics: record counted reads; never change admission or charge.
export {}
type Point={at:number,stack:string,raw:any}
let last:Point|undefined,rootEnd:number|undefined,rootStart:number|undefined,polls=0,nextSample=0,firstAbove:any
const top:any[]=[],sites=new Map<string,number>()
;(globalThis as any).__gapBudget=(end:number|undefined)=>{if(end!==undefined&&rootEnd===undefined){rootEnd=end;rootStart=last?.at}}
;(globalThis as any).__gapEval=(at:number)=>{if(at<nextSample)return;nextSample=at+4096;const stack=(new Error().stack??'').split('\n').filter(s=>/\/(core|kernel)\//.test(s)&&!s.includes('work-observe.ts')).slice(0,7).join('\n');sites.set(stack,(sites.get(stack)??0)+1)}
;(globalThis as any).__gapRead=(at:number,raw:any)=>{
 const stack=new Error().stack??''
 if(!/at (clock|checkBudget|checkWorkEndpoint|checkWorkAdmission|remainingWork|late|pastWall) \(/.test(stack))return
 polls++;const point={at,stack,raw}
 if(last){const gap={units:at-last.at,from:last,to:point,samples:[...sites]};if(gap.units>1024){top.push(gap);top.sort((a,b)=>b.units-a.units);if(top.length>32)top.length=32}if(rootEnd!==undefined&&at>rootEnd&&!firstAbove)firstAbove={rootEnd,rootStart,gap}}
 sites.clear();last=point
}
let nextTableSample=0
;(globalThis as any).__gapTable=(at:number)=>{if(at<nextTableSample)return;nextTableSample=at+4096;const stack='table: '+(new Error().stack??'').split('\n').filter(s=>/\/(core|kernel)\//.test(s)).slice(0,8).join('\n');sites.set(stack,(sites.get(stack)??0)+1)}
process.on('exit',()=>console.log('CAP_GAP_PROBE '+JSON.stringify({polls,rootEnd,rootStart,firstAbove,top})))
