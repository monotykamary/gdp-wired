// Research-only model guidance. A model chooses a branch order, never a fact.
import {type E} from '../../core/machine.ts'
import {type Path,linear,truth} from '../../kernel/kernel.ts'
type Probe={point?:Record<string,number>,sources?:string[]}
const stack:Probe[]=[]
export const rowProbeStats={queries:0,cacheHits:0,mirrorHits:0,probes:0,splits:0,rootClosures:0,terminalCalls:0,fallbacks:0,maxDepth:0}
export const rowProbe={
 get active(){return stack.length>0},
 remember(point:Record<string,number>,sources:string[]){const top=stack.at(-1);if(top){top.point={...point};top.sources=[...sources]}},
 run<T>(run:()=>T):Probe&{value:T}{const probe:Probe={};stack.push(probe);try{const value=run();return {...probe,value}}finally{stack.pop()}}
}
export function chooseRowPair(pairs:readonly (readonly [E,E])[],path:Path,point:Record<string,number>|undefined,sources:readonly string[]=[]):number|undefined{
 if(!point)return undefined
 const value=(e:E):number|undefined=>{
  if(e.op==='var'&&Number.isFinite(point[e.name]))return point[e.name]
  const lin=linear(e,path);if(!lin)return undefined;let out=0
  for(const [name,coefficient]of Object.entries(lin)){const n=name==='1'?1:point[name];if(!Number.isFinite(n))return undefined;out+=coefficient*n!}return Number.isFinite(out)?out:undefined
 }
 const candidates=pairs.flatMap((pair,index)=>{
  if(truth({op:'=',a:pair[0],b:pair[1]},path)!==undefined)return[]
  const a=value(pair[0]),b=value(pair[1]);if(a===undefined||b===undefined)return[]
  return[{index,equal:a===b,relevant:pair[0].op==='var'&&sources.includes(pair[0].name)}]
 })
 return candidates.find(c=>c.equal&&c.relevant)?.index??candidates.find(c=>c.relevant)?.index??candidates.at(-1)?.index
}
