// Passive research telemetry. No consumer means no row reconstruction or policy change.
import {type C} from '../machine.ts'
import {type Goal,type Path,leafConstraints,linear} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
export type FieldDemand={modelColumns:string[],coreColumns:string[],modelKnown:boolean,coreKnown:boolean,scope?:string}
export type FieldAttempt={candidate:C,cellColumns:string[],demand?:FieldDemand,units:number,emitted:boolean,source:string,requested:boolean|undefined,start?:number,end?:number,id?:number,parent?:number,inclusiveUnits?:number}
export const fieldAttemptObserver:{on?:(event:FieldAttempt)=>void}={}
const demands=new WeakMap<Path,FieldDemand>()
const scopeKey=(path:Path)=>JSON.stringify([...path].map(([key,atom])=>[key,atom.holds]).sort((a,b)=>String(a[0]).localeCompare(String(b[0]))))
type Attempt={candidate:C,path:Path,demand?:FieldDemand,source:string,start:number,children:number,id:number,parent?:Attempt}
let serial=0,current:Attempt|undefined
export function beginFieldAttempt(candidate:C,path:Path,demand:FieldDemand|undefined,source:string):Attempt|undefined{
 if(!fieldAttemptObserver.on)return
 const frame:Attempt={candidate,path:new Map(path),demand,source,start:clock(),children:0,id:serial++,parent:current};current=frame;return frame
}
export function endFieldAttempt(frame:Attempt|undefined,emitted:boolean):void{
 if(!frame)return
 const end=clock(),inclusive=end-frame.start;if(current!==frame)throw Error('field attempt stack mismatch');current=frame.parent;if(frame.parent)frame.parent.children+=inclusive
 recordFieldAttempt(frame.candidate,frame.path,frame.demand,Math.max(0,inclusive-frame.children),emitted,frame.source,{id:frame.id,parent:frame.parent?.id,start:frame.start,end,inclusiveUnits:inclusive})
}
export function observeFieldLeaf(goal:Goal,path:Path,result:{core?:number[],witness?:Record<string,number>}):void{
 if(!fieldAttemptObserver.on)return
 const selected=new Set(result.core),columns=new Set<string>()
 if(result.core)for(const row of leafConstraints(goal,path)){const source=row.src as {fact?:number}|undefined;if(source?.fact!==undefined&&selected.has(source.fact))for(const name of Object.keys(row.lin))if(name!=='1')columns.add(name)}
 demands.set(path,{scope:scopeKey(path),modelColumns:Object.keys(result.witness??{}),coreColumns:[...columns],modelKnown:result.witness!==undefined,coreKnown:result.core!==undefined})
}
export const fieldDemandAt=(path:Path):FieldDemand|undefined=>fieldAttemptObserver.on?demands.get(path):undefined
export function recordFieldAttempt(candidate:C,path:Path,demand:FieldDemand|undefined,units:number,emitted:boolean,source:string,span:Pick<FieldAttempt,'id'|'parent'|'start'|'end'|'inclusiveUnits'>={}):void{
 if(!fieldAttemptObserver.on)return
 const cell=candidate.op==='<='||candidate.op==='<'?(candidate.a.op==='if'?candidate.a.then:candidate.a):undefined
 const cellColumns=cell?Object.keys(linear(cell,path)??{}).filter(k=>k!=='1'):[],columns=new Set([...(demand?.coreColumns??[]),...(demand?.modelColumns??[])])
 const known=!!demand&&(demand.modelKnown||demand.coreKnown)&&(demand.scope===undefined||demand.scope===scopeKey(path))
 fieldAttemptObserver.on({candidate,cellColumns,demand,units,emitted,source,...span,requested:known?cellColumns.some(c=>columns.has(c)):undefined})
}
