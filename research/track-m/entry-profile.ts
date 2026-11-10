// Research-only measurements; no production module imports this.
import {fullRate,fullWork} from '../../kernel/prove.ts'
import {realNow} from './without-deadlines.ts'
type Stat={calls:number,units:number,exclusiveUnits:number,wallMs:number,exclusiveWallMs:number}
type Frame={site:string,args:any[],units:number,wall:number,childrenUnits:number,childrenWall:number}
class EntryProfile{
 enabled=false;stack:Frame[]=[];sites=new Map<string,Stat>();interrupted:any;firstLeaf:any;actions:any[]=[]
 branches={activationNodes:0,activationCases:0,activeCases:0,inactiveCases:0,rowCases:0,naturalCalls:0,closureEntries:0,numericLeaves:0}
 beforeFirstLeaf:Record<string,number>={};private action:any
 beginAction(meta:any){this.enabled=true;this.action={meta,units:fullWork()/fullRate,wall:realNow(),firstLeafSeen:!!this.firstLeaf}}
 endAction(){if(!this.enabled)return;this.actions.push({...this.action,units:fullWork()/fullRate-this.action.units,wallMs:realNow()-this.action.wall});this.enabled=false}
 frame(kind:string,meta:any){if(!this.enabled)return;if(kind==='closure')this.branches.closureEntries++;if(kind==='leaf'){this.branches.numericLeaves++;if(!this.firstLeaf){this.beforeFirstLeaf={...this.branches};this.firstLeaf={units:fullWork()/fullRate-this.action.units,wallMs:realNow()-this.action.wall,path:meta.path,end:meta.end}}}}
 run<T>(site:string,args:any[],fn:()=>T):T{
  if(!this.enabled)return fn()
  if(!this.firstLeaf){if(site.endsWith('guard-cases.ts:visit'))this.branches.activationNodes++;if(site.endsWith('guard-cases.ts:leaf')){this.branches.activationCases++;this.branches[args[2]?'activeCases':'inactiveCases']++}if(site.endsWith('row-cases.ts:leaf'))this.branches.rowCases++;if(site.endsWith('natural-cases.ts:proveNaturalCases'))this.branches.naturalCalls++}
  const f:Frame={site,args,units:fullWork()/fullRate,wall:realNow(),childrenUnits:0,childrenWall:0};this.stack.push(f)
  try{return fn()}catch(e){
   if(!this.interrupted&&(e as any)?.name==='Error'&&String(e).includes('cap')){
    const source=[...this.stack].reverse().find(x=>x.args[0]?.hyps),rowQuery=[...this.stack].reverse().find(x=>x.site==='query.refuteFast'||x.site==='query.solve')
    this.interrupted={error:String(e),stack:this.stack.map(x=>({site:x.site,units:fullWork()/fullRate-x.units,wallMs:realNow()-x.wall})),packet:source?{goal:source.args[0],path:source.args[1] instanceof Map?[...source.args[1]]:source.args[1]}:undefined,rows:rowQuery?.args[0]}
   }throw e
  }finally{
   const units=fullWork()/fullRate-f.units,wallMs=realNow()-f.wall;this.stack.pop();const s=this.sites.get(site)??{calls:0,units:0,exclusiveUnits:0,wallMs:0,exclusiveWallMs:0};s.calls++;s.units+=units;s.exclusiveUnits+=units-f.childrenUnits;s.wallMs+=wallMs;s.exclusiveWallMs+=wallMs-f.childrenWall;this.sites.set(site,s);const parent=this.stack.at(-1);if(parent){parent.childrenUnits+=units;parent.childrenWall+=wallMs}
  }
 }
 snapshot(){return {actions:this.actions,firstLeaf:this.firstLeaf??null,branchesBeforeFirstLeaf:this.firstLeaf?this.beforeFirstLeaf:{...this.branches},branches:this.branches,functions:Object.fromEntries([...this.sites].sort((a,b)=>b[1].units-a[1].units)),interrupted:this.interrupted??null}}
}
export const entryProfile=new EntryProfile()
