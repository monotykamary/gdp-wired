// UNTRUSTED candidate index. Minimum-id representatives; direct ITE/guard nodes are opt-in.
// No proposed equality or binding constitutes a kernel certificate.
import type {C,E} from '../../core/machine.ts'
import {Exhausted,Meter,type Binding} from './match.ts'
type Term=E|C
function expression(e:Term):e is E {
  switch(e.op){
    case '=':case '<':case '<=':case 'and':case 'or':case 'not':case 'flag':case 'all':return false
    case 'var':case 'const':case 'get':case 'mul':case 'proj':case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':case 'if':return true
  }
}
function parts(e:Term,nativeIte:boolean):[string,Term[]]{
  switch(e.op){
    case 'var':return [JSON.stringify(['var',e.name]),[]]
    case 'const':return [JSON.stringify(['const',e.value]),[]]
    case 'get':return [JSON.stringify(['get',e.map]),[e.key]]
    case 'mul':case 'proj':return [JSON.stringify([e.op,e.k]),[e.a]]
    case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':return [e.op,[e.a,e.b]]
    case 'if':if(!nativeIte)throw Error('unsupported e-term: if');return ['if',[e.c,e.then,e.else]]
    case '=':case '<':case '<=':if(!nativeIte)throw Error('unexpected condition node');return [JSON.stringify(['guard',e.op]),[e.a,e.b]]
    case 'not':if(!nativeIte)throw Error('unexpected condition node');return [JSON.stringify(['guard','not']),[e.x]]
    case 'and':case 'or':if(!nativeIte)throw Error('unexpected condition node');return [JSON.stringify(['guard',e.op]),e.xs]
    case 'flag':case 'all':throw Error(`unsupported ITE condition: ${e.op}`)
  }
}
type Node={term:Term,head:string,children:number[]}
export class IndexedEGraph {
  private nodes:Node[]=[]
  private parent:number[]=[]
  private signatures=new Map<string,number>()
  private dirty=false
  private byHead=new Map<string,Map<number,number[]>>()
  private indexed=false
  readonly stats={phase:'conversion',lookups:0,rebuildPasses:0,matchingCandidates:0,conditionNodes:0,iteNodes:0,merges:0,hypothesesCompleted:0}
  get size(){return this.nodes.length}
  constructor(readonly meter:Meter,readonly maxNodes=512,readonly nativeIte=false){if(!Number.isSafeInteger(maxNodes)||maxNodes<0)throw Error('invalid node limit')}
  root(id:number):number{this.meter.tick();while(this.parent[id]!==id){this.meter.tick();id=this.parent[id]!}return id}
  private signature(head:string,children:number[]):string{this.meter.tick();return JSON.stringify([head,...children.map(c=>this.root(c))])}
  add(term:E):number{if(this.dirty)this.rebuild();return this.intern(term)}
  private intern(term:Term):number{
    this.stats.phase='intern';this.meter.tick()
    const [head,terms]=parts(term,this.nativeIte),children=terms.map(t=>this.intern(t)),key=this.signature(head,children)
    this.meter.tick();this.stats.lookups++;const old=this.signatures.get(key)
    if(old!==undefined)return this.root(old)
    if(this.nodes.length>=this.maxNodes)throw new Exhausted('e-node limit')
    if(!expression(term))this.stats.conditionNodes++;if(term.op==='if')this.stats.iteNodes++;
    const id=this.nodes.length;this.nodes.push({term,head,children});this.parent.push(id);this.signatures.set(key,id);this.indexed=false;return id
  }
  merge(a:number,b:number):boolean{
    this.meter.tick();a=this.root(a);b=this.root(b);if(a===b)return false
    this.parent[Math.max(a,b)]=Math.min(a,b);this.stats.merges++;this.dirty=true;this.indexed=false;return true
  }
  rebuild(){
    this.stats.phase='rebuild'
    // A merge can invalidate earlier signatures; repeat until an entire pass is stable.
    do{
      this.stats.rebuildPasses++;this.dirty=false
      const table=new Map<string,number>()
      for(let i=0;i<this.nodes.length;i++){
        this.meter.tick();const node=this.nodes[i]!,key=this.signature(node.head,node.children)
        this.meter.tick();const previous=table.get(key)
        if(previous===undefined)table.set(key,i);else this.merge(i,previous)
      }
      this.signatures=table
    }while(this.dirty)
  }
  seed(cs:C[],equalityFirst=false){
    // Schedule only already-asserted top-level positive equalities early. Every
    // hypothesis is still traversed below; no nodes are discarded or hidden.
    if(equalityFirst){
      const early=(c:C):void=>{
        this.meter.tick()
        if(c.op==='and')c.xs.forEach(early)
        else if(c.op==='='){const a=this.add(c.a),b=this.add(c.b);this.merge(a,b)}
      }
      cs.forEach(early)
    }
    const equalities:[number,number][]=[]
    const read=(c:C,positive:boolean):void=>{
      this.meter.tick()
      switch(c.op){
        case '=':case '<':case '<=':{const a=this.add(c.a),b=this.add(c.b);if(positive&&c.op==='=')equalities.push([a,b]);return}
        case 'and':c.xs.forEach(x=>read(x,positive));return
        case 'or':c.xs.forEach(x=>read(x,false));return
        case 'not':read(c.x,false);return
        case 'flag':case 'all':throw Error(`unsupported e-condition: ${c.op}`)
      }
    }
    cs.forEach(c=>{read(c,true);this.stats.hypothesesCompleted++});this.stats.phase='equalities'
    for(const [a,b]of equalities)this.merge(a,b)
    this.rebuild();this.stats.phase='seeded'
  }
  private index(){
    if(this.dirty)this.rebuild()
    if(this.indexed)return
    this.byHead.clear()
    for(let i=0;i<this.nodes.length;i++){
      this.meter.tick();const head=this.nodes[i]!.head,root=this.root(i)
      let classes=this.byHead.get(head);if(!classes){classes=new Map();this.byHead.set(head,classes)}
      const members=classes.get(root);if(members)members.push(i);else classes.set(root,[i])
    }
    this.indexed=true
  }
  private *at(pattern:Term,id:number,variables:Set<string>,env:Binding):Generator<Binding>{
    this.meter.tick();id=this.root(id)
    if(pattern.op==='var'&&variables.has(pattern.name)){
      if(!expression(this.nodes[id]!.term))return
      const old=env.get(pattern.name);if(old===undefined||this.root(old)===id)yield new Map([...env,[pattern.name,id]])
      return
    }
    const [head,children]=parts(pattern,this.nativeIte)
    for(const i of this.byHead.get(head)?.get(id)??[]){
      this.meter.tick();this.stats.matchingCandidates++;const node=this.nodes[i]!;let envs=[env]
      for(let k=0;k<children.length;k++){
        const next:Binding[]=[]
        for(const e of envs)for(const found of this.at(children[k]!,node.children[k]!,variables,e))next.push(found)
        envs=next
      }
      yield* envs
    }
  }
  match(patterns:E[],keys:string[],maxMatches=32,accept?:(binding:Record<string,E>)=>boolean):Record<string,E>[]{
    if(!Number.isSafeInteger(maxMatches)||maxMatches<0)throw Error('invalid match limit')
    if(!maxMatches)return []
    this.index();this.stats.phase='matching'
    const variables=new Set(keys),found:Record<string,E>[]=[],seen=new Set<string>()
    const roots=patterns.map(p=>{
      const ids:number[]=[]
      if(p.op==='var'&&variables.has(p.name)){for(let i=0;i<this.nodes.length;i++){this.meter.tick();if(this.root(i)===i)ids.push(i)}}
      else for(const id of this.byHead.get(parts(p,this.nativeIte)[0])?.keys()??[]){this.meter.tick();ids.push(id)}
      return ids.sort((a,b)=>{this.meter.tick();return a-b})
    })
    const join=function*(this:IndexedEGraph,k:number,env:Binding):Generator<Binding>{
      this.meter.tick();if(k===patterns.length){yield env;return}
      for(const id of roots[k]!)for(const e of this.at(patterns[k]!,id,variables,env))yield* join.call(this,k+1,e)
    }
    for(const env of join.call(this,0,new Map())){
      this.meter.tick();if(!keys.every(k=>env.has(k)))continue
      const ids=keys.map(k=>this.root(env.get(k)!)),key=JSON.stringify(ids)
      if(seen.has(key))continue;seen.add(key)
      const binding:Record<string,E>=Object.fromEntries(keys.map((k,i)=>{const term=this.nodes[ids[i]!]!.term;if(!expression(term))throw Error('condition is not an expression binding');return [k,term]}))
      this.meter.tick() // callers must also charge work performed inside their predicate
      if(accept&&!accept(binding))continue
      found.push(binding)
      if(found.length>=maxMatches)break
    }
    return found
  }
}
