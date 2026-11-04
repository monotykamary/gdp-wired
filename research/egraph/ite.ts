// Untrusted structural adapter. ITEs remain guard/then/else triples, never simplified.
// Encodings never reach the proof kernel: every candidate binding is decoded first.
import type {C,E} from '../../core/machine.ts'
import {EGraph,Meter} from './match.ts'
const prefix='\u0000astra-ite:'
const tag=(s:string,key:E):E=>({op:'get',map:prefix+s,key})
const pair=(a:E,b:E):E=>({op:'tup',a,b})
const unpair=(e:E):[E,E]=>{if(e.op!=='tup')throw Error('malformed ITE encoding');return [e.a,e.b]}
export class IteEGraph {
  private readonly graph:Pick<EGraph,'seed'|'match'>
  constructor(readonly meter:Meter,maxNodes=512,makeGraph=(m:Meter,n:number):Pick<EGraph,'seed'|'match'>=>new EGraph(m,n)){this.graph=makeGraph(meter,maxNodes)}
  private condition(c:C):E {
    this.meter.tick()
    switch(c.op){
      case '=':case '<':case '<=':return tag(c.op,pair(this.encode(c.a),this.encode(c.b)))
      case 'not':return tag('not',this.condition(c.x))
      case 'and':case 'or':return tag(c.op,c.xs.reduceRight<E>((tail,x)=>tag('cons',pair(this.condition(x),tail)),tag('nil',{op:'const',value:0})))
      case 'flag':case 'all':throw Error(`unsupported ITE condition: ${c.op}`)
    }
  }
  private decodeCondition(e:E):C {
    this.meter.tick()
    if(e.op!=='get'||!e.map.startsWith(prefix))throw Error('malformed ITE guard')
    const op=e.map.slice(prefix.length)
    if(op==='='||op==='<'||op==='<='){const [a,b]=unpair(e.key);return {op,a:this.decode(a),b:this.decode(b)}}
    if(op==='not')return {op,x:this.decodeCondition(e.key)}
    if(op==='and'||op==='or'){
      const xs:C[]=[];let tail=e.key
      while(tail.op==='get'&&tail.map===prefix+'cons'){const [head,rest]=unpair(tail.key);xs.push(this.decodeCondition(head));tail=rest}
      if(tail.op!=='get'||tail.map!==prefix+'nil'||tail.key.op!=='const'||tail.key.value!==0)throw Error('malformed ITE guard list')
      return {op,xs}
    }
    throw Error('condition encoding is not an expression binding')
  }
  private encode(e:E):E {
    this.meter.tick()
    switch(e.op){
      case 'var':case 'const':return e
      case 'get':if(e.map.startsWith(prefix))throw Error('reserved ITE map prefix');return {...e,key:this.encode(e.key)}
      case 'mul':case 'proj':return {...e,a:this.encode(e.a)}
      case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':return {...e,a:this.encode(e.a),b:this.encode(e.b)}
      case 'if':return tag('if',pair(this.condition(e.c),pair(this.encode(e.then),this.encode(e.else))))
    }
  }
  private decode(e:E):E {
    this.meter.tick()
    switch(e.op){
      case 'var':case 'const':return e
      case 'get':{
        if(e.map===prefix+'if'){const [guard,branches]=unpair(e.key),[yes,no]=unpair(branches);return {op:'if',c:this.decodeCondition(guard),then:this.decode(yes),else:this.decode(no)}}
        if(e.map.startsWith(prefix))throw Error('condition encoding is not an expression binding')
        return {...e,key:this.decode(e.key)}
      }
      case 'mul':case 'proj':return {...e,a:this.decode(e.a)}
      case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':return {...e,a:this.decode(e.a),b:this.decode(e.b)}
      case 'if':throw Error('unencoded ITE in matcher result')
    }
  }
  private assertion(c:C):C {
    this.meter.tick()
    switch(c.op){
      case '=':case '<':case '<=':return {...c,a:this.encode(c.a),b:this.encode(c.b)}
      case 'not':return {...c,x:this.assertion(c.x)}
      case 'and':case 'or':return {...c,xs:c.xs.map(x=>this.assertion(x))}
      case 'flag':case 'all':throw Error(`unsupported e-condition: ${c.op}`)
    }
  }
  seed(cs:C[]){this.graph.seed(cs.map(c=>this.assertion(c)))}
  match(patterns:E[],keys:string[],maxMatches=32):Record<string,E>[] {
    return this.graph.match(patterns.map(p=>this.encode(p)),keys,maxMatches).map(binding=>Object.fromEntries(Object.entries(binding).map(([k,e])=>[k,this.decode(e)])))
  }
}
