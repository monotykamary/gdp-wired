// Untrusted head-directed materialization, not hypothesis selection for a proof.
// Scan every input node. Store all selected reads (including every child) and
// ALL asserted positive-equality endpoints. Irrelevant observations add no nodes.
import type {C,E} from '../../core/machine.ts'
import {IndexedEGraph} from './indexed-match.ts'
import {Meter} from './match.ts'
export class TriggerIndex {
  readonly graph:IndexedEGraph
  readonly stats={expressionsVisited:0,conditionsVisited:0,selectedReads:0,positiveEqualities:0,hypothesesCompleted:0}
  private heads=new Set<string>()
  private ready=false
  constructor(readonly meter:Meter,patterns:E[],maxNodes=512){
    this.graph=new IndexedEGraph(meter,maxNodes,true)
    for(const pattern of patterns){this.meter.tick();if(pattern.op!=='get')throw Error('trigger index requires read-headed patterns');this.heads.add(pattern.map)}
  }
  private expression(e:E):void{
    this.meter.tick();this.stats.expressionsVisited++
    switch(e.op){
      case 'var':case 'const':return
      case 'get':this.expression(e.key);if(this.heads.has(e.map)){this.stats.selectedReads++;this.graph.add(e)}return
      case 'mul':case 'proj':this.expression(e.a);return
      case 'add':case 'sub':case 'min':case 'max':case 'prod':case 'tup':this.expression(e.a);this.expression(e.b);return
      case 'if':this.condition(e.c,false);this.expression(e.then);this.expression(e.else);return
    }
  }
  private condition(c:C,positive:boolean):void{
    this.meter.tick();this.stats.conditionsVisited++
    switch(c.op){
      case '=':case '<':case '<=':
        this.expression(c.a);this.expression(c.b)
        if(positive&&c.op==='='){this.stats.positiveEqualities++;this.graph.seed([c])}
        return
      case 'and':for(const x of c.xs)this.condition(x,positive);return
      case 'or':for(const x of c.xs)this.condition(x,false);return
      case 'not':this.condition(c.x,false);return
      case 'flag':case 'all':throw Error(`unsupported e-condition: ${c.op}`)
    }
  }
  seed(hyps:C[]){this.ready=false;for(const c of hyps){this.condition(c,true);this.stats.hypothesesCompleted++}this.graph.rebuild();this.ready=true}
  match(patterns:E[],keys:string[],maxMatches=32,accept?:(binding:Record<string,E>)=>boolean){
    if(!this.ready)throw Error('trigger input scan incomplete')
    for(const p of patterns){this.meter.tick();if(p.op!=='get'||!this.heads.has(p.map))throw Error('query outside indexed heads')}
    return this.graph.match(patterns,keys,maxMatches,accept)
  }
}
