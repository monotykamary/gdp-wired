// A minimal direct-frame control; the selected laws remain unmodified.
import {type Machine,type Law} from '../../core/machine.ts'
import {bareRangeMap,readTuples} from '../../core/count-support.ts'
export function frameContext(m:Machine,laws:Law[],target:Law,support:ReadonlySet<Law>):Law[]{
 const maps=new Set(readTuples(target.holds).map(([map])=>map))
 return laws.filter(l=>{if(l===target)return true;const reads=readTuples(l.holds);if(!reads.length||reads.some(([map])=>m.counts?.[map]||!maps.has(map)))return false;return !!bareRangeMap(m,l)||support.has(l)&&!l.keys?.length})
}
