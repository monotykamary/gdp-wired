import type {C, Law, Machine} from '../../core/machine.ts'
import {sourceStructure} from '../lift/source.ts'

export const trueCondition:C={op:'<=',a:{op:'const',value:0},b:{op:'const',value:0}}
const falseCondition:C={op:'<',a:{op:'const',value:0},b:{op:'const',value:0}}
const same=(a:unknown,b:unknown)=>sourceStructure(a)===sourceStructure(b)
/** Mirror only the provided Lean candidate transform, including nested E.ite.
 * This is used for proposals, never as evidence that an erased proof checks. */
export function eraseBound<T>(value:T,bound:number):T {
  if(!Number.isSafeInteger(bound)||bound<=0)throw Error('invalid bound')
  const visit=(x:unknown):unknown=>{
    if(!x||typeof x!=='object')return x
    if(Array.isArray(x))return x.map(visit)
    const o=x as Record<string,unknown>,b=o.b as Record<string,unknown>|undefined
    if((o.op==='<'||o.op==='<=')&&b?.op==='const'&&b.value===bound)return trueCondition
    return Object.fromEntries(Object.entries(o).map(([k,v])=>[k,visit(v)]))
  }
  return visit(value) as T
}
// Binary syntax exactly follows leanConnective, including singleton neutrals.
type Shape={atom:C}|{op:'and'|'or',left:Shape,right:Shape}|{op:'not',inner:Shape}
function shape(c:C):Shape {
  if(c.op==='not')return {op:'not',inner:shape(c.x)}
  if(c.op!=='and'&&c.op!=='or')return {atom:c}
  const neutral=c.op==='and'?trueCondition:falseCondition
  const xs=c.xs.map(shape)
  if(!xs.length)return {atom:neutral}
  if(xs.length===1)return {op:c.op,left:xs[0]!,right:{atom:neutral}}
  return xs.slice(0,-1).reduceRight<Shape>((right,left)=>({op:c.op,left,right}),xs.at(-1)!)
}
export type Weakening={kind:'refl'|'top'|'bot'}|{kind:'orLeft'|'orRight'|'andLeft'|'andRight'|'neg',child:Weakening}|{kind:'orElim'|'andIntro',left:Weakening,right:Weakening}
/** Bounded syntactic AND/OR subsumption. Arithmetic formulas are opaque
 * atoms; negation is contravariant. No arithmetic, SMT, theorem search or evaluation of source programs. */
export function structuralWeakening(strong:C,weak:C):Weakening|null {
  let visits=0
  const go=(a:Shape,b:Shape,depth:number):Weakening|null=>{
    if(++visits>100000||depth>256)throw Error('structural weakening limit exceeded')
    if(same(a,b))return {kind:'refl'}
    if('atom'in b&&same(b.atom,trueCondition))return {kind:'top'}
    if('atom'in a&&same(a.atom,falseCondition))return {kind:'bot'}
    if('op'in a&&a.op==='not'&&'op'in b&&b.op==='not'){
      const child=go(b.inner,a.inner,depth+1)
      return child?{kind:'neg',child}:null
    }
    if('op'in a&&a.op==='or'){
      const left=go(a.left,b,depth+1),right=left&&go(a.right,b,depth+1)
      return left&&right?{kind:'orElim',left,right}:null
    }
    if('op'in b&&b.op==='and'){
      const left=go(a,b.left,depth+1),right=left&&go(a,b.right,depth+1)
      return left&&right?{kind:'andIntro',left,right}:null
    }
    if('op'in a&&a.op==='and'){
      const left=go(a.left,b,depth+1)
      if(left)return {kind:'andLeft',child:left}
      const right=go(a.right,b,depth+1)
      if(right)return {kind:'andRight',child:right}
    }
    if('op'in b&&b.op==='or'){
      const left=go(a,b.left,depth+1)
      if(left)return {kind:'orLeft',child:left}
      const right=go(a,b.right,depth+1)
      if(right)return {kind:'orRight',child:right}
    }
    return null
  }
  return go(shape(strong),shape(weak),0)
}
export function weakeningTerm(p:Weakening):string {
  const prefix='Bapa.StructuralWeakening.Subsumes.'
  if(p.kind==='refl'||p.kind==='top'||p.kind==='bot')return prefix+p.kind+' _'
  if('child'in p)return `${prefix}${p.kind} (${weakeningTerm(p.child)})`
  if('left'in p)return `${prefix}${p.kind} (${weakeningTerm(p.left)}) (${weakeningTerm(p.right)})`
  throw Error('unsupported weakening constructor')
}
export function boundSyntaxValues(pre:C):number[] {
  const values=new Set<number>()
  const visit=(c:C):void=>{
    if(c.op==='and'||c.op==='or')c.xs.forEach(visit)
    else if(c.op==='<'||c.op==='<='){
      if(c.b.op==='const'&&Number.isSafeInteger(c.b.value)&&c.b.value>0)values.add(c.b.value)
    }
  }
  // Only positive upper bounds admitted in the producer precondition qualify;
  // constants in value encodings, laws and arithmetic do not select a cap.
  visit(pre)
  return [...values]
}
export function candidateBounds(source:Machine,producer:Machine):number[] {
  const pre=producer.pre??trueCondition
  return boundSyntaxValues(pre).filter(b=>!same(pre,eraseBound(pre,b))&&!!structuralWeakening(source.pre??trueCondition,eraseBound(pre,b)))
}
export function publicCoverage(laws:Law[],retained:Law[],bound:number):{indices:number[],proofs:Weakening[]} {
  const ordinary=(l:Law)=>!['some','ex','witness','stated','finite'].some(k=>(l as unknown as Record<string,unknown>)[k]!==undefined)
  if(!laws.length||laws.some(l=>!ordinary(l)))throw Error('unsupported public law metadata')
  const proofs:Weakening[]=[],indices=laws.map(l=>{
    const matches=retained.flatMap((r,i)=>{
      if(!ordinary(r)||l.forall!==r.forall||!same(l.keys??[],r.keys??[]))return []
      const proof=structuralWeakening(eraseBound(r.holds,bound),l.holds)
      return proof?[{i,proof}]:[]
    })
    if(matches.length!==1)throw Error(`unsupported or ambiguous structural public coverage (${matches.length} matches)`)
    proofs.push(matches[0]!.proof);return matches[0]!.i
  })
  return {indices,proofs}
}
