import {type Expr, lit} from './model.ts'
export function complexity(e: Expr): number {
  switch (e.k) {
    case 'not': return 1 + complexity(e.x)
    case 'op': return 1 + complexity(e.a) + complexity(e.b)
    case 'choose': return 1 + complexity(e.c) + complexity(e.a) + complexity(e.b)
    case 'calendar': return 2 + complexity(e.a) + complexity(e.b)
    case 'lit': case 'name': case 'undefined': return 1
  }
}
export function shrink(e: Expr): Expr[] {
  const out: Expr[] = [lit(false), lit(true)]
  if (e.k === 'not') out.push(e.x, ...shrink(e.x).map(x => ({...e, x})))
  if (e.k === 'op' || e.k === 'calendar') {
    out.push(e.a, e.b)
    for (const a of shrink(e.a)) out.push({...e, a})
    for (const b of shrink(e.b)) out.push({...e, b})
  }
  const unique = new Map(out.filter(x => complexity(x) < complexity(e)).map(x => [JSON.stringify(x), x]))
  return [...unique.values()].sort((a, b) => complexity(a) - complexity(b))
}
