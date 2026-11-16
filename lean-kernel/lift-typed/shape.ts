// Preflight equivalence only. All generated source literals retain their exact
// original syntax, with the semantic correspondence discharged in Lean.
export function associativeShape<T>(x:T):T {
 if(!x||typeof x!=='object')return x
 if(Array.isArray(x))return x.map(associativeShape) as T
 const out:any=Object.fromEntries(Object.entries(x).map(([k,v])=>[k,associativeShape(v)]))
 if((out.op==='and'||out.op==='or')&&Array.isArray(out.xs))out.xs=out.xs.flatMap((v:any)=>v?.op===out.op?v.xs:[v])
 return out
}
