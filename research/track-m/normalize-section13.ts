// A cap before the first numeric leaf has no numeric model or violated set.
// Recover its exact guard from the active closure frame, never from a prior law.
export function normalizeSection13(result:any):any{
 const r={...result};delete r.columns
 if(!r.closed&&r.firstFailure?.kind==='budget'&&!r.firstFailure.capture){
  const frames:any[]=r.trace?.frames??[],closure=frames.findLast(f=>f.kind==='closure'),leaf=frames.findLast(f=>f.kind==='leaf')
  const frame=leaf??closure
  if(frame){r.firstFailure={...r.firstFailure,path:frame.meta.path,guards:frame.meta.path,numericModel:null,violatedSet:[],phase:leaf?'numeric-leaf-before-model':'closure-preparation-before-numeric-leaf',frame:frame.id,note:'Counted cap interrupted this scope. No terminal numeric model or violated set was returned.'}}
 }
 return r
}
