import {leanLibrary} from '../library.ts'
import {leanProject} from '../emit.ts'

// Lifts always use the current complete library. The general legacy emitter
// intentionally selects an older counted ABI for cut-free historical projects;
// mixing that ABI with the promoted current modules would not compile.
export function liftProject(body:string,options:{name?:string}={}):Record<string,string> {
  return leanProject(body,{...options,currentFamily:true})
}

// Product-owned library only: no filesystem or research-tree dependency.
export function leanSource(module:string):string {
  const text=leanLibrary[module+'.lean']
  if(typeof text!=='string')throw Error('missing product Lean library module: '+module)
  return text
}
