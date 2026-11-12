// Counts-only diagnostic projection; never used for proof/model/verdict equality.
// Never call the native callback: invocation could change counted work.
export const COUNT_PROJECTION='replayEvidence-presence-only/v1'
export function projectCountEvent(value:unknown){
 if(!value||typeof value!=='object'||Array.isArray(value)||Object.getPrototypeOf(value)!==Object.prototype)throw Error('unsupported counts event')
 if(Object.getOwnPropertySymbols(value).length)throw Error('unsupported symbol counts field')
 const event:Record<string,unknown>={},omittedCallbacks:string[]=[]
 for(const key of Object.getOwnPropertyNames(value)){
  const d=Object.getOwnPropertyDescriptor(value,key);if(!d||!d.enumerable||!('value' in d))throw Error('unsupported counts nonenumerable/accessor')
  if(typeof d.value==='function'){
   if(key!=='replayEvidence')throw Error('unsupported counts callback: '+key)
   omittedCallbacks.push(key)
  }else Object.defineProperty(event,key,{value:d.value,enumerable:true})
 }
 return {projection:COUNT_PROJECTION,omittedCallbacks,event}
}
