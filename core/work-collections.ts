// Helpers for closed, ordinary arrays and strings owned by the synchronous
// kernel. Their metadata reads do not call getters/proxies. Callback bodies
// retain their own operation admissions; an iteration ticket is not authority
// for an unbounded callback. OFF uses the original native operations.
import {completeWorkProfile} from './work-profile.ts'
import {startWork} from './work-admission.ts'
export function workMap<T,U>(input:readonly T[],map:(x:T,i:number)=>U,site:string):U[]{
 if(!completeWorkProfile.enabled)return input.map(map)
 const out:U[]=[]
 for(let i=0;i<input.length;i++){startWork('ticks',1,site);out.push(map(input[i]!,i))}
 return out
}
export function workFilter<T>(input:readonly T[],test:(x:T,i:number)=>boolean,site:string):T[]{
 if(!completeWorkProfile.enabled)return input.filter(test)
 const out:T[]=[]
 for(let i=0;i<input.length;i++){startWork('ticks',1,site);const item=input[i]!;if(test(item,i))out.push(item)}
 return out
}
export function workFlatMap<T,U>(input:readonly T[],map:(x:T,i:number)=>readonly U[],site:string):U[]{
 if(!completeWorkProfile.enabled)return input.flatMap((x,i)=>map(x,i))
 const out:U[]=[]
 for(let i=0;i<input.length;i++){
  startWork('ticks',1,site);const part=map(input[i]!,i)
  for(let j=0;j<part.length;j++){startWork('ticks',1,`${site}:copy`);out.push(part[j]!)}
 }
 return out
}
export function workArraySlice<T>(input:readonly T[],start:number,site:string):T[]{
 if(!completeWorkProfile.enabled)return input.slice(start)
 const out:T[]=[]
 for(let i=start;i<input.length;i++){startWork('ticks',1,site);out.push(input[i]!)}
 return out
}
export function workConcat<T>(a:readonly T[],b:readonly T[],site:string):T[]{
 if(!completeWorkProfile.enabled)return[...a,...b]
 const out:T[]=[]
 for(let i=0;i<a.length;i++){startWork('ticks',1,site);out.push(a[i]!)}
 for(let i=0;i<b.length;i++){startWork('ticks',1,site);out.push(b[i]!)}
 return out
}
export function workStrings(input:string[],site:string):string[]{
 if(!completeWorkProfile.enabled)return input.sort()
 const compare=(a:string,b:string)=>{
  startWork('ticks',1,`${site}:compare`)
  for(let i=0;i<Math.min(a.length,b.length);i++){
   startWork('tableCells',1,`${site}:left`);const x=a.charCodeAt(i)
   startWork('tableCells',1,`${site}:right`);const y=b.charCodeAt(i)
   if(x!==y)return x-y
  }
  return a.length-b.length
 }
 // Native Array.sort can copy an entire array before its first comparator.
 // Use a stable merge with every actual reference read/move behind a start.
 let source:string[]=[]
 for(let i=0;i<input.length;i++){startWork('ticks',1,`${site}:input`);source.push(input[i]!)}
 for(let width=1;width<source.length;width*=2){
  const next:string[]=[]
  for(let begin=0;begin<source.length;begin+=2*width){
   let left=begin,right=Math.min(begin+width,source.length)
   const middle=right,end=Math.min(begin+2*width,source.length)
   while(left<middle||right<end){
    let takeLeft=right===end
    if(left<middle&&right<end){
     startWork('ticks',1,`${site}:read-left`);const a=source[left]!
     startWork('ticks',1,`${site}:read-right`);const b=source[right]!
     takeLeft=compare(a,b)<=0
    }
    startWork('ticks',1,`${site}:move`)
    next.push(source[takeLeft?left++:right++]!)
   }
  }
  source=next
 }
 for(let i=0;i<source.length;i++){startWork('ticks',1,`${site}:output`);input[i]=source[i]!}
 return input
}
export function workJoin(input:readonly string[],separator:string,site:string):string{
 if(!completeWorkProfile.enabled)return input.join(separator)
 let n=BigInt(Math.max(0,input.length-1))*BigInt(separator.length)
 for(let i=0;i<input.length;i++){startWork('ticks',1,`${site}:size`);n+=BigInt(input[i]!.length)}
 if(n>BigInt(Number.MAX_SAFE_INTEGER))throw new RangeError('unsafe joined string size')
 // One native string materialization, whose modeled output-code-unit count
 // is known exactly. It cannot publish a partially constructed string.
 startWork('tableCells',Number(n),`${site}:materialize`)
 return input.join(separator)
}
export function workSetArray<T>(input:ReadonlySet<T>,site:string):T[]{
 if(!completeWorkProfile.enabled)return[...input]
 const out:T[]=[],iterator=input.values(),size=input.size
 for(let i=0;i<size;i++){startWork('ticks',1,site);const next=iterator.next();if(next.done)throw new Error('set changed during traversal');out.push(next.value)}
 return out
}
export function workEntries(input:object,site:string):[string,unknown][]{
 if(!completeWorkProfile.enabled)return Object.entries(input)
 const out:[string,unknown][]=[]
 for(const key in input){
  startWork('ticks',1,site)
  const d=Object.getOwnPropertyDescriptor(input,key)
  if(!d||!('value'in d))throw new TypeError('ordinary data members required')
  out.push([key,d.value])
 }
 return out
}
export function workJSON(value:unknown,site:string):string|undefined{
 if(!completeWorkProfile.enabled)return JSON.stringify(value)
 if(typeof value!=='string'){
  if(value!==null&&typeof value==='object')throw new TypeError('scalar formatting required')
  startWork('ticks',1,site);return JSON.stringify(value)
 }
 let length=2,paired=false
 for(let i=0;i<value.length;i++){
  startWork('tableCells',1,`${site}:scan`);const code=value.charCodeAt(i)
  if(code>=0xd800&&code<=0xdbff){
   let low=false
   if(i+1<value.length){startWork('tableCells',1,`${site}:lookahead`);const next=value.charCodeAt(i+1);low=next>=0xdc00&&next<=0xdfff}
   length+=low?1:6;paired=low
  }else if(code>=0xdc00&&code<=0xdfff){length+=paired?1:6;paired=false}
  else{paired=false;length+=code===34||code===92?2:code<32?[8,9,10,12,13].includes(code)?2:6:1}
 }
 startWork('tableCells',length,`${site}:materialize`)
 return JSON.stringify(value)
}
export function workSlice(text:string,start:number,end=text.length,site='string slice'):string{
 if(!completeWorkProfile.enabled)return text.slice(start,end)
 const clamp=(n:number)=>n<0?Math.max(0,text.length+Math.trunc(n)):Math.min(text.length,Math.trunc(n))
 const n=Math.max(0,clamp(end)-clamp(start))
 startWork('tableCells',n,site)
 return text.slice(start,end)
}
