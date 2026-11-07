import {expect,test} from 'bun:test'
import {mldrHandSet} from '../protocols/ic3syn/mldr2-probe.ts'
const pop=(n:number):number=>n?n%2+pop(n>>>1):0
const alpha=(value:unknown):string=>{const ids=new Map<string,string>();return JSON.stringify(value).replace(/"[A-Za-z]+\$\d+"/g,name=>{if(!ids.has(name))ids.set(name,`"bound$${ids.size}"`);return ids.get(name)!})}

test('half and universally bounded overlap encodings agree with all small-set quorums',()=>{
 for(let a=0;a<32;a++)for(let b=0;b<32;b++){
  const p=pop(a&~b),q=pop(b&~a),r=pop(a&b),ha=Math.floor(pop(a)/2),hb=Math.floor(pop(b)/2)
  const half=Math.max(0,ha+1-p)+Math.max(0,hb+1-q)>r
  // The old bound premises are monotone in u,w; their smallest admissible
  // naturals are the only pair at which the conclusion can be hardest.
  const u=Math.max(0,Math.floor((r-p)/2)+1),w=Math.max(0,Math.floor((r-q)/2)+1)
  const bounded=r<u+w
  let semantic=true
  for(let x=a;x;x=(x-1)&a)if(pop(x)>ha)for(let y=b;y;y=(y-1)&b)if(pop(y)>hb&&!(x&y))semantic=false
  expect(half).toBe(semantic)
  expect(bounded).toBe(semantic)
 }
})

test('choosing the canonical overlap form changes no machine or other hand law',()=>{
 const a=mldrHandSet('star','half'),b=mldrHandSet('star','uw')
 expect(alpha(a.m)).toBe(alpha(b.m))
 expect(alpha(a.laws.filter(l=>!l.name.startsWith('Inv2973')))).toBe(alpha(b.laws.filter(l=>!l.name.startsWith('Inv2973'))))
 expect(a.laws.find(l=>l.name.startsWith('Inv2973'))).not.toEqual(b.laws.find(l=>l.name.startsWith('Inv2973')))
})
