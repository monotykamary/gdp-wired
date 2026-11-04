// Exact alpha correspondence of inputs, not proof transport or an added trusted rule.
export type AlphaContext={m:unknown,laws:{name:string,forall?:string,keys?:string[],holds:unknown}[]}
export function contextBindings(source:AlphaContext,target:AlphaContext){
  const names=new Map<string,string>(),back=new Map<string,string>(),free=new Set<string>();let visited=0
  const bind=(a:string,b:string)=>{if((names.has(a)&&names.get(a)!==b)||(back.has(b)&&back.get(b)!==a))throw Error('non-bijective binding');names.set(a,b);back.set(b,a)}
  const extend=(a:string[],b:string[],env:Map<string,string>)=>{
    if(a.length!==b.length||new Set(a).size!==a.length||new Set(b).size!==b.length)throw Error('binder arity')
    const next=new Map(env);a.forEach((x,i)=>{bind(x,b[i]!);next.set(x,b[i]!)});return next
  }
  const walk=(a:unknown,b:unknown,path:string,env:Map<string,string>):void=>{
    if(++visited>100000)throw Error('comparison cap')
    if(!a||!b||typeof a!=='object'||typeof b!=='object'){if(a!==b)throw Error('literal mismatch at '+path);return}
    if(Array.isArray(a)||Array.isArray(b)){if(!Array.isArray(a)||!Array.isArray(b)||a.length!==b.length)throw Error('array mismatch');a.forEach((x,i)=>walk(x,b[i],path+'/'+i,env));return}
    const x=a as Record<string,unknown>,y=b as Record<string,unknown>,keys=Object.keys(x).sort()
    if(JSON.stringify(keys)!==JSON.stringify(Object.keys(y).sort()))throw Error('field mismatch at '+path)
    let inner=env;const skip=new Set<string>()
    if(x.op==='var'&&y.op==='var'){
      const old=x.name as string,next=y.name as string;if((env.get(old)??old)!==next)throw Error('variable mismatch at '+path)
      if(!env.has(old))free.add(old);skip.add('name')
    }else if(x.op==='all'&&y.op==='all'){
      inner=extend([x.key as string,...(x.keys as string[]??[])],[y.key as string,...(y.keys as string[]??[])],env);skip.add('key');skip.add('keys')
    }else if(typeof x.each==='string'&&typeof y.each==='string'&&'value'in x){
      inner=extend([x.each],[y.each],env);skip.add('each')
    }
    for(const key of keys)if(!skip.has(key))walk(x[key],y[key],path+'/'+key,inner)
  }
  walk(source.m,target.m,'machine',new Map())
  if(source.laws.length!==target.laws.length||new Set(source.laws.map(l=>l.name)).size!==source.laws.length)throw Error('law set mismatch')
  for(const l of source.laws){
    const t=target.laws.find(x=>x.name===l.name);if(!t)throw Error('missing law')
    const a=l.forall?[l.forall,...(l.keys??[])]:[],b=t.forall?[t.forall,...(t.keys??[])]:[],env=extend(a,b,new Map())
    const left={...l},right={...t};delete left.forall;delete left.keys;delete right.forall;delete right.keys
    walk(left,right,'law/'+l.name,env)
    if(l.forall&&t.forall)bind(l.forall+'#',t.forall+'#')
  }
  for(const [a,b]of names)if(a!==b&&(free.has(a)||free.has(b)))throw Error('capture hazard')
  return {renamings:Object.fromEntries(names),lawOrder:target.laws.map(t=>source.laws.findIndex(l=>l.name===t.name)),visited}
}
