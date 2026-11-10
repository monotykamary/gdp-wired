import {get,n,same,x} from '../../core/machine.ts'
import {canon,check,linear,type Path} from '../../kernel/kernel.ts'
import {clock,grow,rowsAt} from '../../kernel/prove.ts'
import {liftCountProxies} from './lift-count-proxies.ts'
const r=x('count'),cell=get('Rows',n(0)),lin=linear(cell,new Map())!,path:Path=new Map([[canon(lin),{lin,holds:true}]])
const part={name:'numeric guarded count',hyps:[same(r,cell),{op:'<=' as const,a:n(1),b:r}]},whole={name:'original guarded count',hyps:[same(r,cell),{op:'<=' as const,a:n(1),b:cell}]},out=grow(part,path,{nodes:0,until:clock()+1000}),trace:object[]=[]
const tree='tree'in out?liftCountProxies(part,whole,out.tree,[['count','Rows',n(0)]],path,path,e=>trace.push(e)):undefined
console.log(JSON.stringify({out,sourceChecked:'tree'in out&&check(part,out.tree,path),tree,trace,rp:rowsAt(part,path),rw:rowsAt(whole,path)}))
