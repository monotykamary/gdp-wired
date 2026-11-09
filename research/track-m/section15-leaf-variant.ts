// Section 15.4 experiment only. Never imported by production.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux copy required')
const mode=process.argv[2];if(!['before','after'].includes(mode!))throw Error('before|after required')
if(mode==='after'){
 const change=(p:string,replacements:[string,string][],prefix='')=>{let s=readFileSync(p,'utf8');for(const [a,b]of replacements){if(s.split(a).length!==2)throw Error('leaf anchor changed: '+a);s=s.replace(a,b)}writeFileSync(p,prefix+s)}
 change('core/count-recovery/guard-cases.ts',[
  [' let inactive:Tree|undefined,attempted=false,inactiveLeaf:{tree:Tree,path:Path}|undefined',' let inactive:Tree|undefined,attempted=false,inactiveLeaf:{tree:Tree,path:Path}|undefined\n let leavesLeft=guardLeafCount(guard,conditions,root)'],
  ['end=active?Math.min(until,start+leafAllowance(until-start,1)):Math.min(until,start+500)','end=Math.min(until,start+Math.min(active?Infinity:500,leafAllowance(until-start,leavesLeft--)))']
 ],"import {guardLeafCount} from '../../research/track-m/section15-leaf-count.ts'\n")
 change('core/count-cases.ts',[
  ['const coreGrow=(g:Goal,end:number)=>{','const coreGrow=(g:Goal,end:number)=>{end=Math.min(end,clock()+leafAllowance(end-clock(),1));'],
  ['Math.max(600,(until-clock())/(cuts.length+1-i-(fallback?1:0)))','leafAllowance(until-clock(),cuts.length+1-i-(fallback?1:0))'],
  ['const part={name:goal.name,hyps:[...prefix,...goal.hyps]},out=grow(part,new Map(),{nodes:0,until:caseEnd,units:options.units})','const part={name:goal.name,hyps:[...prefix,...goal.hyps]},out=grow(part,new Map(),{nodes:0,until:Math.min(caseEnd,clock()+leafAllowance(caseEnd-clock(),1)),units:options.units})'],
  ['clock()+(until-clock())/(missing.length-j)','clock()+leafAllowance(until-clock(),missing.length-j)']
 ],"import {leafAllowance} from './count-recovery/leaf-allowance.ts'\n")
 change('core/count-recovery/field-bound-lemmas.ts',[
  ['finish?Math.max(0,until-clock()):250','finish?leafAllowance(until-clock(),1):250'],
  ['solve(part,Math.max(150,until-clock()-200),true)','solve(part,Math.min(Math.max(150,until-clock()-200),leafAllowance(until-clock(),1)),true)']
 ],"import {leafAllowance} from './leaf-allowance.ts'\n")
 change('core/count-recovery/row-cases.ts',[
  ['const t=prove(path,Math.min(until,clock()+1500))','const t=prove(path,Math.min(until,clock()+Math.min(1500,leafAllowance(until-clock(),Math.max(1,(pairs.length<2?2:options.splitEqual?4:3)-cache.size)))))']
 ],"import {leafAllowance} from './leaf-allowance.ts'\n")
}
