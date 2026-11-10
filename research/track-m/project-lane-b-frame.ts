import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const dir='runs/track-m/lane-b-flags-projection-v1',text=readFileSync(dir+'/project.log','utf8'),mark='SIDE=after\n',pos=text.indexOf(mark)
if(pos<0)throw Error('missing after projection')
const capture=JSON.parse(text.slice(pos+mark.length)),m=capture.lastModel,w=m.witness
if(w.size!==3||w.op!==1||w.i!==0||w['a$quorum#']!==0||w['b$quorum']!==0)throw Error('unexpected retained model')
const pre=m.reads.find((r:any[])=>r[1]==='inX$row'&&r[2].op==='var'&&r[2].name==='a$quorum#')
const post=m.reads.find((r:any[])=>r[1]==='inX$row#'&&r[2].op==='var'&&r[2].name==='a$quorum#')
if(!pre||!post)throw Error('missing paired row reads')
const selected=(a:string,b:string)=>m.insts.some((i:any)=>i.unit===0&&i.terms.length===2&&i.terms.some((t:any[])=>t[0]===1&&t[1]===a)&&i.terms.some((t:any[])=>t[0]===-1&&t[1]===b))
const out={evidenceOnly:true,checkedProof:false,source:'7e4f8912 plus disposable flags-first integration',sourceArchiveSha256:'fb2731957f6642bb4ba441e74eecf79379872ee23c8503c3e0dd1adb4dc7441f',projectionSha256:createHash('sha256').update(text).digest('hex'),law:capture.law,operation:'copy',operationCode:w.op,size:w.size,i:w.i,j:w.j,a:w['a$quorum#'],b:w.b$quorum,pre:{read:pre,modelValue:w[pre[0]]},post:{read:post,modelValue:w[post[0]]},selectedRowFrameVectors:{postMinusPre:selected(post[0],pre[0]),preMinusPost:selected(pre[0],post[0])},selectedInstances:m.insts.map(({terms,unit}:any)=>({terms,unit})),finding:'At i=0, the Config copy maps row 0 to itself; whether its guard fires or not, Config is unchanged. The retained symbolic model assigns different pre/post row-0 counts. This is a spurious count frame, not a finite counterexample.'}
writeFileSync(dir+'/op1-spurious-frame.json',JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify(out))
