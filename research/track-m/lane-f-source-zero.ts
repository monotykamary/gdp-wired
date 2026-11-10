// Inspect the exact index, never supply an assumption to the proof engine.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {termColumn,mcGoal} from '../../kernel/kernel.ts'
import {certFor} from '../../core/counts.ts'
import {focusCountCert} from '../../core/count-focused.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {pack} from './section18-codec.ts'
const [file,out]=process.argv.slice(2),p=JSON.parse(readFileSync(file!,'utf8'))
if(!out)throw Error('PACKET OUT required')
for(const [i,t]of p.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw Error('column restoration failed')
const cert=focusCountCert(p.m,p.packet.decls,certFor(p.packet.goal,p.packet.decls,true,1000),{structural:false,frames:true,algebraic:true,requestFrames:true,copyFrames:true,claim:p.packet.goal.hyps.at(-1)}),g=mcGoal(p.packet.goal.hyps,p.packet.decls,cert)
if(!g)throw Error('invalid MC packet')
const raw=g.hyps.slice(0,-cert.insts.length),inst=cert.insts[0]!,reads=cert.reads.filter(r=>inst.terms.some(t=>t[1]===r[0])),hyp=g.hyps[raw.length]
mkdirSync(out,{recursive:true});writeFileSync(join(out,'context.json'),pack({p,cert,g,raw}))
console.log(JSON.stringify({law:p.lawName,source:0,inst,reads,counts:countsForReads(p.packet.decls,reads),hyp,rawLength:raw.length,instances:cert.insts.length}))
