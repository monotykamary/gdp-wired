// Research-only initial selection within the existing non-range slot count.
import {readFileSync,writeFileSync,renameSync} from 'node:fs'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux required')
const file='core/counts.ts',source=readFileSync(file,'utf8')
const anchor='      if (!pass) return c\n      const taken = new Set<string>'
const inserted=`      if (!pass) return c
      const slots=c.insts.length
      const proposals=proposeWriteCountFrames(m,decls,{reads:all,insts:c.insts},new Set(all.filter(r=>r[1].endsWith('#')).map(r=>r[0])),32)
      const transports=proposals.filter(i=>i.terms.length===3).slice(0,Math.min(4,slots))
      if(transports.length){
        const insts=[...transports,...c.insts.slice(0,slots-transports.length)]
        const used=new Set(insts.flatMap(i=>i.terms.map(([,id])=>id))),have=new Set(c.reads.map(r=>r[0]))
        c={...c,insts,reads:[...c.reads,...all.filter(r=>used.has(r[0])&&!have.has(r[0]))],...(c.wits?{wits:[...c.wits,...transports.map(i=>i.wit)]}:{})}
      }
      const taken = new Set<string>`
if(source.split(anchor).length!==2)throw Error('initial selection anchor changed')
writeFileSync(file+'.tmp',"import {proposeWriteCountFrames} from './count-write-frames.ts'\n"+source.replace(anchor,inserted));renameSync(file+'.tmp',file)
