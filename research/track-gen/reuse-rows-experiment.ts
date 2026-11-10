// Research-only patch in a disposable remote snapshot, before enabling shared rows.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.TRACK_GEN_DISPOSABLE!=='1')throw Error('disposable only')
const path='core/infer.ts',old=readFileSync(path,'utf8')
const anchor='  for (const st of opts.seen ?? []) if (!m.params.length) keep({params: {}, st})'
const guard='const moreRuns = (trial: number) => (runsTimed ?'
if(!old.includes(anchor)||!old.includes(guard))throw Error('source mismatch')
writeFileSync(path,old.replace(anchor,anchor+'\n  const supplied = !!opts.cubes && !!opts.rows?.length\n  if (supplied) for (const row of opts.rows!) keep(row)').replace(guard,'const moreRuns = (trial: number) => !supplied && (runsTimed ?'))
