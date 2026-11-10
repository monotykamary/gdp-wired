import {expect,test} from 'bun:test'
import {mkdtempSync,rmSync,writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {brotliDecompressSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {packProduction} from './pack-production.ts'
function fixture(run:(dir:string)=>void){const dir=mkdtempSync(join(tmpdir(),'incl-pack-'));try{writeFileSync(join(dir,'family-source.json'),JSON.stringify({machine:{name:'test'},laws:[]}));run(dir)}finally{rmSync(dir,{recursive:true,force:true})}}
test('lossless diagnostic keeps the source and both phase certificates',()=>fixture(dir=>{
 for(const name of ['production-proof.json','final-proof-0.json','final-proof-1.json'])writeFileSync(join(dir,name),JSON.stringify({name}))
 const out=packProduction(dir),bytes=Buffer.from(out.data,'base64'),files=JSON.parse(brotliDecompressSync(bytes).toString())
 expect(out.omitted).toBe(0);expect(out.filenames).toEqual(Object.keys(files));expect(out.files).toBe(4)
 expect(createHash('sha256').update(bytes).digest('hex')).toBe(out.sha256)
 expect(out).not.toHaveProperty('checked');expect(out).not.toHaveProperty('proven')
}))
test('an unknown result retains the source without pretending to be a proof',()=>fixture(dir=>{
 expect(packProduction(dir).filenames).toEqual(['family-source.json'])
}))
test('a partial proof archive is rejected rather than silently truncated',()=>fixture(dir=>{
 writeFileSync(join(dir,'production-proof.json'),'{}')
 expect(()=>packProduction(dir)).toThrow('incomplete production proof archive')
}))
test('the archive cap never drops required files',()=>fixture(dir=>{
 expect(()=>packProduction(dir,1)).toThrow('refusing to omit required files')
 expect(()=>packProduction(dir,300000)).toThrow('invalid capture limit')
}))
