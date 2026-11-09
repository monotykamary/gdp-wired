import {expect,test} from 'bun:test'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {brotliDecompressSync} from 'node:zlib'
const load=(name:string,sha:string)=>{const bytes=readFileSync(new URL(`fixtures/${name}.br`,import.meta.url));expect(createHash('sha256').update(bytes).digest('hex')).toBe(sha);return JSON.parse(brotliDecompressSync(bytes).toString()) as Record<string,string>}
test('frozen baseline safety archive preserves the exhausted-pool counterexample',()=>{
 const files=load('safety-gp1','b96c779fda332e17778af88d76e69a8682b98de04739c1e07e6d3d4b154c0f0c')
 expect(Object.keys(files)).toHaveLength(39)
 const first=JSON.parse(files['stage-0.json']!),last=JSON.parse(files['stage-26.json']!)
 expect(first.pass).toBe(1);expect(first.phase).toBe('query');expect(first.generation.work).toBe(65536);expect(first.generation.exhausted).toBe(true)
 expect(first.certificateRequest.reads).toHaveLength(5);expect(last.certificateRequest.reads).toHaveLength(5);expect(last.hyps.length).toBeGreaterThan(first.hyps.length)
})
test('frozen E-14 family is the actual 35-law output, not the supplied-p1 fixture',()=>{
 const files=load('e14-generated','4b97fb96467ee51e9b80ff0a13b33f00d2731452fd93e6191f65c17c8882d64a')
 expect(Object.keys(files)).toEqual(['family-first.json'])
 const family=JSON.parse(files['family-first.json']!);expect(family.laws).toHaveLength(35)
 expect(family.laws.some((l:{name:string})=>l.name.startsWith('p1:'))).toBe(false)
 expect(family.laws.some((l:{name:string})=>l.name.startsWith('count cubes:'))).toBe(true)
})
