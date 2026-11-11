import {expect,test} from 'bun:test'
import {linearExportFixture} from '../research/track-m/linear-export-fixture.ts'
import {checkMC} from '../kernel/kernel.ts'
import {encode,mcToLean} from './emit.ts'
test('a checked linear count cut exports its auxiliary proof and refuses mutation',()=>{
 const f=linearExportFixture(),source=mcToLean('linear',f.hyps,f.decls,f.cert)
 expect(source).toContain('def linear_lins : List LinCut')
 expect(source).toContain('linear_frames [] linear_lins = true')
 expect(source).toContain('mcF_sound linear_hyps linear_decls linear_cert linear_frames [] linear_lins linear_check')
 const wrong={...f.cert,lins:[{...f.cert.lins![0]!,tree:{leaf:[]}}]}
 expect(checkMC(f.hyps,f.decls,wrong)).toBe(false)
 expect(()=>mcToLean('wrong',f.hyps,f.decls,wrong)).toThrow('does not check')
})
test('empty linear-cut context preserves the legacy encoding',()=>{
 const ex={name:'plain',goal:{name:'plain',hyps:[]},tree:{leaf:[]}}
 const a=encode(ex),b=encode(ex,false,true,undefined,undefined,false,false,{lins:[]})
 expect([a.tab,a.tree,a.hyps,a.cols]).toEqual([b.tab,b.tree,b.hyps,b.cols])
})
