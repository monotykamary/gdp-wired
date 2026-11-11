import {test,expect} from 'bun:test'
import {archiveProfile,readProfileArchive} from './profile-archive.ts'
test('full profile survives hash-bound archive',()=>{const value={nodes:[{id:1}],samples:[1],timeDeltas:[10]};expect(readProfileArchive(archiveProfile(value))).toEqual(value)})
test('changed compressed bytes are rejected',()=>{const value=archiveProfile({nodes:[]});value.data=Buffer.from('changed').toString('base64');expect(()=>readProfileArchive(value)).toThrow()})
test('changed declared content hash is rejected',()=>{const value=archiveProfile({nodes:[]});value.sha256='bad';expect(()=>readProfileArchive(value)).toThrow()})
test('oversized full profiles are explicitly rejected',()=>{expect(()=>archiveProfile('x'.repeat(8*1024*1024))).toThrow()})
