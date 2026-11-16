import {expect,test} from 'bun:test'
import {resolve} from 'node:path'

function fresh(program:string){
  const p=Bun.spawnSync([process.execPath,'-e',`import {restoreTermPrelude} from ${JSON.stringify(resolve(import.meta.dir,'proof-prelude.ts'))}; ${program}`],{stdout:'pipe',stderr:'pipe',timeout:10000})
  expect(p.exitCode).toBe(0)
  return new TextDecoder().decode(p.stdout)
}
test('term restoration is single use even with empty prelude',()=>{
  expect(fresh(`restoreTermPrelude({terms:[],identities:[]},[]);try {restoreTermPrelude({terms:[],identities:[]},[]);process.exit(2)}catch(e){console.log(e.message)}`)).toContain('single-use')
})
test('failed restoration cannot be retried',()=>{
  expect(fresh(`try {restoreTermPrelude({terms:[{}],identities:[]},[])}catch{};try {restoreTermPrelude({terms:[],identities:[]},[]);process.exit(2)}catch(e){console.log(e.message)}`)).toContain('single-use')
})
