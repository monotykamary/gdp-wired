// Profile only the untrusted call boundary. The kernel functions are unchanged.
import {check as rawCheck} from '../../kernel/kernel.ts'
import {grow as rawGrow,widen as rawWiden,rowsAt as rawRows} from '../../kernel/prove.ts'
import {modelSequence as rawModel} from '../../kernel/model-sequence.ts'
import {solve as rawSolve,refuteFast as rawFast} from '../../core/solver.ts'
import {entryProfile as p} from './entry-profile.ts'
export const check:typeof rawCheck=(...a)=>p.run('query.check',a,()=>rawCheck(...a))
export const grow:typeof rawGrow=(...a)=>p.run('query.grow',a,()=>rawGrow(...a))
export const widen:typeof rawWiden=(...a)=>p.run('query.widen',a,()=>rawWiden(...a))
export const rowsAt:typeof rawRows=(...a)=>p.run('query.rowsAt',a,()=>rawRows(...a))
export const solve:typeof rawSolve=(...a)=>p.run('query.solve',a,()=>rawSolve(...a))
export const refuteFast:typeof rawFast=(...a)=>p.run('query.refuteFast',a,()=>rawFast(...a))
export const modelSequence:typeof rawModel=(...a)=>{const q=rawModel(...a);return (...b)=>p.run('query.modelSequence',[...b,...a],()=>q(...b))}
export const wallSpan=<T>(phase:string,run:()=>T):T=>p.run('phase.'+phase,[],run)
export const wallTree=wallSpan
