// Fresh-worker term prelude. Fail rather than renumber process-local columns.
// This is permitted only in the separately authorized recheck process, never in
// the final native invocation. All native checks/emission follow this operation.
import {snapshotKernelTermState,termColumn} from '../../kernel/kernel.ts'
import type {E} from '../../core/machine.ts'
import type {TermPrelude} from './proof-capture.ts'

// Replay is deliberately single-use. A failed semantic replay can have interned
// a prefix of the term table: discard this process; never retry or renumber it.
let attempted=false
export function restoreTermPrelude(prelude:TermPrelude,memos:ReadonlyArray<readonly [object,unknown]>):void {
  if(attempted)throw Error('term prelude replay is single-use; discard this process')
  attempted=true
  if(snapshotKernelTermState().terms.length!==0||snapshotKernelTermState().identities.length!==0)throw Error('term prelude requires a pristine worker')
  if(!Array.isArray(prelude.terms)||!Array.isArray(prelude.identities)||prelude.terms.length!==prelude.identities.length)throw Error('incomplete ordered term prelude')
  for(let i=0;i<prelude.terms.length;i++) {
    if(!Array.isArray(prelude.identities[i])||prelude.identities[i]![1]!==i||typeof prelude.identities[i]![0]!=='string')throw Error('noncanonical term identity table')
    if(termColumn(prelude.terms[i] as E)!==`⟦${i}⟧`)throw Error(`term ordinal mismatch at ${i}`)
  }
  const same=()=>{
    const state=snapshotKernelTermState()
    if(state.terms.length!==prelude.terms.length||JSON.stringify(state.identities)!==JSON.stringify(prelude.identities))throw Error('term identity replay differs from capture')
  }
  same()
  for(const [object,metadata]of memos) {
    if(!metadata||typeof metadata!=='object'||Object.keys(metadata).length!==1||!('termId'in metadata))throw Error('unsupported graph metadata')
    const id=(metadata as {termId:unknown}).termId
    if(typeof id!=='number'||!Number.isSafeInteger(id)||id<0||id>=prelude.terms.length)throw Error('invalid retained term memo')
    if(termColumn(object as E)!==`⟦${id}⟧`)throw Error('stale or incompatible retained term memo')
  }
  same()
}
