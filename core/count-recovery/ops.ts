// Direct production operations. These helpers propose ordinary trees only;
// no profiler, environment switch, or alternative checker is involved.
export {check} from '../../kernel/kernel.ts'
export {grow,widen,rowsAt} from '../../kernel/prove.ts'
export {modelSequence} from '../../kernel/model-sequence.ts'
export {solve,refuteFast} from '../solver.ts'
export const wallSpan=<T>(_phase:string,run:()=>T):T=>run()
export const wallTree=wallSpan
