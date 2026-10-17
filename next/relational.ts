// Relational laws: two machines (or two runs of one) side by side, stepped by the same requests, as one machine whose
// state is both states. Migration safety is "a and b agree on every history"; tenant isolation is "what B sees is the
// same whether or not anyone else acts". Both become ordinary laws of the product, proven by the same induction.
// The combinators moved to core/compose.ts (with interleave and refinement).
export {agree, product} from '../core/compose.ts'
