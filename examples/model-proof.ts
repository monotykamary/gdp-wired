import type {Verdict} from '../core/dsl.ts'

// Example-only mathematical claim. This never means that a source law was
// natively validated. Refuse a known native translation error even if its
// extracted model has a kernel proof.
export const modelProven = (v: Pick<Verdict, 'proven' | 'checked' | 'kernelProven' | 'translation'>): boolean =>
  (v.proven && v.checked) || (v.kernelProven === true && v.translation === 'unchecked')
