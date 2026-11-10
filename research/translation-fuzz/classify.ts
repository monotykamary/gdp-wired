export type ProofStatus = {proven?: boolean, checked?: boolean, kernelProven?: boolean, translation?: string}
export function classify(v: ProofStatus, nativeOK: boolean, replay: boolean): string {
  if (v.proven && v.checked) {
    if (v.translation === 'unchecked' || v.translation === 'error') return 'UNSAFE_VERDICT'
    return nativeOK ? 'proven-native-valid' : 'FINDING'
  }
  if (v.translation === 'error' && nativeOK) return 'FALSE_REJECTION'
  return nativeOK ? 'model-proven-native-valid' : replay ? 'BLOCKED_FINDING' : 'MODEL_FINDING'
}
