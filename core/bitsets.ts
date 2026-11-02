// Finite sample rows used by the untrusted invariant search. Bits outside the
// sample's domain are zero in every operand. Inputs have the same word count.
export function bitIntersection(a: Uint32Array, b: Uint32Array): Uint32Array {
  const out = new Uint32Array(a.length)
  for (let i = 0; i < a.length; i++) out[i] = a[i]! & b[i]!
  return out
}

// Existence, rather than a materialized intersection: most candidate cubes have
// a witness near the start. No intermediate arrays or scans of later words.
export function bitIntersects(sets: readonly Uint32Array[]): boolean {
  const first = sets[0]
  if (!first) return false
  for (let i = 0; i < first.length; i++) {
    let word = first[i]!
    for (let j = 1; word !== 0 && j < sets.length; j++) word &= sets[j]![i]!
    if (word !== 0) return true
  }
  return false
}
