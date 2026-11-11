// Scheduling only: no operation number or protocol name carries meaning.
export type CountOperationKind = 'leader' | 'copy' | 'replacement' | 'phase'
export function orderCountOperations<T extends {value: number, kind: CountOperationKind}>(cases: readonly T[], order: 'original' | 'cost' = 'cost'): T[] {
  const rank: Record<CountOperationKind, number> = {leader: 0, copy: 1, replacement: 2, phase: 3}
  return [...cases].sort((a, b) => (order === 'cost' ? rank[a.kind] - rank[b.kind] : 0) || a.value - b.value)
}
