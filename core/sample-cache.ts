/** A sample table for pure predicates: equal keys share evaluations, never rows or batches. */
export function samplePredicates<T, R>(groups: readonly (readonly T[])[], key: (t: T) => string, test: (t: T, row: R) => boolean) {
  const ids = new Map<string, number>(), predicates: T[] = []
  const indexed = groups.map(group => group.map(t => {
    const k = key(t), was = ids.get(k)
    if (was !== undefined) return was
    const id = predicates.length
    ids.set(k, id); predicates.push(t)
    return id
  }))
  return {
    groups: indexed,
    on(rows: readonly R[]) {
      const memo = predicates.map(() => new Uint8Array(rows.length))
      return (id: number, row: number): boolean => {
        const column = memo[id]!, was = column[row]!
        if (was) return was === 2
        const yes = test(predicates[id]!, rows[row]!)
        column[row] = yes ? 2 : 1
        return yes
      }
    },
  }
}
