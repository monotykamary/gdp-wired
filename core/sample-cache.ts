import type {State} from './machine.ts'

/** The sampling key, byte-for-byte like the nested-array JSON, without allocating an array for every cell. */
export function sampleStateText(params: Record<string, number>, st: State, defaults: Record<string, number>) {
  const number = (n: number) => Number.isFinite(n) ? String(n) : 'null'
  let maps = '', between = ''
  for (const mp of Object.keys(st.maps)) {
    const cells = st.maps[mp]!, d = st.defaults?.[mp] ?? defaults[mp] ?? 0, keys: number[] = []
    cells.forEach((v, k) => { if (v !== d) keys.push(k) })
    keys.sort((a, b) => a - b)
    let text = '', comma = ''
    for (const k of keys) { text += `${comma}[${number(k)},${number(cells.get(k)!)}]`; comma = ',' }
    maps += `${between}[${text}]`; between = ','
  }
  return `[${JSON.stringify(params)},${JSON.stringify(st.scalars)},[${maps}],${JSON.stringify(st.defaults ?? null)}]`
}

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
