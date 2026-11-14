import {test, expect} from 'bun:test'
import {validateRigidInstance, type RigidSignature} from './rigid-instance.ts'
const V = (variable: string) => ({variable})
const signature = (): RigidSignature => ({
  sorts: {Node: 'nodes', Quorum: 'quorums', Value: 'values'},
  symbols: {member: {args: ['Node', 'Quorum']}},
  axioms: [{name: 'intersection', forall: [{name: 'q1', sort: 'Quorum'}, {name: 'q2', sort: 'Quorum'}], exists: {name: 'n', sort: 'Node'}, body: [
    {relation: 'member', args: [V('n'), V('q1')]}, {relation: 'member', args: [V('n'), V('q2')]},
  ]}],
})
const data = (nodes = 4, quorums = 2, member = [1, 1, 1, 0, 0, 1, 0, 0]) => ({params: {nodes, quorums, values: 0}, tables: {member}})
const bind = (d: {params: Record<string, number>, tables: Record<string, number[]>} = data(), s = signature()) => validateRigidInstance(s, JSON.stringify(d), () => {})

test('intersecting half-size quorums are valid without a majority premise', () => {
  const x = bind()
  expect(x.witness('intersection', [0, 1])).toBe(0)
  expect(x.witnesses[0]!.table.values).toEqual([0, 0, 0, 0])
  expect(x.read('member', [1, 1])).toBe(0)
})
test('smallest witness and duplicate-extension quorum names are deterministic', () => {
  const d = data(5, 2, [0, 0, 1, 1, 0, 0, 1, 1, 0, 0])
  expect(bind(d).witnesses[0]!.table.values).toEqual([1, 1, 1, 1])
  expect(bind(d).witnesses).toEqual(bind(d).witnesses)
})
test('disjoint quorums reject after diagonal instances pass', () => {
  expect(() => bind(data(2, 2, [1, 0, 0, 1]))).toThrow('no witness at (0, 1)')
})
test('empty quorum domain is vacuous; inhabited quorum with empty nodes rejects', () => {
  expect(bind(data(0, 0, [])).witnesses[0]!.table.values).toEqual([])
  expect(bind(data(3, 0, [])).witnesses[0]!.table.values).toEqual([])
  expect(() => bind(data(0, 1, []))).toThrow('no witness')
})
test('no 64-element or positive-value-sort assumption', () => {
  const table = Array.from({length: 140}, (_, i) => i % 2 === 0 ? Number(i / 2 <= 35) : Number((i - 1) / 2 >= 35))
  const x = bind(data(70, 2, table))
  expect(x.params.values).toBe(0)
  expect(x.witness('intersection', [0, 1])).toBe(35)
  expect(x.read('member', [69, 1])).toBe(1)
})
test('interpretation and witness tables are privately copied and frozen', () => {
  const d = data(), s = signature(), x = bind(d, s)
  d.tables.member[0] = 0
  ;(s.symbols.member!.args as string[])[0] = 'Value'
  expect(x.read('member', [0, 0])).toBe(1)
  expect(() => { (x.params as Record<string, number>).nodes = 99 }).toThrow()
  expect(() => { (x.witnesses[0]!.table.values as number[])[0] = 3 }).toThrow()
  expect(Object.isFrozen(x)).toBe(true)
  expect(() => new (x.constructor as any)(Symbol('fake'), {}, {}, [])).toThrow('must pass validation')
})
test('lookup cannot escape its declared arity or domain', () => {
  const x = bind()
  for (const args of [[0], [0, 0, 0], [-1, 0], [0.5, 0], [4, 0], [0, 2]]) expect(() => x.read('member', args)).toThrow()
  expect(() => x.read('missing', [0, 0])).toThrow('unknown rigid symbol')
})
test('relations reject partial, non-natural and non-Boolean tables', () => {
  expect(() => bind(data(4, 2, [1]))).toThrow('exactly 8 cells')
  for (const bad of [2, -1, 0.5, null]) {
    const d: any = data(); d.tables.member[0] = bad
    expect(() => bind(d)).toThrow()
  }
})
test('functions are range-checked, including empty codomains and domains', () => {
  const s = signature(); (s.symbols as any).label = {args: ['Node'], result: 'Value'}
  const d: any = data(); d.params.values = 2; d.tables.label = [1, 0, 1, 0]
  expect(bind(d, s).read('label', [0])).toBe(1)
  d.tables.label[0] = 2; expect(() => bind(d, s)).toThrow('outside its result kind')
  d.params.values = 0; d.tables.label = [0, 0, 0, 0]; expect(() => bind(d, s)).toThrow('outside its result kind')
  expect(bind({...data(0, 0, []), tables: {member: [], label: []}}, s).witnesses[0]!.table.values).toEqual([])
})
test('typed function terms are allowed in the original axiom body', () => {
  const s = signature(); (s.symbols as any).identity = {args: ['Node'], result: 'Node'}
  ;(s.axioms[0]!.body[0]!.args as any[])[0] = {call: 'identity', args: [V('n')]}
  const d: any = data(); d.tables.identity = [0, 1, 2, 3]
  expect(bind(d, s).witness('intersection', [0, 1])).toBe(0)
})
test('undeclared, captured, wrongly sorted, and duplicate axiom bindings reject', () => {
  const variants: RigidSignature[] = []
  let s = signature(); (s.axioms[0]!.forall as any)[1].name = 'q1'; variants.push(s)
  s = signature(); (s.axioms[0]!.body[0]!.args as any[])[0] = V('missing'); variants.push(s)
  s = signature(); (s.axioms[0]!.body[0]!.args as any[])[0] = V('q1'); variants.push(s)
  s = signature(); (s.axioms as any[]).push(s.axioms[0]); variants.push(s)
  for (const v of variants) expect(() => bind(data(), v)).toThrow()
})
test('fresh deterministic witness names do not overwrite an existing symbol', () => {
  const s = signature(); (s.symbols as any)['intersection$choice'] = {args: ['Node', 'Quorum']}
  const d: any = data(); d.tables['intersection$choice'] = [...d.tables.member]
  expect(bind(d, s).witnesses[0]!.name).toBe('intersection$choice2')
})
test('unknown input fields and undeclared tables/parameters reject', () => {
  const variants: any[] = [{...data(), callbacks: {}}, {...data(), params: {...data().params, extra: 1}}, {...data(), tables: {...data().tables, extra: []}}]
  for (const v of variants) expect(() => bind(v)).toThrow('unknown field')
  expect(() => validateRigidInstance(signature(), '{bad json', () => {})).toThrow()
  expect(() => bind({...data(), params: {...data().params, nodes: Number.MAX_SAFE_INTEGER + 1}})).toThrow('safe natural')
})
test('cancellation aborts atomically before or during exact enumeration', () => {
  expect(() => validateRigidInstance(signature(), JSON.stringify(data()), () => { throw Error('cancel') })).toThrow('cancel')
  let n = 0
  expect(() => validateRigidInstance(signature(), JSON.stringify(data(300, 1, Array(300).fill(1))), () => { if (++n === 2) throw Error('cancel in table') })).toThrow('cancel in table')
})
