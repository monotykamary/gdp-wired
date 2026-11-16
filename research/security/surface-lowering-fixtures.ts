import {everyKey, exists, int, nat, rule, type Cond} from '../../core/dsl.ts'
import type {Law} from '../../core/machine.ts'

export type SurfaceFixture = Readonly<{id:string, label:string, source:Cond, lowered:Law, free:readonly string[]}>

const base = (name:string) => rule(name).params({limit:nat}).state({s:0}).maps({A:0}).step(({s}) => ({s}))

export function surfaceFixtures(): SurfaceFixture[] {
  const universalRule = base('surface universal')
  let universal!: Cond
  const universalLowered = universalRule.law('all A is below limit', ({A, limit}) =>
    (universal = everyKey(k => A.at(k).atMost(limit))))

  const alternatingRule = base('surface alternation')
  let alternating!: Cond
  const alternatingLowered = alternatingRule.law('there is a cap for every A cell', ({A}) =>
    (alternating = exists(x => x.atMost(1).and(everyKey(k => A.at(k).atMost(x))))))

  const integerRule = base('surface integer aliases')
  let integerAliases!: Cond
  const integerLowered = integerRule.law('one integer is below every key', () =>
    (integerAliases = exists(int, x => everyKey(k => x.atMost(k)))))

  // The declared parameter has the historical spelling a generated binder would use.
  // The lowered key must be alpha-renamed rather than capture this free parameter.
  const collisionRule = rule('surface free bound collision').params({'key$1':nat}).state({s:0}).maps({A:0}).step(({s}) => ({s}))
  let collision!: Cond
  const collisionLowered = collisionRule.law('free key alias stays free', env =>
    (collision = everyKey(k => env.A.at(k).atMost(env['key$1']))))

  const labelRule = base('surface label')
  let labelled!: Cond
  const labelledLowered = labelRule.law('key$17', ({A}) =>
    (labelled = exists(x => x.atMost(1).and(everyKey(k => A.at(k).atMost(x))))))

  return [
    {id:'universal', label:'all A is below limit', source:universal, lowered:universalLowered, free:['limit']},
    {id:'exists-forall', label:'there is a cap for every A cell', source:alternating, lowered:alternatingLowered, free:[]},
    {id:'integer-aliases', label:'one integer is below every key', source:integerAliases, lowered:integerLowered, free:[]},
    {id:'free-bound-collision', label:'free key alias stays free', source:collision, lowered:collisionLowered, free:['key$1']},
    {id:'label', label:'key$17', source:labelled, lowered:labelledLowered, free:[]},
  ]
}

/** The public DSL deliberately refuses nested one-key universals: there is no sound one-key lowering. */
export function nestedUniversalAdmission(): Cond {
  const r = base('nested universal admission')
  let source!: Cond
  try {
    r.law('nested keys', ({A}) => (source = everyKey(i => everyKey(j => A.at(i).eq(A.at(j))))))
  } catch (error) {
    if (!(error instanceof Error) || !/nested universal keys are two keys at once/.test(error.message)) throw error
    return source
  }
  throw new Error('nested universal fixture was unexpectedly admitted')
}

export const duplicatePolicyNames = (): Law[] => {
  const [first] = surfaceFixtures()
  if (!first) throw new Error('missing fixture')
  return [{...first.lowered, name:'duplicate surface policy'}, {...first.lowered, name:'duplicate surface policy'}]
}

export type OrderedPredicate = 'membership' | 'equality' | 'order'
export type OrderedScalar = Readonly<{kind:'scalar', value:number}>
export type OrderedRecord = Readonly<{kind:'record', id:'a'|'b'|'c', rank:number}>
export type OrderedValue = OrderedScalar | OrderedRecord
export type OrderedListFixture = Readonly<{
  id:string
  valueKind:'scalar'|'record'
  predicate:OrderedPredicate
  before:readonly OrderedValue[]
  after:readonly OrderedValue[]
  source:string
  law:string
  status:'admitted'|'refused'
  refusal?:string
}>

const scalarFifo = `class FIFO:
    def __init__(self):
        self.items: list[int] = []
    def put(self, x: int):
        self.items.append(x)
    def take(self) -> int:
        return self.items.pop(0)
`

// Item intentionally has no __eq__: Python's membership is object identity here.
const recordFifo = `class Item:
    def __init__(self, rank: int):
        self.rank = rank
class FIFO:
    def __init__(self):
        self.items: list[Item] = []
    def put(self, x: Item):
        self.items.append(x)
    def take(self) -> Item:
        return self.items.pop(0)
`

const lawFor = (kind:'scalar'|'record', predicate:OrderedPredicate):string => {
  const o = kind === 'scalar' ? 'o' : 'o.rank'
  const j = kind === 'scalar' ? 'j' : 'j.rank'
  const tail = predicate === 'membership' ? 'o in self.items' : predicate === 'equality' ? `o in self.items or ${o} == ${j}` : `o in self.items or ${o} <= ${j}`
  return `forall o in old(self.items): forall j in old(self.items): ${tail}`
}

function sequences<T>(values:readonly T[], max=3):T[][] {
  const out:T[][]=[[]]
  let row:T[][]=[[]]
  for (let size=1;size<=max;size++) {
    row=row.flatMap(prefix=>values.map(value=>[...prefix,value]))
    out.push(...row)
  }
  return out
}

/**
 * Exact finite source fixtures: every sequence over three representatives at
 * sizes 0..3. This contains all distinct-value permutations and repetitions.
 * Scalar quantification is refused until values and membership are lowered
 * faithfully. Record-argument cases retain their distinct aliasing refusal.
 */
export function orderedListFixtures(): OrderedListFixture[] {
  const scalar:readonly OrderedScalar[]=[{kind:'scalar',value:0},{kind:'scalar',value:1},{kind:'scalar',value:2}]
  const record:readonly OrderedRecord[]=[{kind:'record',id:'a',rank:2},{kind:'record',id:'b',rank:1},{kind:'record',id:'c',rank:1}]
  const make=(kind:'scalar'|'record', values:readonly OrderedValue[], source:string, status:'admitted'|'refused', refusal?:string):OrderedListFixture[] =>
    sequences(values).flatMap(before => (['membership','equality','order'] as const).map(predicate => ({
      id:`ordered-${kind}-${predicate}-${before.map(value=>value.kind==='scalar'?value.value:value.id).join('')||'empty'}`,
      valueKind:kind, predicate, before, after:before.slice(1), source, law:lawFor(kind,predicate), status, ...(refusal ? {refusal} : {}),
    })))
  return [
    ...make('scalar',scalar,scalarFifo,'refused','scalar ordered list'),
    ...make('record',record,recordFifo,'refused','one object in two places'),
  ]
}
