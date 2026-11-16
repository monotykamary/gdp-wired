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
