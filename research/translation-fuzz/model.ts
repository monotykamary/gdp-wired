// Finite, owned source/law inputs. No production target or external service is generated.
export type Value = number | boolean | string | null | undefined | {[key: string]: Value}
export type Op = '==' | '!=' | '<' | '<=' | '>' | '>=' | '+' | '-' | '*' | 'and' | 'or' | 'implies'
export type Expr = {k: 'lit', v: number | boolean | string | null} | {k: 'undefined'} | {k: 'name', name: string} | {k: 'not', x: Expr} | {k: 'op', op: Op, a: Expr, b: Expr} | {k: 'choose', c: Expr, a: Expr, b: Expr} | {k: 'calendar', a: Expr, b: Expr, days: number, op: '<=' | '>=' | '=='}
export type Param = {name: string, type: string, domain: Value[], binding?: string}
export type Case = {id: string, family: string, source: string, entry: string, standalone: boolean, params: Param[], laws: Expr[], tags: string[], mapValues?: Value[], keys?: string[]}
export const STRIDE = 0x9e3779b9
export const mix = (input: number): number => {
  let x = input >>> 0
  x = Math.imul(x ^ (x >>> 16), 0x7feb352d)
  x = Math.imul(x ^ (x >>> 15), 0x846ca68b)
  return (x ^ (x >>> 16)) >>> 0
}
export class Random {
  constructor(public state: number) { this.state >>>= 0 }
  raw(): number { this.state = (this.state + STRIDE) >>> 0; return this.state }
  next(): number { return mix(this.raw()) }
  pick<T>(values: readonly T[]): T { return values[this.next() % values.length]! }
}
// The raw state is addition by an odd number modulo 2^32: full period, including seed zero.
// An odd modular inverse certifies gcd(STRIDE, 2^32)=1; the output mixer is also bijective
// (right-xorshifts and multiplication by odd words). This is not a claim that source texts never repeat.
export function periodCertificate() {
  const modulus = 1n << 32n, mask = modulus - 1n, a = BigInt(STRIDE)
  let inverse = 1n
  for (let i = 0; i < 5; i++) inverse = (inverse * (2n - a * inverse)) & mask
  return {period: modulus, stride: a, inverse, product: (a * inverse) & mask}
}
export const lit = (v: number | boolean | string | null): Expr => ({k: 'lit', v})
export const name = (n: string): Expr => ({k: 'name', name: n})
export const undef: Expr = {k: 'undefined'}
export const op = (o: Op, a: Expr, b: Expr): Expr => ({k: 'op', op: o, a, b})
export const not = (x: Expr): Expr => ({k: 'not', x})
export const choose = (c: Expr, a: Expr, b: Expr): Expr => ({k: 'choose', c, a, b})
export function render(x: Expr, law = false): string {
  switch (x.k) {
    case 'lit': return JSON.stringify(x.v)
    case 'undefined': return 'undefined'
    case 'name': return x.name
    case 'not': return law ? `(not (${render(x.x, true)}))` : `(!(${render(x.x)}))`
    case 'choose': return `(${render(x.c)} ? ${render(x.a)} : ${render(x.b)})`
    case 'calendar': return `((${render(x.b, true)} - ${render(x.a, true)}) ${x.op} ${x.days} business days)`
    case 'op': {
      const operators = law ? {'==': '==', '!=': '!=', and: 'and', or: 'or', implies: 'implies'} : {'==': '===', '!=': '!==', and: '&&', or: '||', implies: '||'}
      if (!law && x.op === 'implies') return `(!(${render(x.a)}) || (${render(x.b)}))`
      return `(${render(x.a, law)} ${(operators as Record<string, string>)[x.op] ?? x.op} ${render(x.b, law)})`
    }
  }
}
// Independent native oracle: no law parser, DSL terms, extracted rule, or calendar implementation is imported.
export function evaluate(x: Expr, env: Record<string, Value>): Value {
  switch (x.k) {
    case 'lit': return x.v
    case 'undefined': return undefined
    case 'name': return x.name.split('.').reduce<Value>((v, field) => typeof v === 'object' && v !== null ? v[field] : undefined, env)
    case 'not': return !evaluate(x.x, env)
    case 'choose': return evaluate(evaluate(x.c, env) ? x.a : x.b, env)
    case 'calendar': {
      const a = evaluate(x.a, env), b = evaluate(x.b, env)
      if (typeof a !== 'number' || typeof b !== 'number' || !Number.isFinite(a) || !Number.isFinite(b)) return false
      const first = Math.floor(a / 86400), last = Math.floor(b / 86400)
      let days = 0
      for (let d = Math.min(first, last) + 1; d <= Math.max(first, last); d++) {
        const weekday = new Date(d * 86400000).getUTCDay()
        if (weekday !== 0 && weekday !== 6) days += last >= first ? 1 : -1
      }
      return x.op === '<=' ? days <= x.days : x.op === '>=' ? days >= x.days : days === x.days
    }
    case 'op': {
      const a = evaluate(x.a, env)
      if (x.op === 'and') return Boolean(a) && Boolean(evaluate(x.b, env))
      if (x.op === 'or') return Boolean(a) || Boolean(evaluate(x.b, env))
      if (x.op === 'implies') return !a || Boolean(evaluate(x.b, env))
      const b = evaluate(x.b, env)
      switch (x.op) {
        case '==': return a === b
        case '!=': return a !== b
        case '+': return Number(a) + Number(b)
        case '-': return Number(a) - Number(b)
        case '*': return Number(a) * Number(b)
        case '<': return Number(a) < Number(b)
        case '<=': return Number(a) <= Number(b)
        case '>': return Number(a) > Number(b)
        case '>=': return Number(a) >= Number(b)
      }
    }
  }
}
const bool = (n: string): Param => ({name: n, type: 'boolean', domain: [false, true]})
const numeric = (n: string): Param => ({name: n, type: '0 | 1 | 2 | 3', domain: [0, 1, 2, 3]})
const choiceParam = (n: string, values: string[]): Param => ({name: n, type: values.map(v => JSON.stringify(v)).join(' | '), domain: values})
function boolExpr(r: Random, depth: number): Expr {
  if (!depth) return r.pick([name('a'), name('b'), lit(false), lit(true)])
  return r.pick([not(boolExpr(r, depth - 1)), op(r.pick(['and', 'or', '==', '!=']), boolExpr(r, depth - 1), boolExpr(r, depth - 1))])
}
function numExpr(r: Random, depth: number): Expr {
  if (!depth) return r.pick([name('a'), name('b'), lit(r.pick([0, 1, 2, 3]))])
  return op(r.pick(['+', '-']), numExpr(r, depth - 1), numExpr(r, depth - 1))
}
const equalities = (xs: Expr[]): Expr[] => xs.flatMap(x => [op('==', name('result'), x), op('!=', name('result'), x)])
function fn(id: string, family: string, params: Param[], result: string, body: Expr, laws: Expr[], tags: string[], style = 0): Case {
  const expression = render(body)
  const statements = style === 1 && body.k === 'choose' ? `if (${render(body.c)}) return ${render(body.a)}; return ${render(body.b)};` : style === 2 ? `const local = ${expression}; return local;` : `return ${expression};`
  return {id, family, source: `export function decide(${params.map(p => `${p.binding ?? p.name}: ${p.type}`).join(', ')}): ${result} { ${statements} }`, entry: 'decide', standalone: true, params, laws: [lit(true), lit(false), ...laws], tags}
}
function classScalar(c: Case): Case { return {...c, source: c.source.replace('export function decide', 'export class Decision { decide') + ' }', entry: 'Decision', standalone: false, tags: [...c.tags, 'class']} }
function mapCase(id: string, numericValue: boolean, variant: number): Case {
  const type = numericValue ? 'number' : 'boolean', values = numericValue ? [0, 1, 86400] : [false, true]
  const optional = variant === 2, test = variant === 0 ? '!value' : variant === 1 ? 'value' : 'value !== null'
  const body = optional ? 'return value;' : variant === 1 ? `if (${test}) return true; return value === undefined;` : `if (${test}) return value === undefined; return true;`
  const absent = op('==', name('result'), undef)
  const laws = [lit(true), lit(false), ...equalities([lit(false), lit(true), lit(0), undef, lit(null)]), ...[lit(null), lit(false), lit(0)].map(v => op('implies', absent, op('==', name('result'), v)))]
  if (numericValue && optional) laws.push(op('implies', absent, op('==', op('+', name('result'), lit(1)), lit(1))), op('implies', absent, op('>=', name('result'), lit(0))), op('implies', absent, {k: 'calendar', a: lit(0), b: name('result'), days: 1, op: '<='}))
  return {id, family: numericValue ? 'map-number' : 'map-boolean', source: `export class Decision { values = new Map<string, ${type}>(); put(key: string, value: ${type}) { this.values.set(key, value); } decide(key: string): ${optional ? `${type} | undefined` : 'boolean'} { const value = this.values.get(key); ${body} } }`, entry: 'Decision', standalone: false, params: [{name: 'key', type: 'string', domain: ['a', 'b']}], laws, tags: ['class', 'Map.get', numericValue ? 'number' : 'boolean', optional ? 'optional' : 'truthiness', 'strict-null'], mapValues: values, keys: ['a', 'b']}
}
export const FAMILIES = ['boolean', 'number', 'choice', 'optional', 'nullable', 'narrowing', 'record', 'record-alias', 'map-boolean', 'map-number', 'calendar', 'class-choice', 'class-optional'] as const
export function generate(seed: number, index: number): Case {
  if (!Number.isInteger(index) || index < 0 || index > 0xffffffff) throw new Error('case index outside uint32')
  const r = new Random(mix((seed >>> 0) ^ (index >>> 0))), family = FAMILIES[index % FAMILIES.length]!, id = `${seed >>> 0}:${index}`
  const style = r.next() % 3
  switch (family) {
    case 'boolean': { const body = boolExpr(r, 2); return fn(id, family, [bool('a'), bool('b')], 'boolean', body, equalities([lit(true), lit(false), name('a'), name('b'), body]), ['boolean', 'boolean-composition'], style) }
    case 'number': { const body = numExpr(r, 2); return fn(id, family, [numeric('a'), numeric('b')], 'number', body, [...equalities([lit(0), name('a'), body]), op('>=', name('result'), lit(0)), op('<=', name('result'), lit(3))], ['number', 'arithmetic'], style) }
    case 'choice': case 'class-choice': {
      const a = r.pick([['red'], ['red', 'blue'], ['blue', 'red']]), b = r.pick([['green'], ['green', 'amber'], ['blue', 'amber']])
      const body = r.pick([name('a'), lit(r.pick(b))]), params = [choiceParam('a', a), choiceParam('b', b)]
      const c = fn(id, family, params, [...new Set([...a, ...b])].map(x => JSON.stringify(x)).join(' | '), body, equalities([name('a'), name('b'), lit(r.pick(a)), lit(r.pick(b))]), ['choice', 'domain-equality'], style)
      return family === 'class-choice' ? classScalar(c) : c
    }
    case 'optional': case 'nullable': case 'class-optional': {
      const absent = family === 'nullable' ? lit(null) : undef, type = r.pick(['boolean', 'number'] as const), v = type === 'boolean' ? lit(r.pick([false, true])) : lit(r.pick([0, 1, 2]))
      const body = choose(name('flag'), v, absent), missing = op('==', name('result'), absent)
      const laws = [...equalities([v, absent, lit(null), undef]), op('implies', missing, op('==', name('result'), family === 'nullable' ? undef : lit(null))), op('implies', missing, op('==', name('result'), type === 'boolean' ? lit(false) : lit(0))), op('implies', missing, op('>=', name('result'), lit(0))), op('implies', missing, op('==', op('+', name('result'), lit(1)), lit(1)))]
      const c = fn(id, family, [bool('flag')], `${type} | ${family === 'nullable' ? 'null' : 'undefined'}`, body, laws, ['optional', family === 'nullable' ? 'nullable' : 'undefined', 'early-return', type], 1)
      return family === 'class-optional' ? classScalar(c) : c
    }
    case 'narrowing': {
      const c = fn(id, family, [bool('flag')], 'boolean', lit(true), equalities([lit(true), lit(false), name('flag')]), ['optional', 'strict-null', 'truthiness', 'early-return'])
      const absent = r.pick(['null', 'undefined']), condition = r.pick(['!value', 'value', 'value === null', 'value !== null', 'value === undefined', 'value !== undefined'])
      c.source = `export function decide(flag: boolean): boolean { const value = flag ? false : ${absent}; if (${condition}) return value === ${r.pick(['null', 'undefined'])}; return ${r.pick(['true', 'false'])}; }`
      return c
    }
    case 'record': {
      const params = [{name: 'facts', type: '{enabled: boolean}', domain: [{enabled: false}, {enabled: true}]}]
      const c = fn(id, family, params, '{value: number, failed: boolean}', lit(0), [op('==', name('result.value'), lit(r.pick([0, 1]))), op('==', name('result.failed'), name('facts.enabled')), op('!=', name('result.failed'), name('facts.enabled'))], ['record', 'record-result', 'reserved-fields'])
      c.source = `export function decide(facts: {enabled: boolean}): {value: number, failed: boolean} { return {value: ${r.pick([0, 1])}, failed: facts.enabled}; }`
      return c
    }
    case 'record-alias': return fn(id, family, [{name: 'arg', type: '{enabled: boolean}', domain: [{enabled: false}, {enabled: true}]}, {name: 'second', binding: '{enabled}', type: '{enabled: boolean}', domain: [{enabled: false}, {enabled: true}]}], 'boolean', name('arg.enabled'), equalities([name('enabled'), name('arg.enabled')]), ['record', 'destructured', 'heap-alias'], style)
    case 'map-boolean': return mapCase(id, false, r.next() % 3)
    case 'map-number': return mapCase(id, true, r.next() % 3)
    case 'calendar': {
      if (r.next() % 2 === 0) {
        const p = (n: string): Param => ({name: n, type: '0 | 86400 | 172800', domain: [0, 86400, 172800]})
        return fn(id, family, [p('a'), p('b')], 'boolean', lit(true), [
          {k: 'calendar', a: name('a'), b: name('b'), days: 2, op: '<='},
          {k: 'calendar', a: name('a'), b: name('b'), days: 0, op: '=='},
        ], ['calendar', 'number', 'finite-calendar'], style)
      }
      const body = choose(name('flag'), lit(r.pick([0, 86400, 172800])), undef)
      return fn(id, family, [bool('flag')], 'number | undefined', body, [{k: 'calendar', a: lit(0), b: name('result'), days: r.pick([0, 1, 2]), op: '<='}, op('implies', op('==', name('result'), undef), {k: 'calendar', a: lit(0), b: name('result'), days: 1, op: '<='})], ['optional', 'number', 'calendar', 'early-return'], 1)
    }
  }
}
export function controls(): Record<string, Case> {
  const p1 = fn('P1', 'choice', [choiceParam('a', ['red'])], '"green"', lit('green'), [op('==', name('result'), name('a'))], ['choice'])
  const p2 = generate(1, FAMILIES.indexOf('record-alias')); p2.id = 'P2'; p2.laws = [op('==', name('result'), name('enabled'))]
  const b1 = mapCase('B1', true, 2)
  b1.family = 'calendar'; b1.tags.push('calendar')
  p1.laws = [op('==', name('result'), name('a'))]
  b1.laws = [op('implies', op('==', name('result'), undef), {k: 'calendar', a: lit(0), b: name('result'), days: 1, op: '<='})]
  const b2 = mapCase('B2', false, 0); b2.laws = [op('==', name('result'), lit(true))]
  return {B1: b1, B2: b2, P1: p1, P2: p2}
}
export function inputs(c: Case): {args: Value[], env: Record<string, Value>, entries: [string, Value][]}[] {
  let combinations: Value[][] = [[]]
  for (const p of c.params) combinations = combinations.flatMap(xs => p.domain.map(v => [...xs, v]))
  let maps: [string, Value][][] = [[]]
  if (c.mapValues) for (const key of c.keys!) maps = maps.flatMap(entries => [entries, ...c.mapValues!.map(v => [...entries, [key, v] as [string, Value]])])
  const rows = maps.flatMap(entries => combinations.map(args => ({args, entries, env: Object.fromEntries(c.params.flatMap((p, i) => p.binding ? Object.entries(args[i] as Record<string, Value>) : [[p.name, args[i]]]))})))
  if (rows.length > 4096) throw new Error('finite native domain exceeds cap')
  return rows
}
export function native(c: Case): (args: Value[], entries: [string, Value][]) => Value {
  const js = new Bun.Transpiler({loader: 'ts', target: 'bun'}).transformSync(c.source).replace(/export\s+(?=function|class)/g, '')
  // Only this generator's owned, loop-free source is evaluated; never a model response or external source.
  // oxlint-disable-next-line typescript/no-implied-eval
  const load = new Function(`${js}; return ${c.standalone ? 'decide' : 'Decision'};`) as () => ((...args: Value[]) => Value) | (new () => {put?: (key: string, value: Value) => void, decide: (...args: Value[]) => Value})
  const target = load()
  return c.standalone ? (args) => (target as (...args: Value[]) => Value)(...args) : (args, entries) => {
    const object = new (target as new () => {put?: (key: string, value: Value) => void, decide: (...args: Value[]) => Value})()
    for (const [key, value] of entries) object.put!(key, value)
    return object.decide(...args)
  }
}
export function nativeCheck(c: Case, law: Expr) {
  const call = native(c), rows = inputs(c)
  let witness: {args: Value[], env: Record<string, Value>, entries: [string, Value][], result: Value} | undefined
  let violations = 0
  for (const row of rows) {
    const result = call(row.args, row.entries)
    if (!evaluate(law, {...row.env, result})) { violations++; witness ??= {...row, result} }
  }
  return {ok: violations === 0, checked: rows.length, violations, witness}
}
