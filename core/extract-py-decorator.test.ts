import {expect, test} from 'bun:test'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractPython, type PyOptions} from './extract-py.ts'
import {buildLaw} from './laws.ts'
import {proveSteps} from './dsl.ts'

const extract = (source: string, options: PyOptions = {}) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-py-decorator-`)
  try {
    const file = `${dir}/counter.py`
    writeFileSync(file, source)
    const x = extractPython(file, {entry: 'Counter', methods: ['credit'], ...options, check: {runs: 8, depth: 3, states: 0, probes: false}})
    expect(x.ok).toBe(true)
    expect(x.evidence?.mismatch).toBeUndefined()
    expect(x.evidence!.requests).toBeGreaterThan(0)
    return x
  } finally { rmSync(dir, {recursive: true, force: true}) }
}

const step = (x: ReturnType<typeof extract>, expr: string, name = 'decorated credit is exact') => {
  const b = buildLaw(x, {name, expr, method: 'credit'})
  if (b.kind !== 'step') throw Error('expected a step law')
  return b.law
}
const prove = (x: ReturnType<typeof extract>, law: ReturnType<typeof step>) =>
  proveSteps(x.rule!, x.invariants ?? [], [law], {search: false})

test('Python observes the actual backing map of a stated store', () => {
  const x = extract(`class Counter:
    def __init__(self, cache):
        self.cache = cache
    def credit(self, key: str):
        n = self.cache.get(key)
        if n is None:
            n = 0
        self.cache.set(key, n + 1)
        return n + 1
`, {stores: {cache: {get: ['get'], set: ['set'], value: 'int'}}})
  const value = 'cache[key]', before = `old(${value})`
  const v = prove(x, step(x, `(${before} is None implies ${value} == 1) and (${before} is not None implies ${value} == ${before} + 1)`))
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
})

test('Python source laws use the executed scalar answer, not its request envelope', () => {
  const x = extract(`class Counter:
    def __init__(self):
        self.total = 0
    def answer(self) -> int:
        return 1
    def credit(self):
        n = self.answer()
        self.total += n
        return n
`, {answers: {answer: 'int'}})
  const v = prove(x, step(x, 'total == old(total) + answer(...) and result == answer(...)'))
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
})

const transparent = `from functools import wraps

def transparent(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        return fn(*args, **kwargs)
    return wrapper
`
const counter = (decorator = 'transparent', body = `        self.total += n
        n += 1
        return n`, param = 'n: int = 7') => `class Counter:
    def __init__(self):
        self.total = 0
    @${decorator}
    def credit(self, ${param}):
${body}
`

// A generic chain must bind the source defaults, not the wrapper's *args/**kwargs.
// The local reassignment must not overwrite the saved pre-call input.
test('Python admits a generic transparent wraps chain with default and input reassignment', () => {
  const x = extract(transparent + counter('transparent\n    @transparent'))
  const v = prove(x, step(x, 'total == old(total) + n and result == n + 1'))
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
})

test('Python admits a transparent wraps decorator with explicit parameters', () => {
  const x = extract(`from functools import wraps

def explicit(fn):
    @wraps(fn)
    def wrapper(self, n=7):
        return fn(self, n=n)
    return wrapper
` + counter('explicit'))
  const v = prove(x, step(x, 'total == old(total) + n and result == n + 1'))
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
})

test('Python admits async generic wraps, including resuming the same source frame', () => {
  // Only the decorator suspends: both extracted functions have simple bodies.
  // Awaiting bounce suspends credit, so a second call event for that SAME
  // coroutine frame must not be mistaken for a second invocation.
  const x = extract(`import asyncio
from functools import wraps

def transparent(fn):
    @wraps(fn)
    async def wrapper(*args, **kwargs):
        return await fn(*args, **kwargs)
    return wrapper

def suspending(fn):
    @wraps(fn)
    async def wrapper(*args, **kwargs):
        await asyncio.sleep(0)
        return await fn(*args, **kwargs)
    return wrapper

@suspending
async def bounce(n: int) -> int:
    return n

class Counter:
    def __init__(self):
        self.total = 0
    @transparent
    @transparent
    async def credit(self, n: int = 7):
        n = await bounce(n)
        self.total += n
        n += 1
        return n
`)
  const v = prove(x, step(x, 'total == old(total) + n and result == n + 1'))
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
})

test('Python decorated binding capture retains a genuinely omitted None default', () => {
  const x = extract(transparent + counter('transparent', `        self.total += 1
        return n is None`, 'n: None = None'))
  expect(x.read?.args.credit).toEqual([['n', {k: 'dflt'}]])
  const accepted = prove(x, step(x, 'total == old(total) + 1 and result == true'))
  expect(accepted).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(accepted.translationChecks).toBeGreaterThan(0)
  const wrong = step(x, 'result == false', 'wrong decorated None result')
  wrong.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const rejected = prove(x, wrong)
  expect(rejected).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(rejected.translationWitness?.args).toEqual([['n', {dflt: true}]])
  expect(rejected.translationWitness?.bindings).toMatchObject({n: null})
})

test('Python transparent wraps still rejects a falsely lowered law using the real input', () => {
  const x = extract(transparent + counter())
  const wrong = step(x, 'result == n + 2', 'wrong decorated result')
  wrong.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const v = prove(x, wrong)
  expect(v).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(v.why).toContain('translation error: wrong decorated result is false in the native code')
  expect(v.translationWitness?.bindings).toHaveProperty('n')
})

// These wrappers deliberately agree with replay. An output-only comparison
// cannot detect them; admission must inspect actual source entry and bindings.
const pureCounter = (decorator: string) => counter(decorator, '        return n')
for (const [name, decorator, error] of [
  ['changed arguments with a compensated result', `def adversary(fn):
    @wraps(fn)
    def wrapper(self, n=7):
        return fn(self, n=n + 1) - 1
    return wrapper
`, 'decorator changed native arguments before source method entry'],
  ['no source entry despite an identical result', `def adversary(fn):
    @wraps(fn)
    def wrapper(self, n=7):
        return n
    return wrapper
`, 'native source method entry was not observed'],
  ['two distinct source frames with an identical result', `def adversary(fn):
    @wraps(fn)
    def wrapper(self, n=7):
        fn(self, n=n)
        return fn(self, n=n)
    return wrapper
`, 'native source method entered more than once in one invocation'],
  ['a different receiver with identical arguments and result', `def adversary(fn):
    @wraps(fn)
    def wrapper(self, n=7):
        other = object.__new__(type(self))
        other.total = self.total
        return fn(other, n=n)
    return wrapper
`, 'native source method receiver differs from the called receiver'],
] as const) test(`Python decorator admission refuses ${name}`, () => {
  const x = extract(`from functools import wraps\n\n${decorator}\n${pureCounter('adversary')}`)
  const v = prove(x, step(x, 'total == old(total) and result == n'))
  expect(v).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
  expect(v.why).toContain('source translation unchecked: native observation unavailable: native parameter capture:')
  expect(v.why).toContain(error)
})

for (const [name, mutation] of [
  ['fake wrapped candidate', `    def fabricated(self, n=999):
        return n
    wrapper.__wrapped__ = fabricated`],
  ['source-position-spoofed different bytecode', `    def fabricated(self, n=7):
        return n + 1
    fn.__code__ = fabricated.__code__.replace(co_filename=fn.__code__.co_filename, co_name=fn.__code__.co_name, co_qualname=fn.__code__.co_qualname, co_firstlineno=fn.__code__.co_firstlineno)
    def wrapper(self, n=7):
        return fn(self, n=n) - 1
    wrapper.__wrapped__ = fn`],
  ['cyclic wrapped candidate', '    wrapper.__wrapped__ = wrapper'],
  ['nonfunction wrapped candidate', '    wrapper.__wrapped__ = object()'],
  ['customized signature on outer wrapper', `    import inspect
    wrapper.__signature__ = inspect.Signature()`],
  ['customized text signature on source candidate', `    fn.__text_signature__ = '($self, n=999)'`],
] as const) test(`Python decorator admission fails closed for ${name}`, () => {
  const x = extract(`from functools import wraps

def adversary(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        return fn(*args, **kwargs)
${mutation}
    return wrapper

` + pureCounter('adversary'))
  const v = prove(x, step(x, 'total == old(total) and result == n'))
  expect(v).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'unchecked'})
  expect(v.why).toContain('source translation unchecked: native observation unavailable: native parameter capture: ValueError:')
})
