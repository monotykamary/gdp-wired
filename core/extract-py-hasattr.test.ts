import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractPython, readPython} from './extract-py.ts'
import {proveSteps} from './dsl.ts'

const hasPython = (() => { try { execFileSync('python3', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasPython ? test : test.skip
const budget = {runs: 32, depth: 5, states: 48}
const withSource = <T>(source: string, f: (file: string) => T): T => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-py-presence-`)
  try {
    const file = `${dir}/m.py`
    writeFileSync(file, source)
    return f(file)
  } finally { rmSync(dir, {recursive: true, force: true}) }
}
const init = '    def __init__(self):\n        self.total = 0\n'
const put = '    def put(self) -> int:\n        self.total += 1\n        return self.total\n'
const check = (source: string) => withSource(source, file => extractPython(file, {entry: 'Counter', methods: ['put'], check: budget}))
const checked = (source: string) => {
  const x = check(source)
  if (!x.ok) throw Error(JSON.stringify({refusals: x.refusals, evidence: x.evidence}))
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms)
  const r = x.rule!
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const law = r.stepLaw('each request increments once', (b: any, a: any) => a.total.eq(b.total.plus(1)))
  const result = proveSteps(r, x.invariants ?? [], [law])
  expect(result.proven && result.checked).toBe(true)
  return x
}
const refused = (source: string, why: RegExp) => {
  const x = check(source)
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toMatch(why)
}

for (const [name, field] of [['instance', 'total'], ['missing', 'missing'], ['method', 'put'], ['constant', 'TAG'], ['collection', 'TAGS']] as const) {
  t(`hasattr checks a literal ${name} binding without reading its value`, () => {
    const present = name !== 'missing'
    checked(`class Counter:\n    TAG = None\n    TAGS = [1, 2]\n${init}    def put(self) -> int:\n        if ${present ? '' : 'not '}hasattr(self, '${field}'):\n            self.total += 1\n        return self.total\n`)
  })
}

t('hasattr follows declaration-owned C3 through a diamond', () => {
  checked(`class Root:\n${init}class Left(Root):\n    pass\nclass Right(Root):\n    TOKEN = None\nclass Counter(Left, Right):\n    def put(self) -> int:\n        if hasattr(self, 'TOKEN'):\n            self.total += 1\n        return self.total\n`)
})

t('hasattr does not invoke a property, including one raising AttributeError', () => {
  for (const body of ['return 1', 'raise AttributeError("not present")', 'self.total += 100\n        return 1']) {
    refused(`class Counter:\n${init}    @property\n    def flag(self):\n        ${body}\n    def put(self) -> int:\n        if hasattr(self, 'flag'):\n            self.total += 1\n        return self.total\n`, /descriptor/)
  }
})

for (const binding of ['flag = Descriptor()', 'flag: object = Descriptor()', 'flag = alias = Descriptor()', 'flag, alias = (Descriptor(), 1)']) {
  t(`hasattr refuses unresolved final binding: ${binding}`, () => {
    refused(`class Descriptor:\n    def __get__(self, obj, owner):\n        obj.total += 100\n        return 1\nclass Counter:\n${init}    def flag(self) -> int:\n        return 1\n    ${binding}\n    def put(self) -> int:\n        if hasattr(self, 'flag'):\n            self.total += 1\n        return self.total\n`, /final class binding/)
  })
}

t('annotation-only and final method definitions preserve presence', () => {
  for (const bindings of ['    def flag(self):\n        return 1\n    flag: int\n', '    flag = [1]\n    def flag(self):\n        return 1\n']) {
    checked(`class Counter:\n${init}${bindings}    def put(self) -> int:\n        if hasattr(self, 'flag'):\n            self.total += 1\n        return self.total\n`)
  }
})

t('overwritten inherited method metadata cannot establish presence', () => {
  refused(`class Root:\n${init}    def flag(self) -> int:\n        return 1\nclass Counter(Root):\n    flag = object()\n    def put(self) -> int:\n        if hasattr(self, 'flag'):\n            self.total += 1\n        return self.total\n`, /final class binding/)
})

t('dynamic names, keyword calls and implicit object attributes remain refused', () => {
  for (const call of ['hasattr(self, str(self.total))', "hasattr(self, name='total')", "hasattr(self, '__class__')"]) {
    refused(`class Counter:\n${init}    def put(self) -> int:\n        if ${call}:\n            self.total += 1\n        return self.total\n`, /literal|keywords|implicit/)
  }
})

t('a duplicate final method without annotation clears the earlier return type', () => {
  withSource(`class Counter:\n${init}    def flag(self) -> int:\n        return 1\n    def flag(self):\n        return True\n${put}`, file => {
    const r = Object.values(readPython(file, ['Counter']).recs).find(r => r.short === 'Counter')!
    expect(r.rets?.flag).toBeUndefined()
  })
})

t('the final initializer supplies field types rather than an earlier definition', () => {
  checked(`class Counter:\n    def __init__(self, total: bool):\n        self.total = total\n${init}${put}`)
  withSource('class Counter:\n    def __init__(self, total: bool):\n        self.total = total\n    def __init__(self, total: int):\n        self.total = total\n' + put, file => {
    const r = Object.values(readPython(file, ['Counter']).recs).find(r => r.short === 'Counter')!
    expect(r.fields.find(f => f.name === 'total')!.t.k).toBe('int')
  })
})

for (const binding of ['__init__ = None', '__init__ = [1]']) {
  t(`entry and nested constructors reject ${binding}`, () => {
    refused(`class Counter:\n${init}    ${binding}\n${put}`, /final __init__ binding/)
    refused(`class Child:\n${init}    ${binding}\nclass Counter:\n    def __init__(self):\n        self.child = Child()\n        self.total = 0\n${put}`, /final __init__ binding/)
    refused(`class Root:\n${init}class Counter(Root):\n    ${binding}\n${put}`, /final __init__ binding/)
  })
}

t('an inherited initializer and annotation-only declaration still construct', () => {
  checked(`class Root:\n${init}class Counter(Root):\n    __init__: object\n${put}`)
})

for (const decorator of ['property', 'classmethod', 'staticmethod']) {
  t(`a ${decorator} constructor is refused`, () => {
    refused(`class Counter:\n    @${decorator}\n${init}${put}`, /decorated __init__/)
  })
}

t('unknown class construction is refused even with a syntactic initializer', () => {
  for (const prefix of ['def decorate(cls):\n    return cls\n@decorate\nclass Counter:\n', 'class Meta(type):\n    pass\nclass Counter(metaclass=Meta):\n', 'class Counter:\n    if True:\n        TAG = 1\n']) {
    refused(prefix + init + put, /known static MRO/)
  }
})

t('custom allocation and attribute hooks are refused, including inherited hooks', () => {
  for (const method of ['__new__', '__getattribute__', '__getattr__', '__setattr__', '__delattr__', '__init_subclass__']) {
    const hook = `    def ${method}(self, *args):\n        return None\n`
    refused(`class Counter:\n${hook}${init}${put}`, /custom allocation or attribute hooks/)
    refused(`class Root:\n${hook}${init}class Counter(Root):\n${put}`, /custom allocation or attribute hooks/)
  }
})
