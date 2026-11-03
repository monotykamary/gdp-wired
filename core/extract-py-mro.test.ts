import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractPython, readPython} from './extract-py.ts'
import {proveSteps} from './dsl.ts'

const hasPython = (() => { try { execFileSync('python3', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasPython ? test : test.skip
const budget = {runs: 32, depth: 5, states: 48}
const root = 'class Root:\n    def __init__(self):\n        self.total = 0\n    def amount(self) -> int:\n        return 1\n'
const put = '    def put(self) -> int:\n        self.total += self.amount()\n        return self.total\n'
const fixture = (code: string, files: Record<string, string> = {}) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-py-mro-`)
  for (const [name, source] of Object.entries({...files, 'm.py': code})) writeFileSync(`${dir}/${name}`, source)
  return {dir, file: `${dir}/m.py`}
}
const checked = (code: string, files: Record<string, string> = {}) => {
  const {dir, file} = fixture(code, files)
  const x = extractPython(file, {root: dir, entry: 'Counter', methods: ['put'], check: budget})
  if (!x.ok) throw Error(JSON.stringify({refusals: x.refusals, evidence: x.evidence}))
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms)
  return x
}
const increment = (x: ReturnType<typeof checked>, amount: number) => {
  const r = x.rule!
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const law = r.stepLaw('the selected MRO method determines the increment', (b: any, a: any) => a.total.eq(b.total.plus(amount)))
  const result = proveSteps(r, x.invariants ?? [], [law])
  expect(result.proven).toBe(true)
}

t('leftmost own method wins over a later base inheriting the root method', () => {
  increment(checked(root + 'class Left(Root):\n    def amount(self) -> int:\n        return 2\nclass Right(Root):\n    pass\nclass Counter(Left, Right):\n' + put), 2)
})

t('a later own declaration wins over an earlier base merely inheriting the root', () => {
  increment(checked(root + 'class Left(Root):\n    pass\nclass Right(Root):\n    def amount(self) -> int:\n        return 3\nclass Counter(Left, Right):\n' + put), 3)
})

t('cooperative super visits the next sibling in the actual receiver MRO', () => {
  increment(checked(root + 'class Left(Root):\n    def amount(self) -> int:\n        return super().amount() + 2\nclass Right(Root):\n    def amount(self) -> int:\n        return super(Right, self).amount() + 4\nclass Counter(Left, Right):\n' + put), 7)
})

t('cooperative constructors visit both sibling initializers exactly once', () => {
  const source = 'class Root:\n    def __init__(self):\n        super().__init__()\n        self.total = 1\nclass Left(Root):\n    def __init__(self):\n        super().__init__()\n        self.total += 2\nclass Right(Root):\n    def __init__(self):\n        super().__init__()\n        self.total += 4\nclass Counter(Left, Right):\n    def put(self) -> int:\n        self.total += 1\n        return self.total\n'
  const x = checked(source)
  expect(x.source).toContain('7')
  increment(x, 1)
})

t('super reads a sibling scalar through a property without consulting instance fields', () => {
  const source = 'class Root:\n    STEP = 1\n    def __init__(self):\n        self.total = 0\nclass Left(Root):\n    @property\n    def STEP(self) -> int:\n        return super().STEP + 2\nclass Right(Root):\n    STEP = 4\nclass Counter(Left, Right):\n    def put(self) -> int:\n        self.total += self.STEP\n        return self.total\n'
  increment(checked(source), 6)
})

t('ordinary class-name attribute reads use the same selected scalar binding', () => {
  const source = root + 'class Left(Root):\n    STEP = 2\nclass Right(Root):\n    STEP = 4\nclass Counter(Left, Right):\n    def put(self) -> int:\n        self.total += Counter.STEP\n        return self.total\n'
  increment(checked(source), 2)
})

t('field declarations follow C3 owners rather than flattened base fields', () => {
  const source = 'class Root:\n    flag: int = 1\n    def __init__(self):\n        self.flag = self.flag\nclass Left(Root):\n    pass\nclass Right(Root):\n    flag: bool = True\nclass Counter(Left, Right):\n    def put(self) -> bool:\n        self.flag = not self.flag\n        return self.flag\n'
  const {file} = fixture(source)
  const rec = Object.values(readPython(file, ['Counter']).recs).find(r => r.short === 'Counter')!
  expect(rec.fields.find(f => f.name === 'flag')!.t.k).toBe('bool')
  checked(source)
})

t('same-named classes from different modules keep different method identities', () => {
  const files = { 'left.py': 'class Shared:\n    def __init__(self):\n        self.seed = 0\n    def amount(self) -> int:\n        return self.seed + 2\n', 'right.py': 'class Shared:\n    def __init__(self):\n        self.seed = 0\n    def amount(self) -> int:\n        return self.seed + 4\n' }
  const source = 'from left import Shared as L\nfrom right import Shared as R\nclass Counter:\n    def __init__(self):\n        self.left = L()\n        self.right = R()\n        self.total = 0\n    def put(self) -> int:\n        self.total += self.left.amount() + self.right.amount()\n        return self.total\n'
  increment(checked(source, files), 6)
})

t('an unbound class value shadows an inherited method instead of falling through', () => {
  const {file} = fixture(root + 'class Counter(Root):\n    amount = [2]\n' + put)
  const x = extractPython(file, {entry: 'Counter', methods: ['put'], check: budget})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toMatch(/no field amount|cannot be bound|not callable|shared class collection|outside/)
})

t('an inherited collection may pass through a constructor only while its value stays unread', () => {
  const source = 'class Root:\n    DEFAULTS = ["code"]\n    def __init__(self):\n        self.defaults = self.DEFAULTS\n        self.total = 0\nclass Counter(Root):\n    def put(self) -> int:\n        self.total += 1\n        return self.total\n'
  const x = checked(source)
  expect(x.notes.join('\n')).toContain('never copied or frozen')
  increment(x, 1)
})

t('shared collection contents and alias identity remain refused, not scalarized', () => {
  const base = 'class Root:\n    DEFAULTS = ["code"]\n    def __init__(self):\n        self.defaults = self.DEFAULTS\n        self.total = 0\nclass Counter(Root):\n'
  for (const body of ['        self.defaults.append("token")\n        self.total = len(self.defaults)\n', '        if self.defaults is Root.DEFAULTS:\n            self.total += 1\n']) {
    const {file} = fixture(base + '    def put(self) -> int:\n' + body + '        return self.total\n')
    const x = extractPython(file, {entry: 'Counter', methods: ['put'], check: budget})
    expect(x.ok).toBe(false)
    expect(x.refusals.map(r => r.what).join('; ')).toMatch(/shared class collection|outside|opaque/)
  }
})

t('empty variadics in inherited constructors and methods are bound, not unbound locals', () => {
  const source = 'class Root:\n    def __init__(self, **kwargs):\n        self.total = kwargs.get("start", 0)\nclass Counter(Root):\n    def put(self, *args, **kwargs) -> int:\n        if kwargs:\n            self.total += 100\n        self.total += kwargs.get("amount", 1)\n        return self.total\n'
  const x = checked(source)
  expect(x.notes.join('\n')).toContain('**kwargs is empty')
  increment(x, 1)
})

t('nonempty variadic calls are refused rather than dropping their arguments', () => {
  const source = root + 'class Counter(Root):\n    def helper(self, **kwargs):\n        self.total += kwargs.get("amount", 1)\n    def put(self) -> int:\n        self.helper(amount=10)\n        return self.total\n'
  const {file} = fixture(source)
  const x = extractPython(file, {entry: 'Counter', methods: ['put'], check: budget})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toMatch(/kwargs given|more arguments|variadic/)
})

t('object initializer arguments and non-own explicit super remain refused', () => {
  for (const init of ['super().__init__(1)', 'super(Root, self).__init__()']) {
    const {file} = fixture(root + `class Counter(Root):\n    def __init__(self):\n        ${init}\n        self.total = 0\n` + put)
    const x = extractPython(file, {entry: 'Counter', methods: ['put'], check: budget})
    expect(x.ok).toBe(false)
  }
})
