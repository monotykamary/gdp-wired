import {expect, setDefaultTimeout, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractPython, type PyOptions} from './extract-py.ts'
import {proveSteps} from './dsl.ts'
import {envOf, inEnv} from './system.ts'
setDefaultTimeout(60_000)
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type A = any
const available = (module: string) => { try { execFileSync('python3', ['-c', `import ${module}`], {stdio: 'ignore'}); return true } catch { return false } }
const django = available('django') ? test : test.skip
const sqlalchemy = available('sqlalchemy') ? test : test.skip
const prefix = `from django.conf import settings
if not settings.configured:
    settings.configure(INSTALLED_APPS=[], DATABASES={})
import django
django.setup()
from django.db import models
class Account(models.Model):
    id = models.IntegerField(primary_key=True)
    amount = models.IntegerField()
    active = models.BooleanField()
    label = models.CharField(max_length=50)
    class Meta:
        app_label = 'gdp_test'
    def credit(self, n: int):
        self.amount += n
        return self.amount
`
const run = (code: string, opts: PyOptions) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-orm-`)
  try { writeFileSync(`${dir}/model.py`, code); return extractPython(`${dir}/model.py`, {check: {runs: 20, depth: 5, states: 50}, share: true, domains: {key: 'nat'}, ...opts}) }
  finally { rmSync(dir, {recursive: true, force: true}) }
}
const checked = (x: ReturnType<typeof extractPython>) => {
  expect(x.refusals).toEqual([])
  expect(x.ok).toBe(true)
  expect(x.evidence?.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms)
  return x
}
const python = available('sys') ? test : test.skip
python('stated optional datetime state and arguments retain None and real datetime behavior', () => {
  for (const aware of [false, true]) {
    const ty = `${aware ? 'datetime-utc' : 'datetime'} | None`
    const x = checked(run(`from datetime import datetime, timezone
class Deadline:
    def __init__(self):
        self.until = None
    def set(self, until):
        self.until = until
    def expired(self):
        return self.until is not None and self.until < datetime.now(${aware ? 'timezone.utc' : ''})
    def clear(self):
        self.until = None
`, {entry: 'Deadline', methods: ['set', 'expired', 'clear'], types: {until: ty}}))
    expect(x.notes.some(n => n.includes('millisecond-aligned'))).toBe(true)
  }
})
python('an optional datetime answer is built as a datetime, not a numeric timestamp', () => {
  checked(run(`from datetime import datetime
def remote_deadline():
    return None
class Deadline:
    def __init__(self):
        self.until = None
    def load(self):
        self.until = remote_deadline()
        return self.until is not None and self.until < datetime.now()
`, {entry: 'Deadline', methods: ['load'], types: {until: 'datetime | None'}, answers: {remote_deadline: 'datetime | None'}}))
})
python('optional datetime equality and tuple membership preserve None and zones', () => {
  for (const b of ['datetime-naive | None', 'datetime-utc | None']) checked(run(`class Handler:
    def equal(self, a, b):
        return a == b
    def member(self, a, b):
        return a in (b,)
`, {entry: 'Handler', methods: ['equal', 'member'], types: {a: 'datetime-naive | None', b}}))
})
python('non-UTC process timezone explicitly refuses stated naive dates', () => {
  const tz = process.env.TZ
  try {
    process.env.TZ = 'Etc/GMT+5'
    const x = run(`from datetime import datetime
class Handler:
    def expired(self, expiry):
        return expiry < datetime.now()
`, {entry: 'Handler', methods: ['expired'], types: {expiry: 'datetime-naive'}})
    expect(x.ok).toBe(false)
    expect(x.refusals.map(r => r.what).join(';')).toContain('UTC process timezone')
  } finally { if (tz === undefined) delete process.env.TZ; else process.env.TZ = tz }
})
python('storing a naive datetime into a stated UTC field refuses', () => {
  const x = run(`class Deadline:
    def __init__(self):
        self.until = None
    def set(self, naive):
        self.until = naive
`, {entry: 'Deadline', methods: ['set'], types: {until: 'datetime-utc | None', naive: 'datetime-naive'}})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join(';')).toContain('expected datetime-utc')
})
python('non-UTC naive clocks refuse even without a datetime boundary', () => {
  const tz = process.env.TZ
  try {
    process.env.TZ = 'Etc/GMT+5'
    const x = run(`from datetime import datetime
class Clock:
    def timestamp(self):
        return datetime.now().timestamp()
`, {entry: 'Clock', methods: ['timestamp']})
    expect(x.ok).toBe(false)
    expect(x.refusals.map(r => r.what).join(';')).toContain('UTC process timezone')
  } finally { if (tz === undefined) delete process.env.TZ; else process.env.TZ = tz }
})
python('stated UTC datetime cannot silently become naive', () => {
  const x = run(`from datetime import datetime
class Deadline:
    def check(self, until):
        return until < datetime.now()
`, {entry: 'Deadline', methods: ['check'], types: {until: 'datetime-utc'}})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join(';')).toContain('mixed aware and naive')
})

django('Django model columns initialize a real row', () => {
  const x = checked(run(prefix, {entry: 'Account', methods: ['credit']}))
  const r = x.rule!
  const amount = x.names!.find(n => n.code === 'amount' && n.role === 'state')!.rule
  const input = x.names!.find(n => n.code === 'n' && n.role === 'input')!.rule
  expect(proveSteps(r, x.invariants ?? [], [r.stepLaw('credit adds exactly the request', (b: A, a: A) => a[amount].eq(b[amount].plus(b[input])))]).proven).toBe(true)
})
django('Django keyed handlers persist only at save, and share table state', () => {
  const x = checked(run(prefix + `
def create(key: int, amount: int):
    assert key >= 0
    Account.objects.create(id=key, amount=amount, active=True, label='new')
def credit(key: int, n: int):
    assert key >= 0
    row = Account.objects.get(pk=key)
    row.amount += n
    row.save()
    return row.amount
def unsaved(key: int, n: int):
    assert key >= 0
    row = Account.objects.get(id=key)
    row.amount += n
    return Account.objects.get(pk=key).amount
def exists(key: int):
    assert key >= 0
    return Account.objects.filter(pk=key).exists()
def remove(key: int):
    assert key >= 0
    Account.objects.filter(pk=key).delete()
`, {entry: ['create', 'credit', 'unsaved', 'exists', 'remove']}))
  expect(x.model!.maps.length).toBe(1)
  const name = x.names!.find(n => n.map?.store)!
  expect(name.code).toBe('Account')
  const columns = Object.keys(x.rule!.machine.maps ?? {}).filter(n => n === name.rule || n.startsWith(`${name.rule}.`))
  const system = inEnv(x.rule!, envOf('read committed, keys expire'), {stores: [columns], own: Object.keys(x.rule!.machine.state).filter(n => x.model!.outputs.some(o => n === o || n.startsWith(`${o}$`)))})
  expect(system.level).toBe('read committed')
  expect(system.reads.length).toBeGreaterThan(0)
  expect(system.models.map(m => m.name)).toContain('read committed')
})
django('nullable columns and deleted primary keys round-trip', () => {
  checked(run(prefix.replace('amount = models.IntegerField()', 'amount = models.IntegerField(null=True)') + `
def create(key: int):
    assert key >= 0
    Account.objects.create(id=key, amount=None, active=True, label='new')
def value(key: int):
    assert key >= 0
    row = Account.objects.get(pk=key)
    if row.amount is None:
        row.amount = 0
    row.save()
    return row.amount
def remove(key: int):
    assert key >= 0
    row = Account.objects.get(pk=key)
    row.delete()
    return row.id is None
`, {entry: ['create', 'value', 'remove']}))
})

django('Django first returns a detached optional row', () => {
  checked(run(prefix + `
def lookup(key: int):
    assert key >= 0
    row = Account.objects.filter(pk=key).first()
    if row is None:
        return 0
    return row.amount
`, {entry: ['lookup']}))
})
django('Django non-key filters and primary-key mutation refuse', () => {
  for (const [body, why] of [[`Account.objects.filter(amount=key).exists()`, 'non-key filters'], [`row = Account.objects.get(pk=key)\n    row.id += 1\n    row.save()`, 'primary key']] as const) {
    const x = run(prefix + `\ndef bad(key: int):\n    ${body}\n`, {entry: ['bad']})
    expect(x.ok).toBe(false)
    expect(x.refusals.map(r => r.what).join(';')).toContain(why)
  }
})
django('Django UTC datetime columns, timezone.utc and linear relativedelta', () => {
  const code = prefix.replace('    amount = models.IntegerField()', '    amount = models.IntegerField()\n    expires = models.DateTimeField()') + `
from datetime import datetime, timezone
from dateutil.relativedelta import relativedelta
class Timed(models.Model):
    expires = models.DateTimeField()
    class Meta:
        app_label = 'gdp_test'
    def expired(self):
        return datetime.now(timezone.utc) >= self.expires
    def renew(self):
        self.expires = datetime.now(timezone.utc) + relativedelta(days=90)
`
  checked(run(code, {entry: 'Timed', methods: ['expired', 'renew']}))
  const x = run(code.replace('days=90', 'months=3'), {entry: 'Timed', methods: ['renew']})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join(';')).toContain('months')
})
django('an inherited persistence override cannot be hidden by the manager stub', () => {
  const code = prefix.replace('class Account(models.Model):', `class Mutator:
    def save(self):
        self.amount = 9
        super().save()
class Account(Mutator, models.Model):`) + `
def create(key: int):
    assert key >= 0
    row = Account.objects.create(id=key, amount=1, active=True, label='new')
    return row.amount
`
  const x = run(code, {entry: ['create']})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join(';')).toContain('inherited ORM')
})
django('an overridden framework save hook is refused before persistence is replaced', () => {
  const code = prefix.replace('    def credit', '    def save_base(self, *args, **kwargs):\n        self.amount = 9\n    def credit') + `
def create(key: int):
    assert key >= 0
    row = Account.objects.create(id=key, amount=1, active=True, label='new')
    return row.amount
`
  const x = run(code, {entry: ['create']})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join(';')).toContain('persistence behavior')
})
sqlalchemy('decorated mapped classes and cross-session transfers fail closed', () => {
  const prefix = `from sqlalchemy import Column, Integer
from sqlalchemy.orm import declarative_base, Session
Base = declarative_base()
class Account(Base):
    __tablename__ = 'account'
    id = Column(Integer, primary_key=True)
    amount = Column(Integer, nullable=False)
`
  const handler = `
def create(a: Session, b: Session, key: int):
    assert key >= 0
    row = Account(id=key, amount=1)
    a.add(row)
    b.add(row)
    b.commit()
    return row.amount
`
  const x = run(prefix + handler, {entry: ['create']})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join(';')).toContain('transferring a row')
  const decorated = prefix.replace('class Account(Base):', 'def decorate(cls):\n    return cls\n@decorate\nclass Account(Base):')
  const y = run(decorated + handler, {entry: ['create']})
  expect(y.ok).toBe(false)
  expect(y.refusals.map(r => r.what).join(';')).toContain('decorated ORM classes')
})

sqlalchemy('pending inserts are not confused with a loaded instance of their class', () => {
  const prefix = `from sqlalchemy import Column, Integer
from sqlalchemy.orm import declarative_base, Session
Base = declarative_base()
class Account(Base):
    __tablename__ = 'account'
    id = Column(Integer, primary_key=True)
    amount = Column(Integer, nullable=False)
`
  checked(run(prefix + `
def replace(session: Session, key: int):
    assert key >= 0
    row = session.get(Account, key)
    if row is None:
        return 0
    new = Account(id=key, amount=99)
    session.add(new)
    session.commit()
    return 1
`, {entry: ['replace']}))
  checked(run(prefix + `
def touch(session: Session, key: int):
    assert key >= 0
    row = session.get(Account, key)
    if row is None:
        return 0
    session.add(row)
    row.amount += 1
    session.commit()
    return row.amount
`, {entry: ['touch']}))
})

sqlalchemy('SQLAlchemy typed Session handlers flush a detached row only on commit', () => {
  checked(run(`from sqlalchemy import Column, Integer
from sqlalchemy.orm import declarative_base, Session
Base = declarative_base()
class Account(Base):
    __tablename__ = 'account'
    id = Column(Integer, primary_key=True)
    amount = Column(Integer, nullable=False)
def credit(session: Session, key: int, n: int):
    assert key >= 0
    row = session.get(Account, key)
    if row is None:
        return 0
    row.amount += n
    session.commit()
    return row.amount
`, {entry: ['credit']}))
})

sqlalchemy('SQLAlchemy declarative Column and mapped_column rows', () => {
  for (const columns of [`id = Column(Integer, primary_key=True)\n    amount = Column(Integer, nullable=False)`, `id: Mapped[int] = mapped_column(primary_key=True)\n    amount: Mapped[int] = mapped_column()`]) {
    checked(run(`from sqlalchemy import Column, Integer
from sqlalchemy.orm import declarative_base, mapped_column, Mapped
Base = declarative_base()
class Account(Base):
    __tablename__ = 'account'
    ${columns}
    def credit(self, n: int):
        self.amount += n
        return self.amount
`, {entry: 'Account', methods: ['credit']}))
  }
})
