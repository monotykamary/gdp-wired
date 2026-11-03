// The Rust front end (core/extract-rs.ts on core/extract-step.ts): rules read from Rust, each checked against the crate
// it was read from (built by cargo beside a generated harness, overflow checks on). The cases: a u8 that traps past
// its range, a wrapping and a checked one, an Option field, a Result's Err as the failure, a C-like enum and its
// discriminant, an atomic's fetch_add, and the refusals (a loop, a map in the state). Skipped where cargo isn't
// installed (research/langs/rust/rust-setup.sh installs it in a job).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractRust, readRust} from './extract-rs.ts'
import {extractStep} from './extract-step.ts'
import {proveRule, proveSteps} from './dsl.ts'

const hasCargo = (() => { try { execFileSync('cargo', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasCargo ? test : test.skip
const DIR = new URL('./rs/examples/limits', import.meta.url).pathname
const budget = {runs: 40, depth: 8, states: 80}
const genericCrate = (code: string) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-rs-generics-`)
  mkdirSync(`${dir}/src`)
  writeFileSync(`${dir}/Cargo.toml`, '[package]\nname = "generic_meter"\nversion = "0.1.0"\nedition = "2021"\n')
  writeFileSync(`${dir}/src/lib.rs`, code)
  return dir
}

t('Rust atomic ordering: typed load and store retain invalid-order failures', () => {
  const dir = genericCrate(`use std::sync::atomic::{AtomicU32, Ordering};
    pub struct Meter { value: AtomicU32 }
    impl Meter {
      pub fn new() -> Self { Self { value: AtomicU32::new(7) } }
      pub fn load(&self, ordering: Ordering) -> u32 { self.value.load(ordering) }
      pub fn store(&self, value: u32, ordering: Ordering) { self.value.store(value, ordering); }
    }
  `)
  const x = ok(extractRust(dir, {entry: 'Meter', check: budget, failures: 'kept', strict: true, share: false}))
  expect(x.source).toContain("'Relaxed', 'Release', 'Acquire', 'AcqRel', 'SeqCst'")
  expect(x.notes.join('\n')).toContain("calls that don't interleave")
  const load = step(x, 'load never changes the atomic value', (b, a) => a.value.eq(b.value), b => b.method.is('load'))
  expect(load).toMatchObject({proven: true, checked: true})
  const store = step(x, 'failed store leaves the atomic value unchanged', (b, a) => a.failed.implies(a.value.eq(b.value)), b => b.method.is('store'))
  expect(store).toMatchObject({proven: true, checked: true})
  for (const method of ['load', 'store']) {
    const invalid = (b: A) => b[`${method}_ordering`].is(method === 'load' ? 'Release' : 'Acquire').or(b[`${method}_ordering`].is('AcqRel'))
    expect(step(x, `${method} fails exactly on invalid ordering`, (b, a) => invalid(b).implies(a.failed).and(a.failed.implies(invalid(b))), b => b.method.is(method))).toMatchObject({proven: true, checked: true})
  }
  expect(step(x, 'successful store keeps the supplied value', (b, a) => a.failed.not().implies(a.value.eq(b.store_value)), b => b.method.is('store'))).toMatchObject({proven: true, checked: true})
  const r = x.rule!, runtime = r.interpreter(), params = r.encodeParams({})
  for (const method of ['load', 'store']) for (const order of ['Relaxed', 'Release', 'Acquire', 'AcqRel', 'SeqCst']) {
    const invalid = order === 'AcqRel' || order === (method === 'load' ? 'Release' : 'Acquire')
    const next = runtime.step(params, runtime.init(params), r.encodeInput({method, load_ordering: order, store_ordering: order, store_value: 11}))
    expect(r.decode(next)).toMatchObject({value: method === 'store' && !invalid ? 11 : 7, failed: invalid})
  }
}, 300_000)

t('Rust atomic ordering: fully qualified standard types do not use a local Ordering enum', () => {
  const dir = genericCrate(`pub enum Ordering { Custom }
    pub struct Meter { value: core::sync::atomic::AtomicU16 }
    impl Meter {
      pub fn new() -> Self { Self { value: core::sync::atomic::AtomicU16::new(7) } }
      pub fn load(&self, order: core::sync::atomic::Ordering) -> u16 { self.value.load(order) }
      pub fn ordinal(&self, order: core::sync::atomic::Ordering) -> u8 { order as u8 }
    }
  `)
  ok(extractRust(dir, {entry: 'Meter', check: budget, failures: 'kept', strict: true}))
}, 300_000)

t('Rust atomic ordering: nonstandard enum values stay their own and dynamic RMW remains refused', () => {
  const own = genericCrate(`#[derive(Clone, Copy, Debug)] pub enum Ordering { First, Second }
    pub struct Meter { value: u8 }
    impl Meter {
      pub fn new() -> Self { Self { value: 0 } }
      pub fn choose(&mut self, order: Ordering) { self.value = match order { Ordering::First => 1, Ordering::Second => 2 }; }
    }
  `)
  const x = ok(extractRust(own, {entry: 'Meter', check: budget, strict: true}))
  expect(x.source).not.toContain('Relaxed')
  const dynamic = genericCrate(`use std::sync::atomic::{AtomicU32, Ordering};
    pub struct Meter { value: AtomicU32 }
    impl Meter {
      pub fn new() -> Self { Self { value: AtomicU32::new(0) } }
      pub fn add(&self, n: u32, order: Ordering) -> u32 { self.value.fetch_add(n, order) }
    }
  `)
  const refused = extractRust(dynamic, {entry: 'Meter', check: budget, strict: true})
  expect(refused.ok).toBe(false)
  expect(refused.refusals.length).toBeGreaterThan(0)
}, 300_000)

t('Rust atomic ordering: argument effects survive an invalid-order failure', () => {
  const dir = genericCrate(`use std::sync::atomic::{AtomicU32, Ordering};
    pub struct Meter { value: AtomicU32, seen: u8 }
    impl Meter {
      pub fn new() -> Self { Self { value: AtomicU32::new(7), seen: 0 } }
      pub fn store(&mut self, n: u32, order: Ordering) {
        self.value.store({ self.seen = self.seen.wrapping_add(1); n }, order);
      }
    }
  `)
  const x = ok(extractRust(dir, {entry: 'Meter', check: budget, failures: 'kept', strict: true}))
  const r = x.rule!, runtime = r.interpreter(), params = r.encodeParams({})
  for (const order of ['Acquire', 'Release']) {
    const next = runtime.step(params, runtime.init(params), r.encodeInput({n: 11, order}))
    expect(r.decode(next)).toMatchObject({seen: 1, value: order === 'Acquire' ? 7 : 11, failed: order === 'Acquire'})
  }
}, 300_000)

t('Rust atomic sequencing: capture an earlier read before the later argument mutates it', () => {
  const dir = genericCrate(`use std::sync::atomic::{AtomicU32, Ordering};
    pub struct Meter { value: AtomicU32, seen: u32 }
    impl Meter {
      pub fn new() -> Self { Self { value: AtomicU32::new(7), seen: 0 } }
      pub fn store(&mut self, order: Ordering) {
        self.value.store(self.seen, { self.seen = self.seen.wrapping_add(1); order });
      }
    }
  `)
  const x = ok(extractRust(dir, {entry: 'Meter', check: budget, failures: 'kept', strict: true}))
  const r = x.rule!, runtime = r.interpreter(), params = r.encodeParams({})
  for (const order of ['Relaxed', 'Release', 'Acquire', 'AcqRel', 'SeqCst']) {
    const failed = order === 'Acquire' || order === 'AcqRel'
    const state = runtime.step(params, runtime.init(params), r.encodeInput({order}))
    expect(r.decode(state)).toMatchObject({value: failed ? 7 : 0, seen: 1, failed})
  }
  const request = r.encodeInput({order: 'Release'})
  const first = runtime.step(params, runtime.init(params), request)
  expect(r.decode(runtime.step(params, first, request))).toMatchObject({value: 1, seen: 2, failed: false})
}, 300_000)

t('Rust atomic sequencing: an earlier argument failure prevents later argument effects', () => {
  const dir = genericCrate(`use std::sync::atomic::{AtomicU32, Ordering};
    pub struct Meter { value: AtomicU32, seen: u32, operand: u32 }
    impl Meter {
      pub fn new(start: u32) -> Self { Self { value: AtomicU32::new(7), seen: 0, operand: start } }
      pub fn store(&mut self, order: Ordering) {
        self.value.store(self.operand + 1u32, { self.seen = self.seen.wrapping_add(1); order });
      }
    }
  `)
  const x = ok(extractRust(dir, {entry: 'Meter', check: budget, failures: 'kept', strict: true}))
  const r = x.rule!, runtime = r.interpreter()
  for (const start of [0, 1, 4_294_967_295]) for (const order of ['Relaxed', 'Release', 'Acquire', 'AcqRel', 'SeqCst']) {
    const params = r.encodeParams({start}), overflow = start === 4_294_967_295
    const failed = overflow || order === 'Acquire' || order === 'AcqRel'
    const state = runtime.step(params, runtime.init(params), r.encodeInput({order}))
    expect(r.decode(state)).toMatchObject({value: failed ? 7 : start + 1, seen: overflow ? 0 : 1, failed})
  }
}, 300_000)

t('Rust atomic sequencing: variable division remains refused', () => {
  const dir = genericCrate(`use std::sync::atomic::{AtomicU32, Ordering};
    pub struct Meter { value: AtomicU32, seen: u32, divisor: u32 }
    impl Meter {
      pub fn new(divisor: u32) -> Self { Self { value: AtomicU32::new(7), seen: 0, divisor } }
      pub fn store(&mut self, order: Ordering) {
        self.value.store(10u32 / self.divisor, { self.seen = self.seen.wrapping_add(1); order });
      }
    }
  `)
  const x = extractRust(dir, {entry: 'Meter', check: budget, failures: 'kept', strict: true})
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toContain("division by a value that isn't a constant")
}, 120_000)

t('Rust atomic ordering: unresolved aliases and wildcard imports remain refused', () => {
  for (const [imports, order] of [
    ['use std::sync::atomic::*;', 'Ordering'],
    ['use std::sync::atomic::{AtomicU32, Ordering as Order};', 'Order'],
  ]) {
    const dir = genericCrate(`${imports}
      pub struct Meter { value: AtomicU32 }
      impl Meter {
        pub fn new() -> Self { Self { value: AtomicU32::new(0) } }
        pub fn load(&self, ordering: ${order}) -> u32 { self.value.load(ordering) }
      }
    `)
    const x = extractRust(dir, {entry: 'Meter', check: budget, strict: true})
    expect(x.ok).toBe(false)
    expect(x.refusals.length).toBeGreaterThan(0)
  }
}, 120_000)

t('Rust atomic ordering: an explicit crate alias cannot masquerade as std or core', () => {
  for (const root of ['std', 'core']) {
    const dir = genericCrate(`extern crate other as ${root};
      pub struct Meter { value: u32 }
      impl Meter { pub fn load(&self, order: ::${root}::sync::atomic::Ordering) -> u32 { self.value } }
    `)
    const mod = readRust(dir, ['Meter'])
    const order = mod.funcs['Meter::load']!.params.find(p => p.name === 'order')!
    expect(order.t.k).toBe('opaque')
  }
}, 120_000)

t('Rust primitive extrema: every integer width replays its native associated min and max', () => {
  const types = ['u8', 'u16', 'u32', 'u64', 'u128', 'usize', 'i8', 'i16', 'i32', 'i64', 'i128', 'isize']
  const dir = genericCrate(`
    pub struct Meter { ${types.flatMap(t => [`lo_${t}: ${t}`, `hi_${t}: ${t}`]).join(',')} }
    impl Meter {
      pub fn new() -> Self { Self { ${types.flatMap(t => [`lo_${t}: 0`, `hi_${t}: 0`]).join(',')} } }
      ${types.map(t => `pub fn choose_${t}(&mut self, a: ${t}, b: ${t}) { self.lo_${t} = ${t}::min(a, b); self.hi_${t} = ${t}::max(a, b); }`).join('\n')}
    }
  `)
  const x = ok(extractRust(dir, {entry: 'Meter', check: budget, strict: true}))
  expect(x.notes.join('\n')).not.toMatch(/answered|left out/)
  expect(x.evidence!.requests).toBeGreaterThan(0)
}, 300_000)

t('Rust primitive extrema: a same-named user type keeps the declared call', () => {
  const dir = genericCrate(`
    #[allow(non_camel_case_types)] pub struct usize;
    impl usize { pub fn min(_a: u8, b: u8) -> u8 { b } }
    pub struct Meter { value: u8 }
    impl Meter {
      pub fn new() -> Self { Self { value: 0 } }
      pub fn choose(&mut self, a: u8, b: u8) { self.value = usize::min(a, b); }
    }
  `)
  const body = JSON.stringify(readRust(dir, ['Meter']).funcs['Meter::choose'])
  expect(body).not.toContain('"builtin"')
  expect(body).toContain('usize::min')
}, 300_000)

t('Rust primitive extrema: aliases, modules and glob imports do not authorize primitive lowering', () => {
  for (const declaration of [
    'type usize = u8;',
    'mod custom { pub struct Limit; } use custom::Limit as usize;',
    'mod usize { pub fn min(a: u8, _b: u8) -> u8 { a } }',
    'mod custom {} use custom::*;',
    'extern crate custom as usize;',
    '#![no_implicit_prelude]',
  ]) {
    const dir = genericCrate(`${declaration}
      pub struct Meter { value: u8 }
      impl Meter { pub fn choose(&mut self, a: u8, b: u8) { self.value = usize::min(a, b); } }
    `)
    expect(JSON.stringify(readRust(dir, ['Meter']).funcs['Meter::choose'])).not.toContain('"builtin"')
  }
}, 120_000)

t('Rust lifetime parameters do not masquerade as type or const parameters', () => {
  const dir = genericCrate(`
    pub struct Borrowed<'a> { value: &'a u8 }
    pub struct Typed<T> { value: T }
    pub struct Fixed<const N: usize> { value: [u8; N] }
    pub fn borrowed<'a>(value: &'a u8) -> u8 { *value }
    pub fn typed<T>(value: T) -> T { value }
    pub fn fixed<const N: usize>() -> usize { N }
  `)
  const mod = readRust(dir, ['Borrowed', 'Typed', 'Fixed', 'borrowed', 'typed', 'fixed'])
  expect(mod.recs.Borrowed!.kinds.some(k => k.startsWith('generic:'))).toBe(false)
  expect(mod.recs.Typed!.kinds.some(k => k.startsWith('generic:'))).toBe(true)
  expect(mod.recs.Fixed!.kinds.some(k => k.startsWith('generic:'))).toBe(true)
  expect(Object.values(mod.funcs).find(f => f.name === 'borrowed')).toHaveProperty('generic', false)
  expect(Object.values(mod.funcs).find(f => f.name === 'typed')).toHaveProperty('generic', true)
  expect(Object.values(mod.funcs).find(f => f.name === 'fixed')).toHaveProperty('generic', true)
}, 120_000)

t('Rust lifetime-bearing methods retain original-code replay', () => {
  const dir = genericCrate(`
    pub struct Meter { used: u8 }
    impl Meter {
      pub fn new() -> Self { Self { used: 0 } }
      pub fn add<'a>(&'a mut self, amount: u8) {
        self.used = self.used.wrapping_add(amount);
      }
      pub fn clear<'a: 'b, 'b>(&'a mut self) { self.used = 0; }
    }
  `)
  const x = extractRust(dir, {entry: 'Meter', methods: ['add', 'clear'], check: budget})
  expect(x.ok).toBe(true)
  expect(x.evidence?.requests).toBeGreaterThan(0)
}, 120_000)

t('Rust lifetime parameters do not authorize unsupported borrowed fields', () => {
  const dir = genericCrate(`
    pub struct Borrowed<'a> { bytes: &'a [u8], used: u8 }
    impl<'a> Borrowed<'a> {
      pub fn new(bytes: &'a [u8]) -> Self { Self { bytes, used: 0 } }
      pub fn advance(&mut self) { self.used = self.used.wrapping_add(1); }
    }
  `)
  const x = extractRust(dir, {entry: 'Borrowed', check: budget})
  expect(x.ok).toBe(false)
  expect(x.refusals.length).toBeGreaterThan(0)
  expect(x.refusals.every(r => !r.what.includes('a generic type'))).toBe(true)
}, 120_000)

t('Rust lifetime parameters do not erase mixed type or const method parameters', () => {
  for (const method of [
    "pub fn add<'a, T>(&'a mut self, amount: u8, value: T) { self.used = amount; }",
    "pub fn add<'a, const N: usize>(&'a mut self, amount: u8) { self.used = amount; }",
  ]) {
    const dir = genericCrate(`pub struct Meter { used: u8 } impl Meter {
      pub fn new() -> Self { Self { used: 0 } } ${method}
    }`)
    const x = extractRust(dir, {entry: 'Meter', methods: ['add'], check: budget})
    expect(x.ok).toBe(false)
    expect(x.refusals.some(r => r.what.includes('generic'))).toBe(true)
  }
}, 120_000)

t('Rust unresolved type and const parameters remain refused', () => {
  for (const declaration of [
    'pub struct Meter<T> { value: T }',
    'pub struct Meter<const N: usize> { value: [u8; N] }',
  ]) {
    const x = extractRust(genericCrate(declaration), {entry: 'Meter', check: budget})
    expect(x.ok).toBe(false)
    expect(x.refusals.some(r => r.what.includes('a generic type'))).toBe(true)
  }
}, 120_000)

for (const [name, initial, body, expected] of [
  ['plain arguments', 7, 'self.value = first(self.seen, 0);', {value: 0, seen: 0}],
  ['earlier read before later effects', 7, 'self.value = first(self.seen, { self.seen = self.seen.wrapping_add(1); 0 });', {value: 0, seen: 1}],
  ['each prelude before its own value', 7, 'self.value = first({ self.seen = self.seen.wrapping_add(1); self.seen }, { self.seen = self.seen.wrapping_add(1); 0 });', {value: 1, seen: 2}],
  ['earlier failure before later effects', 4_294_967_295, 'self.value = first(self.value + 1u32, { self.seen = self.seen.wrapping_add(1); 0 });', {value: 4_294_967_295, seen: 0, failed: true}],
  ['local callable shadows the free function', 7, 'let first = |a: u32, _b: u32| a.wrapping_add(10); self.value = first(self.seen, 0);', {value: 10, seen: 0}],
] as const) t(`Rust free calls: ${name}`, () => {
  const dir = genericCrate(`fn first(a: u32, _b: u32) -> u32 { a }
    pub struct Meter { value: u32, seen: u32 }
    impl Meter {
      pub fn new() -> Self { Self { value: ${initial}, seen: 0 } }
      pub fn take(&mut self) { ${body} }
    }
  `)
  const x = ok(extractRust(dir, {entry: 'Meter', check: budget, failures: 'kept', strict: true}))
  const r = x.rule!, runtime = r.interpreter(), params = r.encodeParams({})
  expect(r.decode(runtime.step(params, runtime.init(params), r.encodeInput({})))).toMatchObject(expected)
}, 300_000)

type X = ReturnType<typeof extractRust>
const ok = (x: X) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}\n${JSON.stringify(x.evidence)}`)
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type A = any
const step = (x: X, name: string, then: (b: A, a: A) => A, when?: (b: A) => A) => proveSteps(x.rule as A, x.invariants ?? [], [(x.rule as A).stepLaw(name, then, when)])

t('integers of a width: + traps past it (the failure), wrapping_add wraps, checked_add is an Option', () => {
  const x = ok(extractRust(DIR, {entry: 'Budget', methods: ['spend', 'lap', 'try_spend', 'mark'], failures: 'kept', check: budget}))
  expect(x.notes.join('\n')).toMatch(/past u8's range \(a panic/)
  expect(proveRule(x.rule!, [...x.invariants!, x.rule!.law('spent within the limit', ({spent, limit}: A) => spent.atMost(limit))]).proven).toBe(true)
  expect(step(x, 'a lap wraps at 256', (b, a) => a.laps.eq(0), b => b.method.is('lap').and(b.laps.eq(255))).proven).toBe(true)
  expect(step(x, 'mark keeps the phase', (b, a) => a.phase.eq(b.mark_p).and(a.phase_none.not()), b => b.method.is('mark')).proven).toBe(true)
}, 120_000)

t('a C-like enum, its discriminant, an Err returned, an atomic counter', () => {
  const x = ok(extractRust(DIR, {entry: 'Job', methods: ['start', 'finish'], failures: 'kept', check: budget}))
  expect(x.source).toContain("phase: oneOf('Idle', 'Running', 'Done')")
  expect(step(x, 'finish only from running', (b, a) => a.failed.not().implies(b.phase.is('Running').and(a.finish_result.eq(2))), b => b.method.is('finish')).proven).toBe(true)
  expect(step(x, 'a start counts one', (b, a) => a.start_result.implies(a.hits.eq(b.hits.plus(1))), b => b.method.is('start').and(b.hits.lt(1000))).proven).toBe(true)
}, 120_000)

t('refusals, each where it is with why', () => {
  const loop = extractRust(DIR, {entry: 'Tally', methods: ['add_all']})
  expect(loop.ok).toBe(false)
  expect(loop.refusals[0]!.what).toMatch(/a loop/)
  const map = extractRust(DIR, {entry: 'Ledger', methods: []})
  expect(map.ok).toBe(false)
}, 120_000)

t('the boundary inferred: other crates\' calls left out or answered (tagged: their types aren\'t read), the entry', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-rscase-`)
  mkdirSync(`${dir}/src`)
  writeFileSync(`${dir}/Cargo.toml`, '[package]\nname = "meter"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\npath = "src/lib.rs"\n')
  writeFileSync(`${dir}/src/lib.rs`, `pub struct Meter { used: u32, cap: u32 }
impl Meter {
    pub fn new(cap: u32) -> Self { Meter { used: 0, cap } }
    pub fn take(&mut self, n: u32) -> bool {
        std::thread::yield_now();
        let extra: u32 = std::process::id(); // gdp: answer u32
        if n > self.cap || extra > self.cap - n || self.used > self.cap - n - extra { return false; }
        self.used += n + extra;
        true
    }
}
`)
  const x = ok(extractRust(dir, {check: budget}))
  const notes = x.notes.join('\n')
  expect(notes).toMatch(/the entry inferred: Meter/)
  expect(notes).toMatch(/std::thread::yield_now .*left out \(inferred/)
  expect(notes).toMatch(/std::process::id .*answered by the request \(tagged/)
  expect(step(x, 'never past its cap', (_b, a) => a.used.atMost(a.cap), b => b.used.atMost(b.cap)).proven).toBe(true)
}, 300_000)

// The check's build (the code with the harness): a compiler failing with nothing to say of the code (killed, past
// GDP_COMPILE_S) is retried once, then the check's harness failure; its errors about the code, the source refused with
// its message. Never "the rule and the code differ".
const killedBuild = <X>(make: () => X): X => { const old = process.env.GDP_COMPILE_S; process.env.GDP_COMPILE_S = '0.001'; try { return make() } finally { if (old === undefined) delete process.env.GDP_COMPILE_S; else process.env.GDP_COMPILE_S = old } }
t('the check\'s build: a crate rustc rejects refused with its message; cargo killed is the harness\'s failure, retried once', () => {
  const crate = (code: string) => { const d = mkdtempSync(`${tmpdir()}/gdp-rscase-`); mkdirSync(`${d}/src`); writeFileSync(`${d}/Cargo.toml`, '[package]\nname = "meter"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\npath = "src/lib.rs"\n'); writeFileSync(`${d}/src/lib.rs`, code); return d }
  const src = 'pub struct Meter { used: u32 }\nimpl Meter {\n    pub fn new() -> Self { Meter { used: 0 } }\n    pub fn take(&mut self, n: u32) -> bool { if n > 10 { return false; } self.used = self.used.wrapping_add(n); true }\n}\n'
  const bad = extractRust(crate(src.replace('if n > 10', 'let s: u32 = "x"; if n > 10')), {entry: 'Meter', check: {runs: 6, depth: 4, states: 6}})
  expect(bad.refusals[0]!.what).toMatch(/^the source doesn't compile \(cargo\): error\[E0308\]: mismatched types/)
  const killed = killedBuild(() => extractRust(crate(src), {entry: 'Meter', check: {runs: 6, depth: 4, states: 6}}))
  expect(killed.refusals[0]!.what).toMatch(/^the check's harness failed, twice .*cargo failed twice with nothing to say of the code/)
}, 600_000)

// The reader fuzz's crash (treadmill rust seed 675942: a span cut from src/lib.rs): the reader's own error, the source
// not parsing, was read as a module and threw; refused with it, and any front end's reader that gives no module too.
t('a crate that doesn\'t parse: refused with the reader\'s error, never a crash', () => {
  const d = mkdtempSync(`${tmpdir()}/gdp-rscase-`)
  mkdirSync(`${d}/src`)
  writeFileSync(`${d}/Cargo.toml`, '[package]\nname = "meter"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\npath = "src/lib.rs"\n')
  writeFileSync(`${d}/src/lib.rs`, 'pub struct Meter { used: u32 }\nimpl Meter {\n    pub fn take(&mut self, n: u32) -> bool { if n > 10 { return false; } self.used = \n')
  const x = extractRust(d, {entry: 'Meter'})
  expect(x.ok).toBe(false)
  expect(x.refusals[0]!.what).toMatch(/^the crate doesn't parse: /)
  const y = extractStep({error: 'src/lib.rs: expected an expression'} as never, () => ({cmd: 'false', args: [], hello: {}}), {})
  expect(y.refusals[0]!.what).toMatch(/^the reader read nothing: src\/lib.rs: expected an expression/)
}, 120_000)
