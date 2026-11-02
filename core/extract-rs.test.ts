// The Rust front end (core/extract-rs.ts on core/extract-step.ts): rules read from Rust, each checked against the crate
// it was read from (built by cargo beside a generated harness, overflow checks on). The cases: a u8 that traps past
// its range, a wrapping and a checked one, an Option field, a Result's Err as the failure, a C-like enum and its
// discriminant, an atomic's fetch_add, and the refusals (a loop, a map in the state). Skipped where cargo isn't
// installed (research/langs/rust/rust-setup.sh installs it in a job).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractRust} from './extract-rs.ts'
import {extractStep} from './extract-step.ts'
import {proveRule, proveSteps} from './dsl.ts'

const hasCargo = (() => { try { execFileSync('cargo', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasCargo ? test : test.skip
const DIR = new URL('./rs/examples/limits', import.meta.url).pathname
const budget = {runs: 40, depth: 8, states: 80}
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
