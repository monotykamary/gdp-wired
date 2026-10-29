// The extractor's Rust front end (`extractRust`): a crate's struct and its methods (or its functions) read through
// syn (core/rs/, built once per version of its source with the cargo on the PATH), executed by the shared step
// executor (core/extract-step.ts), printed, built and checked as every front end's rule is. The check builds the crate
// as it ships, in a copy beside a generated harness (a test module inside the struct's own module, so private fields
// are read and set as the crate's own code does), with overflow checks on (a debug build: `+ - *` past the type's
// range panic, the step's failure), drives it with the rule's requests and compares every state.
//
// The subset: a struct (made by its `new`, or by a derived Default) and its methods taking &self or &mut self, or the
// crate's free functions; integers of every width (`+ - *` trap, `wrapping_`/`saturating_`/`checked_` wrap, saturate
// or give an Option, `/` and `%` by a constant truncate, `as` widening, or narrowing where the value fits), bool,
// String, C-like enums (choices, `as` their discriminant), Option (Some, None, `?`, is_some, unwrap, unwrap_or,
// if let, match), Result (Ok, Err, `?`; an Err returned is the step's failure), Instant and Duration as nanoseconds
// (`Instant::now()` the request's time, once a step; duration_since, elapsed, checked_duration_since, as_secs,
// from_millis ...), atomics as the field they are (load, store, fetch_add, compare_exchange: one request is one step,
// the claim is for calls that don't interleave), a Mutex's lock as its value, nested structs by value (a copy where
// the code copies), the crate's struct arguments as records of inputs, closures that don't assign to what they
// capture, panics and assertions (failures). Refused, each where it is with why: loops, generics and traits objects,
// enums with data, references kept, maps and vectors (for now), floats, unsafe pointers, other crates' code.
import {type Extraction} from './extract.ts'
import {Refusal} from './extract-read.ts'
import {type Harness, type Leaf, type PArg, type SModule, type SType, type StepOptions, type StepRead, extractStep, node} from './extract-step.ts'

export type RsOptions = StepOptions & {cargo?: string}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
type FS = {existsSync: (p: string) => boolean, readFileSync: (p: string, e: string) => string, writeFileSync: (p: string, s: string) => void, mkdirSync: (p: string, o?: unknown) => void, cpSync: (a: string, b: string, o: unknown) => void, readdirSync: (p: string, o: unknown) => string[], rmSync: (p: string, o?: unknown) => void, mkdtempSync: (p: string) => string}
const proc = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process

// The reader, built once per version of its source (into the system's temporary directory).
export function rsReader(cargo = 'cargo'): string {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os'), crypto = node<{createHash: (a: string) => {update: (s: string) => {digest: (e: string) => string}}}>('node:crypto')
  const dir = new URL('./rs/', import.meta.url).pathname
  const h = crypto.createHash('sha256').update(fs.readFileSync(`${dir}src/main.rs`, 'utf8') + fs.readFileSync(`${dir}Cargo.toml`, 'utf8')).digest('hex').slice(0, 12)
  const target = `${os.tmpdir()}/gdp-rsreader-${h}`, bin = `${target}/release/gdp-rsreader`
  if (!fs.existsSync(bin)) cp.execFileSync(cargo, ['build', '--release', '--quiet', '--target-dir', target], {cwd: dir, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: {...proc?.env}})
  return bin
}
export function readRust(dir: string, names: string[], cargo?: string): SModule {
  const cp = node<CP>('node:child_process')
  let out: string
  try { out = cp.execFileSync(rsReader(cargo), [JSON.stringify({root: dir, names})], {encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['ignore', 'pipe', 'pipe']}) }
  catch (e) { throw new Refusal(dir, `the Rust reader didn't run (${String((e as {stderr?: string}).stderr ?? (e as Error).message).split('\n').filter(Boolean).slice(-2).join(' | ')}): cargo is needed to extract Rust`) }
  return JSON.parse(out) as SModule
}

export function extractRust(dir: string, opts: RsOptions): Extraction & {read?: StepRead} {
  let mod: SModule
  try {
    if (opts.answers && Object.keys(opts.answers).length) throw new Refusal(dir, 'answers: the Rust check has no stubs yet (a call of other code is refused where it is)')
    if (opts.stores && Object.keys(opts.stores).length) throw new Refusal(dir, 'stores: not in the Rust front end yet')
    mod = readRust(dir, Array.isArray(opts.entry) ? opts.entry : [opts.entry], opts.cargo)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  return extractStep(mod, read => harnessFor(dir, mod, read, opts), opts)
}

// --- the harness --------------------------------------------------------------------------------------------------
// Rust source for one value of a type, from a JSON spec (core/extract-step.ts's checkStep builds the specs).
type Rec = SModule['recs'][string] & {fields: {name: string, t: SType, rs?: string}[], module?: string}
const INTS = new Set(['u8', 'u16', 'u32', 'u64', 'u128', 'usize', 'i8', 'i16', 'i32', 'i64', 'i128', 'isize'])
const bare = (rs: string) => rs.replace(/^&\s*(mut\s*)?/, '').replace(/\s+/g, '')
function rsOf(t: SType, rs: string | undefined, mod: SModule): string {
  if (t.k === 'int') return t.unit === 'instant' ? 'std::time::Instant' : t.unit === 'duration' ? 'std::time::Duration' : (t as {rs?: string}).rs ?? bare(rs ?? 'i64')
  if (t.k === 'bool') return 'bool'
  if (t.k === 'str') return 'String'
  if (t.k === 'choice') return t.enum ?? 'UnknownEnum'
  if (t.k === 'opt') return `Option<${rsOf(t.of, undefined, mod)}>`
  if (t.k === 'rec') return t.name
  return `/* ${t.k} */ ()`
}
// The expression making a value of type t from the JSON value `v` (a &serde_json::Value), with `?` on errors.
function fromJson(t: SType, v: string, mod: SModule, depth = 0): string {
  if (depth > 6) return 'return Err("too deep".into())'
  switch (t.k) {
    case 'int': {
      if (t.unit === 'instant') return `inst(int(val(${v}))?)`
      if (t.unit === 'duration') return `std::time::Duration::from_nanos(u64::try_from(int(val(${v}))?).map_err(|_| "a duration below 0".to_string())?)`
      const ty = (t as {rs?: string}).rs ?? 'i64'
      return `<${ty}>::try_from(int(val(${v}))?).map_err(|_| format!("{} outside ${ty}", val(${v})))?`
    }
    case 'bool': return `val(${v}).as_bool().ok_or("not a bool")?`
    case 'str': return `val(${v}).as_str().ok_or("not a string")?.to_string()`
    case 'choice': return `match val(${v}).as_str().ok_or("not a variant")? { ${t.values.map(x => `${JSON.stringify(x)} => ${t.enum}::${x}`).join(', ')}, x => return Err(format!("no variant {x}")) }`
    case 'opt': return `if ${v}.get("none").and_then(|x| x.as_bool()) == Some(true) || ${v}.is_null() { None } else { Some(${fromJson(t.of, v, mod, depth + 1)}) }`
    case 'rec': {
      const r = mod.recs[t.name] as Rec | undefined
      if (!r) return `return Err("no record ${t.name}".into())`
      return `${t.name} { ${r.fields.map(f => `${f.name}: match ${v}.get("f").and_then(|m| m.get(${JSON.stringify(f.name)})) { Some(x) => ${fromJson(f.t, 'x', mod, depth + 1)}, None => ${zero(f.t, mod, depth + 1)} }`).join(', ')} }`
    }
    default: return `return Err("a value of ${t.k}".into())`
  }
}
// A zero of a type (a field the rule doesn't read: the claim is for any value it holds, and the check gives this one).
function zero(t: SType, mod: SModule, depth = 0): string {
  if (depth > 6) return 'Default::default()'
  if (t.k === 'int') return t.unit === 'instant' ? 'inst(0)' : t.unit === 'duration' ? 'std::time::Duration::ZERO' : '0'
  if (t.k === 'bool') return 'false'
  if (t.k === 'str') return 'String::new()'
  if (t.k === 'opt') return 'None'
  if (t.k === 'choice') return `${t.enum}::${t.values[0]}`
  if (t.k === 'rec') { const r = mod.recs[t.name] as Rec | undefined; return r ? `${t.name} { ${r.fields.map(f => `${f.name}: ${zero(f.t, mod, depth + 1)}`).join(', ')} }` : 'Default::default()' }
  return 'Default::default()'
}
// A leaf's place in the object, read and written as its type says (an atomic by load and store, a Mutex by its lock).
function access(path: string[], t: SType | undefined): {read: string, write: (v: string) => string} {
  const place = `o.${path.join('.')}`
  const lk = (t as {lock?: string} | undefined)?.lock, at = (t as {atomic?: string} | undefined)?.atomic
  if (at) return {read: `${place}.load(std::sync::atomic::Ordering::SeqCst)`, write: v => `${place}.store(${v}, std::sync::atomic::Ordering::SeqCst)`}
  if (lk) { const g = lk === 'std' ? `${place}.lock().unwrap()` : `${place}.lock()`; return {read: `(*${g})`, write: v => `*${g} = ${v}`} }
  return {read: `${place}`, write: v => `${place} = ${v}`}
}
function toJson(t: SType, x: string): string {
  if (t.k === 'int') return t.unit === 'instant' ? `json!(of_inst(${x}).to_string())` : t.unit === 'duration' ? `json!((${x}).as_nanos().to_string())` : `json!(((${x}) as i128).to_string())`
  if (t.k === 'bool') return `json!(${x})`
  if (t.k === 'str') return `json!(${x}.clone())`
  if (t.k === 'choice') return `json!(match ${x} { ${t.values.map(v => `${t.enum}::${v} => ${JSON.stringify(v)}`).join(', ')} })`
  return 'json!(null)'
}
function harnessCode(mod: SModule, read: StepRead, cls: Rec | undefined): string {
  const leaves = read.leaves.filter(l => l.kind !== 'frame' && l.kind !== 'map')
  if (read.leaves.some(l => l.kind === 'map')) throw new Refusal(mod.file, 'a map in the state: the Rust harness reads none yet')
  const byPath = new Map<string, Leaf[]>()
  for (const l of leaves) { const k = l.path.join('.'); byPath.set(k, [...(byPath.get(k) ?? []), l]) }
  const get: string[] = [], set: string[] = []
  for (const [, ls] of byPath) {
    const val = ls.find(l => l.kind !== 'none'), none = ls.find(l => l.kind === 'none')
    if (!val?.t) throw new Refusal(mod.file, `${ls[0]!.path.join('.')}: a leaf of no type the harness reads`)
    const t = val.t.k === 'opt' ? val.t.of : val.t
    const ac = access(val.path, val.t)
    if (none) {
      get.push(`match ${ac.read} { Some(x) => { s.insert(${JSON.stringify(val.name)}.into(), ${toJson(t, 'x')}); s.insert(${JSON.stringify(none.name)}.into(), json!(false)); } None => { s.insert(${JSON.stringify(val.name)}.into(), ${toJson(t, zero(t, mod))}); s.insert(${JSON.stringify(none.name)}.into(), json!(true)); } }`)
      set.push(`{ let v = &st[${JSON.stringify(val.name)}]; let n = st[${JSON.stringify(none.name)}].as_bool() == Some(true); ${ac.write(`if n { None } else { Some(${fromJson(t, 'v', mod)}) }`)}; }`)
    } else {
      get.push(`s.insert(${JSON.stringify(val.name)}.into(), ${toJson(t, ac.read)});`)
      set.push(`{ let v = &st[${JSON.stringify(val.name)}]; ${ac.write(fromJson(t, 'v', mod))}; }`)
    }
  }
  const self = cls?.name ?? '()'
  const fn = (id: string) => mod.funcs[id]!
  const newId = cls?.methods.new ?? undefined
  const make = cls ? (newId ? `{ let a = &req["a"]; let _ = a; ${self}::new(${fn(newId).params.filter(p => !p.self).map((p, i) => fromJson(p.t, `(&a[${i}][1])`, mod)).join(', ')}) }` : `${self}::default()`) : '()'
  const calls = Object.entries(read.args).map(([m]) => {
    const f = cls ? fn(cls.methods[m]!) : fn(m)
    const ps = f.params.filter(p => !p.self)
    const args = ps.map((p, i) => { const rs = (p as {rs?: string}).rs ?? ''; const v = fromJson(p.t, `(&a[${i}][1])`, mod); return /^&\s*mut/.test(rs) ? `&mut ${v}` : rs.startsWith('&') ? `&${v}` : v })
    const target = cls ? `o.${m}(${args.join(', ')})` : `${m}(${args.join(', ')})`
    const ret = f.ret
    const out = ret.k === 'res' ? `match r { Ok(v) => { let _ = &v; Ok(${ret.of.k === 'none' ? 'json!(null)' : tagged(ret.of, 'v')}) } Err(_) => Err("an Err".to_string()) }` : ret.k === 'opt' ? `Ok(match r { Some(v) => ${tagged(ret.of, 'v')}, None => json!(null) })` : ret.k === 'none' ? 'Ok(json!(null))' : `Ok(${tagged(ret, 'r')})`
    return `${JSON.stringify(m)} => { let r = ${target}; ${out} }`
  })
  const clsMod = cls?.module ?? 'crate'
  void clsMod
  return `
#[cfg(test)]
#[allow(unused, clippy::all)]
pub(crate) mod __gdp_harness {
  use super::*;
  use serde_json::{json, Value};
  use std::io::{BufRead, Write};
  static BASE: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
  static NOW: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(0);
  fn base() -> std::time::Instant { *BASE.get_or_init(|| std::time::Instant::now() + std::time::Duration::from_secs(1u64 << 31)) }
  pub(crate) fn now() -> std::time::Instant { inst(NOW.load(std::sync::atomic::Ordering::SeqCst) as i128) }
  fn inst(n: i128) -> std::time::Instant { if n >= 0 { base() + std::time::Duration::from_nanos(n as u64) } else { base() - std::time::Duration::from_nanos((-n) as u64) } }
  fn of_inst(t: std::time::Instant) -> i128 { if t >= base() { t.duration_since(base()).as_nanos() as i128 } else { -(base().duration_since(t).as_nanos() as i128) } }
  fn val(v: &Value) -> &Value { v.get("in").unwrap_or(v) }
  fn int(v: &Value) -> Result<i128, String> { if let Some(s) = v.as_str() { s.parse::<i128>().map_err(|e| e.to_string()) } else if let Some(i) = v.as_i64() { Ok(i as i128) } else if let Some(u) = v.as_u64() { Ok(u as i128) } else { Err(format!("not a number: {v}")) } }
  fn get(o: &${self}) -> Value { let mut s = serde_json::Map::new(); ${get.join(' ')} Value::Object(s) }
  fn set(o: &mut ${self}, st: &Value) -> Result<(), String> { ${set.join(' ')} Ok(()) }
  fn make(req: &Value) -> Result<${self}, String> { NOW.store(int(&req["now"]).unwrap_or(0) as i64, std::sync::atomic::Ordering::SeqCst); Ok(${make}) }
  fn call(o: &mut ${self}, m: &str, a: &Value) -> Result<Result<Value, String>, String> {
    Ok(match m { ${calls.join(', ')}, _ => return Err(format!("no method {m}")) })
  }
  #[test]
  fn __gdp_harness_main() {
    let args: Vec<String> = std::env::args().collect();
    let (fin, fout) = (&args[args.len() - 2], &args[args.len() - 1]);
    std::panic::set_hook(Box::new(|_| {}));
    let input = std::io::BufReader::new(std::fs::File::open(fin).unwrap());
    let mut out = std::fs::OpenOptions::new().write(true).open(fout).unwrap();
    let mut objs: Vec<${self}> = vec![];
    for line in input.lines() {
      let line = line.unwrap();
      let req: Value = serde_json::from_str(&line).unwrap();
      let op = req["op"].as_str().unwrap_or("").to_string();
      let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Value {
        match op.as_str() {
          "hello" => json!({"ok": true}),
          "new" => match make(&req) { Ok(o) => { objs.push(o); json!({"id": objs.len()}) } Err(e) => json!({"err": e}) },
          "at" => match make(&req) { Ok(mut o) => match set(&mut o, &req["state"]) { Ok(()) => { objs.push(o); json!({"id": objs.len()}) } Err(e) => json!({"bad": e}) }, Err(e) => json!({"bad": e}) },
          "get" => { let i = req["id"].as_u64().unwrap() as usize - 1; json!({"state": get(&objs[i])}) }
          "call" => {
            let i = req["id"].as_u64().unwrap() as usize - 1;
            NOW.store(int(&req["now"]).unwrap_or(0) as i64, std::sync::atomic::Ordering::SeqCst);
            let m = req["m"].as_str().unwrap().to_string();
            let a = req["a"].clone();
            let o = &mut objs[i];
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| call(o, &m, &a))) {
              Ok(Ok(Ok(v))) => json!({"out": v}),
              Ok(Ok(Err(e))) => json!({"out": null, "err": e}),
              Ok(Err(bad)) => json!({"out": null, "bad": bad}),
              Err(p) => json!({"out": null, "err": format!("panic: {}", p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default())}),
            }
          }
          "coverage" => json!({"hit": []}),
          _ => json!({"error": format!("no op {op}")}),
        }
      })).unwrap_or_else(|_| json!({"error": "the harness panicked"}));
      writeln!(out, "{}", res).unwrap(); out.flush().unwrap();
    }
  }
}
`
}
const tagged = (t: SType, x: string): string => (t.k === 'int' ? `json!({"n": ${toJsonNum(t, x)}})` : t.k === 'bool' ? `json!(${x})` : t.k === 'str' ? `json!({"s": ${x}})` : t.k === 'choice' ? `json!({"s": ${toJson(t, x).replace(/^json!\(|\)$/g, '')}})` : `json!({"o": "value"})`)
const toJsonNum = (t: SType, x: string) => (t.k === 'int' && t.unit === 'instant' ? `of_inst(${x}).to_string()` : t.k === 'int' && t.unit === 'duration' ? `(${x}).as_nanos().to_string()` : `((${x}) as i128).to_string()`)

// The crate copied (its target left out), the harness put in the struct's module, the clock read through it, the
// tests built with serde_json beside the crate's own dependencies: the test binary is the harness.
function harnessFor(dir: string, mod: SModule, read: StepRead, opts: RsOptions): Harness {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os')
  const cls = read.cls ? mod.recs[read.cls] as Rec : undefined
  try {
    const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-rscheck-`)
    fs.cpSync(dir, work, {recursive: true, filter: (p: string) => !/\/target(\/|$)/.test(p.slice(dir.length))})
    // serde_json for the harness, as a dev-dependency of the copy.
    let toml = fs.readFileSync(`${work}/Cargo.toml`, 'utf8')
    if (!/\[dev-dependencies(\.serde_json)?\][^[]*serde_json/s.test(toml)) toml += '\n[dev-dependencies.serde_json]\nversion = "1"\n'
    fs.writeFileSync(`${work}/Cargo.toml`, toml)
    const file = cls ? String((cls as {file?: string}).file) : String((mod as {fmods?: Record<string, string>}).fmods ? mod.path.slice(mod.root.length + 1) : mod.path.slice(mod.root.length + 1))
    const modPath = cls?.module ?? (mod as {fmods?: Record<string, string>}).fmods?.[Object.keys(read.args)[0]!] ?? 'crate'
    // The clock: Instant::now() read through the harness (the request's time), the code's own calls rewritten first.
    const lib = fs.existsSync(`${work}/src/lib.rs`) ? 'src/lib.rs' : 'src/main.rs'
    const walk = (d: string): string[] => fs.readdirSync(d, {withFileTypes: true} as never).flatMap((e: unknown) => { const x = e as {name: string, isDirectory: () => boolean}; return x.isDirectory() ? walk(`${d}/${x.name}`) : x.name.endsWith('.rs') ? [`${d}/${x.name}`] : [] })
    for (const f of walk(`${work}/src`)) { const s = fs.readFileSync(f, 'utf8'); const t = s.replace(/\b(?:std::time::)?Instant::now\(\)/g, 'crate::__gdp_now()'); if (t !== s) fs.writeFileSync(f, t) }
    fs.writeFileSync(`${work}/${file}`, fs.readFileSync(`${work}/${file}`, 'utf8') + harnessCode(mod, read, cls))
    fs.writeFileSync(`${work}/${lib}`, `${fs.readFileSync(`${work}/${lib}`, 'utf8')}\n#[cfg(test)]\n#[allow(unused)]\npub(crate) fn __gdp_now() -> std::time::Instant { ${modPath}::__gdp_harness::now() }\n`)
    const target = `${os.tmpdir()}/gdp-rscheck-target`
    let msgs: string
    try { msgs = cp.execFileSync(opts.cargo ?? 'cargo', ['test', '--lib', '--no-run', '--message-format=json', '--target-dir', target], {cwd: work, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 28, env: {...proc?.env}}) }
    catch (e) {
      const out = String((e as {stdout?: string}).stdout ?? '')
      const errs = out.split('\n').flatMap(l => { try { const j = JSON.parse(l) as {reason?: string, message?: {level?: string, rendered?: string}}; return j.reason === 'compiler-message' && j.message?.level === 'error' ? [j.message.rendered ?? ''] : [] } catch { return [] } })
      return {cmd: 'false', args: [], hello: {}, error: `the crate doesn't build with the check's harness: ${(errs.join(' | ') || String((e as {stderr?: string}).stderr ?? '')).replace(/\s+/g, ' ').slice(0, 600)}`}
    }
    const exe = msgs.split('\n').flatMap(l => { try { const j = JSON.parse(l) as {reason?: string, executable?: string, target?: {kind?: string[]}}; return j.reason === 'compiler-artifact' && j.executable && j.target?.kind?.includes('lib') ? [j.executable] : [] } catch { return [] } })[0]
    if (!exe) return {cmd: 'false', args: [], hello: {}, error: 'the test build gave no executable'}
    read.model.notes.push('Rust: the code is checked in a debug build (overflow checks on); its branch arms are not counted (no instrumentation yet)')
    read.arms.length = 0
    const test = `${modPath === 'crate' ? '' : `${modPath.replace(/^crate::/, '')}::`}__gdp_harness::__gdp_harness_main`
    return {cmd: exe, args: [test, '--exact', '--nocapture', '--test-threads=1'], hello: {}}
  } catch (e) {
    if (e instanceof Refusal) return {cmd: 'false', args: [], hello: {}, error: e.what}
    throw e
  }
}
