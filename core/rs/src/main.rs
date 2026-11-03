// The extractor's Rust reader (core/extract-rs.ts): a crate read through syn and lowered into the shared step IR
// (core/extract-step.ts's SModule, as JSON on stdout), which the shared executor runs into the rule. Rust is
// expression-oriented, so the lowering is to A-normal form: an `if` or `match` used as a value, a `?`, a `return`
// inside an expression become statements over temporaries. Nothing here decides the subset beyond the syntax: a
// construct the IR has no node for becomes {"e": "no"} / {"s": "no"} with the reason, refused only where a step reaches
// it. Integer semantics are the IR's own operations: `+ - *` trap on overflow (a debug build's panic), the
// `wrapping_`, `saturating_` and `checked_` forms wrap, saturate or give an Option, `/` and `%` truncate.
//
//   gdp-rsreader '{"root": <crate>, "names": [<struct or functions>]}'
use proc_macro2::Span;
use quote::ToTokens;
use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{BinOp, Expr, Fields, ImplItem, Item, Lit, Pat, ReturnType, Stmt, Type, UnOp};

struct File { rel: String, items: Vec<Item>, module: String, no_implicit_prelude: bool, closed_source: bool, inline_end: Option<usize> }
// D3 deliberately rejects crate-wide uncertainty rather than expanding macros,
// interpreting cfg, or implementing import resolution. Inspect before load drops mods.
struct ClosedSource { clean: bool }
impl<'ast> Visit<'ast> for ClosedSource {
  fn visit_attribute(&mut self, a: &'ast syn::Attribute) { if !a.path().is_ident("doc") { self.clean = false; } }
  fn visit_macro(&mut self, _: &'ast syn::Macro) { self.clean = false; }
  fn visit_item(&mut self, i: &'ast Item) {
    if matches!(i, Item::Use(_) | Item::ExternCrate(_) | Item::ForeignMod(_) | Item::Verbatim(_)) { self.clean = false; }
    syn::visit::visit_item(self, i);
  }
}
#[derive(Default)]
struct ClosedBindings { names: BTreeSet<String>, items: bool }
impl<'ast> Visit<'ast> for ClosedBindings {
  fn visit_pat_ident(&mut self, p: &'ast syn::PatIdent) {
    self.names.insert(p.ident.to_string());
    syn::visit::visit_pat_ident(self, p);
  }
  fn visit_item(&mut self, _: &'ast Item) { self.items = true; }
}
#[derive(Default)]
struct UnexpandedModules { found: bool }
impl<'ast> Visit<'ast> for UnexpandedModules {
  fn visit_item_mod(&mut self, m: &'ast syn::ItemMod) {
    if m.content.is_none() { self.found = true; }
    syn::visit::visit_item_mod(self, m);
  }
}
// Native helper hygiene only. Do not guess exports or expand macros in order
// to rename a colliding helper; existing noncollision behavior is unchanged.
// Module helpers occupy the type namespace; root function bridges occupy values.
fn native_helper_name(files: &[File], scope: &File, base: &str, value_namespace: bool) -> Result<String, &'static str> {
  fn identifiers(tokens: proc_macro2::TokenStream, names: &mut BTreeSet<String>) {
    for token in tokens { match token {
      proc_macro2::TokenTree::Ident(i) => { names.insert(i.to_string().trim_start_matches("r#").to_string()); }
      proc_macro2::TokenTree::Group(g) => identifiers(g.stream(), names),
      _ => {}
    } }
  }
  fn named(i: &syn::Ident, name: &str) -> bool { i.to_string().trim_start_matches("r#") == name }
  fn imported(t: &syn::UseTree, name: &str, parent: &str) -> bool {
    match t {
      syn::UseTree::Path(p) => imported(&p.tree, name, &p.ident.to_string()),
      syn::UseTree::Name(n) => named(&n.ident, name) || (n.ident == "self" && parent.trim_start_matches("r#") == name),
      syn::UseTree::Rename(r) => named(&r.rename, name),
      syn::UseTree::Group(g) => g.items.iter().any(|t| imported(t, name, parent)),
      syn::UseTree::Glob(_) => true, // this scope may import the helper name; do not guess
    }
  }
  let canonical = |m: &str| m.split("::").map(|s| s.trim_start_matches("r#")).collect::<Vec<_>>().join("::");
  let child = format!("{}::{base}", canonical(&scope.module));
  let occupied = (!value_namespace && files.iter().any(|f| canonical(&f.module) == child)) || scope.items.iter().any(|i| match i {
    Item::Use(i) => imported(&i.tree, base, ""),
    _ if value_namespace => match i {
      Item::Fn(i) => named(&i.sig.ident, base), Item::Const(i) => named(&i.ident, base),
      Item::Static(i) => named(&i.ident, base),
      Item::Struct(i) => matches!(&i.fields, Fields::Unnamed(_) | Fields::Unit) && named(&i.ident, base),
      Item::ForeignMod(i) => i.items.iter().any(|i| match i {
        syn::ForeignItem::Fn(i) => named(&i.sig.ident, base),
        syn::ForeignItem::Static(i) => named(&i.ident, base), _ => false,
      }),
      _ => false,
    },
    Item::Mod(i) => named(&i.ident, base), Item::Struct(i) => named(&i.ident, base),
    Item::Enum(i) => named(&i.ident, base), Item::Union(i) => named(&i.ident, base),
    Item::Type(i) => named(&i.ident, base), Item::Trait(i) => named(&i.ident, base),
    Item::TraitAlias(i) => named(&i.ident, base),
    Item::ExternCrate(i) => named(i.rename.as_ref().map(|(_, n)| n).unwrap_or(&i.ident), base),
    _ => false,
  });
  // Only bindings in this declaration's namespace and scope trigger repair.
  // A same-spelled field or an unrelated module must not cause a new refusal.
  if !occupied { return Ok(base.into()) }
  let mut names = BTreeSet::new();
  let mut missing = UnexpandedModules::default();
  for f in files {
    // File loading removes resolved mod declarations from parent items.
    for part in f.module.split("::") { names.insert(part.trim_start_matches("r#").to_string()); }
    for item in &f.items { identifiers(item.to_token_stream(), &mut names); missing.visit_item(item); }
  }
  if missing.found || files.iter().any(|f| !f.closed_source) {
    return Err(if value_namespace { "native replay cannot choose a fresh root bridge: namespace is not closed" }
      else { "native replay cannot choose a fresh helper module: namespace is not closed" })
  }
  for n in 1..=names.len() + 1 {
    let candidate = format!("{base}_{n}");
    if !names.contains(&candidate) { return Ok(candidate) }
  }
  Err(if value_namespace { "native replay has no fresh root bridge name" } else { "native replay has no fresh helper module name" })
}
fn unparen(mut e: &Expr) -> &Expr { while let Expr::Paren(p) = e { e = &p.expr; } e }
fn ordinary_function(s: &syn::Signature) -> bool {
  s.asyncness.is_none() && s.unsafety.is_none() && s.constness.is_none() && s.abi.is_none() &&
    s.variadic.is_none() && s.generics.params.is_empty() && s.generics.where_clause.is_none()
}
#[derive(Clone, Default)]
struct Enum { values: Vec<String>, discs: Vec<i64>, data: bool }

struct Reader {
  files: Vec<File>,
  structs: BTreeMap<String, (String, syn::ItemStruct)>, // name -> (file, item)
  smod: BTreeMap<String, String>, // name -> its module path
  enums: BTreeMap<String, Enum>,
  consts: BTreeMap<String, Value>,
  recs: Map<String, Value>,
  funcs: Map<String, Value>,
  methods: BTreeMap<String, Vec<(String, String, syn::ImplItemFn)>>, // type -> (file, module, fn)
  free: BTreeMap<String, (String, syn::ItemFn)>,
  fmod: BTreeMap<String, String>,
  free_counts: BTreeMap<String, usize>, // actual loaded declarations, before map insertion
  // per function
  file: String,
  tmp: usize,
  locals: Vec<BTreeSet<String>>,
  self_ty: Option<String>,
  lifted: Vec<(String, Value)>,
  fid: String,
}

fn text(t: &impl ToTokens) -> String {
  let s = t.to_token_stream().to_string().split_whitespace().collect::<Vec<_>>().join(" ");
  if s.len() <= 60 { s } else { format!("{}...", &s[..s.char_indices().nth(57).map(|x| x.0).unwrap_or(s.len())]) }
}
fn no(p: &str, why: String) -> Value { json!({"e": "no", "p": p, "why": why}) }
fn sno(p: &str, why: String) -> Value { json!({"s": "no", "p": p, "why": why}) }
// Lifetimes constrain borrowing but do not select a runtime value type. Preserve
// refusals for type/const parameters; the existing type and ownership checks still
// decide whether a lifetime-bearing field, argument or operation can be read.
fn has_type_or_const_params(g: &syn::Generics) -> bool {
  g.params.iter().any(|p| !matches!(p, syn::GenericParam::Lifetime(_)))
}
fn last_ident(p: &syn::Path) -> String { p.segments.last().map(|s| s.ident.to_string()).unwrap_or_default() }
fn path_str(p: &syn::Path) -> String { p.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::") }
fn is_place(v: &Value) -> bool { matches!(v["e"].as_str(), Some("var") | Some("get") | Some("idx")) }
const ORDERINGS: [&str; 5] = ["Relaxed", "Release", "Acquire", "AcqRel", "SeqCst"];
fn ordering_variant(name: &str, p: &str) -> Value {
  json!({"e": "variant", "enum": "::std::sync::atomic::Ordering", "v": name, "values": ORDERINGS, "discs": [0, 1, 2, 3, 4], "ord": name, "p": p})
}

impl Reader {
  fn at(&self, s: Span) -> String { let l = s.start(); format!("{}:{}:{}", self.file, l.line, l.column + 1) }

  // --- the crate: its files by `mod` declarations from src/lib.rs (or src/main.rs) ---------------------------------
  fn load(root: &Path) -> Result<Vec<File>, String> {
    let mut out = vec![];
    let lib = if root.join("src/lib.rs").exists() { "src/lib.rs" } else { "src/main.rs" };
    Self::load_file(root, Path::new(lib), "crate", &mut out)?;
    Ok(out)
  }
  fn load_file(root: &Path, rel: &Path, module: &str, out: &mut Vec<File>) -> Result<(), String> {
    let src = std::fs::read_to_string(root.join(rel)).map_err(|e| format!("{}: {e}", rel.display()))?;
    // (syn's parser and the lowering recurse on each level of nesting: past MAX_DEPTH brackets the source is refused, said
    // so as core/extract-read.ts's statedRefusal reads it, before any recursion could pass the reader's stack)
    let deep = src.chars().fold((0i64, 0i64), |(d, m), c| match c { '(' | '[' | '{' => (d + 1, m.max(d + 1)), ')' | ']' | '}' => (d - 1, m), _ => (d, m) }).1;
    if deep > MAX_DEPTH { eprintln!("gdp: refused: {}: the source nests {deep} brackets deep (past {MAX_DEPTH})", rel.display()); std::process::exit(3) }
    let f = syn::parse_file(&src).map_err(|e| format!("{}: {e}", rel.display()))?;
    let dir: PathBuf = if rel.file_name().map(|n| n == "lib.rs" || n == "main.rs" || n == "mod.rs").unwrap_or(false) { rel.parent().unwrap().to_path_buf() } else { rel.with_extension("") };
    let mut audit = ClosedSource { clean: true };
    audit.visit_file(&f);
    let mut closed_source = audit.clean;
    let no_implicit_prelude = f.attrs.iter().any(|a| a.path().is_ident("no_implicit_prelude"));
    let mut items = vec![];
    for it in f.items {
      if let Item::Mod(m) = &it {
        if m.attrs.iter().any(|a| a.path().is_ident("cfg") && text(&a.meta).contains("test")) { continue }
        let name = m.ident.to_string();
        let sub = format!("{module}::{name}");
        match &m.content {
          Some((brace, inner)) => { out.push(File { rel: rel.display().to_string(), items: inner.clone(), module: sub, inline_end: Some(brace.span.close().byte_range().start), closed_source, no_implicit_prelude: no_implicit_prelude || m.attrs.iter().any(|a| a.path().is_ident("no_implicit_prelude")) }); }
          None => {
            let a = dir.join(format!("{name}.rs"));
            let b = dir.join(&name).join("mod.rs");
            let r = if root.join(&a).exists() { a } else if root.join(&b).exists() { b } else { closed_source = false; continue };
            Self::load_file(root, &r, &sub, out)?;
          }
        }
        continue
      }
      items.push(it);
    }
    out.push(File { rel: rel.display().to_string(), items, module: module.to_string(), no_implicit_prelude, closed_source, inline_end: None });
    Ok(())
  }
  fn index(&mut self) {
    for f in &self.files {
      for it in &f.items {
        match it {
          Item::Struct(s) => { self.structs.insert(s.ident.to_string(), (f.rel.clone(), s.clone())); self.smod.insert(s.ident.to_string(), f.module.clone()); }
          Item::Enum(e) => {
            let mut en = Enum::default();
            let mut next = 0i64;
            for v in &e.variants {
              if !matches!(v.fields, Fields::Unit) { en.data = true }
              if let Some((_, Expr::Lit(l))) = &v.discriminant { if let Lit::Int(i) = &l.lit { next = i.base10_parse().unwrap_or(next) } }
              en.values.push(v.ident.to_string()); en.discs.push(next); next += 1;
            }
            self.enums.insert(e.ident.to_string(), en);
          }
          Item::Impl(im) => {
            if let Type::Path(tp) = &*im.self_ty {
              let ty = last_ident(&tp.path);
              for ii in &im.items { if let ImplItem::Fn(m) = ii { self.methods.entry(ty.clone()).or_default().push((f.rel.clone(), f.module.clone(), m.clone())); } }
            }
          }
          Item::Fn(fun) => { *self.free_counts.entry(fun.sig.ident.to_string()).or_default() += 1; self.free.insert(fun.sig.ident.to_string(), (f.rel.clone(), fun.clone())); self.fmod.insert(fun.sig.ident.to_string(), f.module.clone()); }
          Item::Const(c) => { if let Expr::Lit(l) = &*c.expr { if let Some(v) = self.lit(&l.lit, "") { self.consts.insert(c.ident.to_string(), v); } } }
          _ => {}
        }
      }
    }
  }

  // A narrow standard-library resolution check, not general use/alias expansion.
  // Unknown wildcard bindings and visible competing declarations fail closed.
  fn standard_atomic(&self, path: &syn::Path, wanted: &str) -> bool {
    if path.segments.iter().any(|s| !matches!(s.arguments, syn::PathArguments::None)) { return false }
    fn bindings(t: &syn::UseTree, prefix: &[String], wanted: &str, out: &mut Vec<Vec<String>>) {
      match t {
        syn::UseTree::Path(p) => { let mut next = prefix.to_vec(); next.push(p.ident.to_string()); bindings(&p.tree, &next, wanted, out); }
        syn::UseTree::Name(n) => {
          let name = n.ident.to_string();
          let mut full = prefix.to_vec();
          if name != "self" { full.push(name); }
          if full.last().map(|n| n == wanted).unwrap_or(false) { out.push(full); }
        }
        syn::UseTree::Rename(r) if r.rename == wanted => { let mut full = prefix.to_vec(); if r.ident != "self" { full.push(r.ident.to_string()); } out.push(full); }
        syn::UseTree::Group(g) => for t in &g.items { bindings(t, prefix, wanted, out); },
        syn::UseTree::Glob(_) => out.push(vec![]),
        _ => {}
      }
    }
    let imports = |name: &str| {
      let mut out = vec![];
      for f in self.files.iter().filter(|f| f.rel == self.file) { for it in &f.items { if let Item::Use(u) = it { bindings(&u.tree, &[], name, &mut out); } } }
      out
    };
    let declared = |name: &str| self.structs.contains_key(name) || self.enums.contains_key(name) || self.files.iter().any(|f| f.module.split("::").any(|n| n == name)) ||
      self.files.iter().filter(|f| f.rel == self.file).any(|f| f.items.iter().any(|it| match it {
        Item::Type(t) => t.ident == name, Item::Union(u) => u.ident == name,
        Item::Trait(t) => t.ident == name, Item::TraitAlias(t) => t.ident == name,
        Item::Mod(m) => m.ident == name,
        Item::ExternCrate(e) => e.rename.as_ref().map(|(_, n)| n == name).unwrap_or(e.ident == name && name != "std" && name != "core"),
        _ => false,
      }));
    let standard = |s: &[String]| s.len() == 4 && (s[0] == "std" || s[0] == "core") && s[1] == "sync" && s[2] == "atomic" && s[3] == wanted;
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    if standard(&segs) { return !declared(&segs[0]) && imports(&segs[0]).is_empty() }
    if segs.len() != 1 || segs[0] != wanted || declared(wanted) { return false }
    let found = imports(wanted);
    !found.is_empty() && found.iter().all(|s| standard(s) && !declared(&s[0]) && imports(&s[0]).is_empty())
  }
  fn atomic_field(&self, receiver: &Expr) -> bool {
    let Expr::Field(f) = receiver else { return false };
    if !matches!(&*f.base, Expr::Path(p) if p.qself.is_none() && p.path.is_ident("self")) { return false }
    let syn::Member::Named(name) = &f.member else { return false };
    let Some((_, rec)) = self.self_ty.as_ref().and_then(|n| self.structs.get(n)) else { return false };
    let Some(field) = rec.fields.iter().find(|fd| fd.ident.as_ref() == Some(name)) else { return false };
    let Type::Path(t) = &field.ty else { return false };
    let name = last_ident(&t.path);
    t.qself.is_none() && ["AtomicU8", "AtomicU16", "AtomicU32", "AtomicU64", "AtomicUsize", "AtomicI32", "AtomicI64", "AtomicIsize", "AtomicBool"].contains(&name.as_str()) && self.standard_atomic(&t.path, &name)
  }

  // --- types -------------------------------------------------------------------------------------------------------
  fn ty(&self, t: &Type) -> Value {
    match t {
      Type::Reference(r) => {
        if let Type::Path(p) = &*r.elem { if p.path.is_ident("str") { return json!({"k": "str"}) } }
        self.ty(&r.elem)
      }
      Type::Paren(p) => self.ty(&p.elem),
      Type::Tuple(t) if t.elems.is_empty() => json!({"k": "none"}),
      Type::Path(p) => {
        if p.qself.is_none() && self.standard_atomic(&p.path, "Ordering") { return json!({"k": "choice", "values": ORDERINGS, "discs": [0, 1, 2, 3, 4], "enum": "::std::sync::atomic::Ordering"}) }
        let seg = match p.path.segments.last() { Some(s) => s, None => return json!({"k": "opaque", "why": text(t)}) };
        let name = seg.ident.to_string();
        let args: Vec<Type> = match &seg.arguments { syn::PathArguments::AngleBracketed(a) => a.args.iter().filter_map(|x| if let syn::GenericArgument::Type(t) = x { Some(t.clone()) } else { None }).collect(), _ => vec![] };
        let int = |bits: u32, signed: bool| json!({"k": "int", "bits": bits, "signed": signed, "rs": name});
        match name.as_str() {
          "u8" => int(8, false), "u16" => int(16, false), "u32" => int(32, false), "u64" | "usize" => int(64, false), "u128" => int(128, false),
          "i8" => int(8, true), "i16" => int(16, true), "i32" => int(32, true), "i64" | "isize" => int(64, true), "i128" => int(128, true),
          "bool" => json!({"k": "bool"}), "String" | "str" => json!({"k": "str"}),
          "f32" | "f64" => json!({"k": "opaque", "why": format!("{name}, a float (a binary fraction that rounds; the subset reads integers)")}),
          "Instant" => json!({"k": "int", "bits": 0, "signed": true, "unit": "instant"}),
          "Duration" => json!({"k": "int", "bits": 0, "signed": false, "unit": "duration"}),
          "AtomicU8" => json!({"k": "int", "bits": 8, "signed": false, "atomic": name, "rs": "u8"}), "AtomicU16" => json!({"k": "int", "bits": 16, "signed": false, "atomic": name, "rs": "u16"}),
          "AtomicU32" => json!({"k": "int", "bits": 32, "signed": false, "atomic": name, "rs": "u32"}), "AtomicU64" => json!({"k": "int", "bits": 64, "signed": false, "atomic": name, "rs": "u64"}), "AtomicUsize" => json!({"k": "int", "bits": 64, "signed": false, "atomic": name, "rs": "usize"}),
          "AtomicI32" => json!({"k": "int", "bits": 32, "signed": true, "atomic": name, "rs": "i32"}), "AtomicI64" => json!({"k": "int", "bits": 64, "signed": true, "atomic": name, "rs": "i64"}), "AtomicIsize" => json!({"k": "int", "bits": 64, "signed": true, "atomic": name, "rs": "isize"}),
          "AtomicBool" => json!({"k": "bool", "atomic": name}),
          "Option" if args.len() == 1 => json!({"k": "opt", "of": self.ty(&args[0])}),
          "Result" if !args.is_empty() => json!({"k": "res", "of": self.ty(&args[0])}),
          "HashMap" | "BTreeMap" if args.len() == 2 => json!({"k": "map", "key": self.ty(&args[0]), "val": self.ty(&args[1]), "rs": name}),
          "Vec" if args.len() == 1 => json!({"k": "list", "of": self.ty(&args[0])}),
          "Mutex" | "RwLock" if args.len() == 1 => { let mut v = self.ty(&args[0]); let std = p.path.segments.iter().any(|s| s.ident == "std") || self.std_lock(); v["lock"] = json!(if std { "std" } else { "parking_lot" }); v["lockty"] = json!(name); v }
          "Self" => match &self.self_ty { Some(s) => self.named(s, t), None => json!({"k": "opaque", "why": "Self outside an impl"}) },
          _ => self.named(&name, t),
        }
      }
      _ => json!({"k": "opaque", "why": text(t)}),
    }
  }
  // Whether the crate's Mutex is std's (its lock() a Result) rather than parking_lot's.
  fn std_lock(&self) -> bool { !self.files.iter().any(|f| f.items.iter().any(|i| matches!(i, Item::Use(u) if text(u).contains("parking_lot")))) }
  fn record_collision(&self, name: &str) -> bool {
    self.files.iter().flat_map(|f| f.items.iter()).filter(|it| matches!(it, Item::Struct(s) if s.ident == name)).take(2).count() > 1
  }
  fn named(&self, name: &str, t: &Type) -> Value {
    if self.record_collision(name) { return json!({"k": "opaque", "why": format!("{name}: multiple source record declarations; module-qualified identity is outside the reader")}) }
    if let Some(e) = self.enums.get(name) {
      if e.data { return json!({"k": "opaque", "why": format!("{name}, an enum with data (a variant record)")}) }
      return json!({"k": "choice", "values": e.values, "discs": e.discs, "enum": name})
    }
    if self.structs.contains_key(name) { return json!({"k": "rec", "name": name}) }
    json!({"k": "opaque", "why": format!("{}, a type outside the crate's own", text(t))})
  }
  fn rec(&mut self, name: &str) {
    if self.recs.contains_key(name) { return }
    let (file, s) = match self.structs.get(name) { Some(x) => x.clone(), None => return };
    self.recs.insert(name.to_string(), Value::Null);
    let saved = self.self_ty.replace(name.to_string());
    let mut fields = vec![];
    if let Fields::Named(f) = &s.fields { for fd in &f.named { fields.push(json!({"name": fd.ident.as_ref().unwrap().to_string(), "t": self.ty(&fd.ty), "rs": text(&fd.ty)})) } }
    let derives: Vec<String> = s.attrs.iter().filter(|a| a.path().is_ident("derive")).flat_map(|a| text(&a.meta).replace("derive (", "").replace(')', "").split(',').map(|x| x.trim().to_string()).collect::<Vec<_>>()).collect();
    let generic = has_type_or_const_params(&s.generics);
    let mut kinds = vec![json!("value")];
    if derives.iter().any(|d| d == "Default") { kinds.push(json!("default")) }
    if generic { kinds.push(json!(format!("generic:{}", text(&s.generics)))) }
    // Its methods (each lowered once, inherent and trait impls alike).
    let mut methods = Map::new();
    for (mfile, _module, m) in self.methods.get(name).cloned().unwrap_or_default() {
      let fid = format!("{name}::{}", m.sig.ident);
      methods.insert(m.sig.ident.to_string(), json!(fid.clone()));
      let f = self.func(&mfile, &m.sig, &m.block, &m.attrs, Some(name), &fid);
      self.funcs.insert(fid, f);
    }
    self.self_ty = saved;
    self.recs.insert(name.to_string(), json!({"name": name, "short": name, "fields": fields, "methods": methods, "kinds": kinds, "own": true, "module": self.smod.get(name).cloned().unwrap_or_default(), "file": file, "p": format!("{}:{}:1", file, s.ident.span().start().line), "derives": derives}));
  }

  // --- functions ---------------------------------------------------------------------------------------------------
  fn func(&mut self, file: &str, sig: &syn::Signature, block: &syn::Block, attrs: &[syn::Attribute], cls: Option<&str>, fid: &str) -> Value {
    let saved = (std::mem::replace(&mut self.file, file.to_string()), self.tmp, std::mem::take(&mut self.locals), std::mem::replace(&mut self.fid, fid.to_string()));
    self.tmp = 0;
    let mut params = vec![];
    let mut names = BTreeSet::new();
    let mut is_static = true;
    let mut recv = Value::Null;
    for a in &sig.inputs {
      match a {
        syn::FnArg::Receiver(r) => { is_static = false; names.insert("self".to_string()); recv = json!(if r.reference.is_none() { "value" } else if r.mutability.is_some() { "mut" } else { "ref" }); params.push(json!({"name": "self", "t": {"k": "any"}, "self": true})) }
        syn::FnArg::Typed(pt) => {
          let n = match &*pt.pat { Pat::Ident(i) => i.ident.to_string(), _ => format!("_arg{}", params.len()) };
          names.insert(n.clone());
          params.push(json!({"name": n, "t": self.ty(&pt.ty), "rs": text(&pt.ty)}));
        }
      }
    }
    self.locals.push(names);
    for s in &block.stmts { if let Stmt::Local(l) = s { self.bind_pat(&l.pat) } }
    // The current callable table is keyed by short owner/method names. Do not
    // let its last inserted declaration choose a module or trait implementation.
    let collision = cls.and_then(|owner| {
      if self.record_collision(owner) { Some(format!("{owner}: multiple source record declarations; module-qualified identity is outside the reader")) }
      else if self.methods.get(owner).map(|ms| ms.iter().filter(|(_, _, m)| m.sig.ident == sig.ident).take(2).count()).unwrap_or(0) > 1 {
        Some(format!("{owner}::{}: multiple source method candidates; implementation resolution is outside the reader", sig.ident))
      } else { None }
    });
    let (mut body, tail) = if let Some(why) = collision { (vec![sno(&self.at(sig.ident.span()), why)], Value::Null) } else { self.block(block) };
    if !tail.is_null() && tail["e"] != "none" { body.push(json!({"s": "ret", "p": self.at(block.span()), "x": tail})) }
    let ret = match &sig.output { ReturnType::Default => json!({"k": "none"}), ReturnType::Type(_, t) => self.ty(t) };
    let generic = has_type_or_const_params(&sig.generics);
    let decs: Vec<Value> = attrs.iter().filter(|a| !a.path().is_ident("doc") && !a.path().is_ident("inline") && !a.path().is_ident("must_use") && !a.path().is_ident("allow")).map(|a| json!({"name": format!("attr:{}", text(a.path())), "text": text(&a.meta), "p": self.at(a.span())})).collect();
    let out = json!({"id": fid, "name": sig.ident.to_string(), "cls": cls, "p": self.at(sig.ident.span()), "span": [file, sig.span().start().line, block.span().end().line],
      "params": params, "ret": ret, "body": body, "async": sig.asyncness.is_some(), "static": is_static, "recv": recv, "decorators": decs, "generic": generic});
    self.file = saved.0; self.tmp = saved.1; self.locals = saved.2; self.fid = saved.3;
    out
  }
  fn bind_pat(&mut self, p: &Pat) {
    match p {
      Pat::Ident(i) => { if let Some(l) = self.locals.last_mut() { l.insert(i.ident.to_string()); } }
      Pat::Type(t) => self.bind_pat(&t.pat),
      Pat::Tuple(t) => for x in &t.elems { self.bind_pat(x) },
      _ => {}
    }
  }
  fn is_local(&self, n: &str) -> bool { self.locals.iter().any(|l| l.contains(n)) }
  fn temp(&mut self) -> String { self.tmp += 1; let n = format!("$t{}", self.tmp); if let Some(l) = self.locals.last_mut() { l.insert(n.clone()); } n }

  // --- statements: each lowered with what its expressions need before them ----------------------------------------
  fn block(&mut self, b: &syn::Block) -> (Vec<Value>, Value) {
    let mut out = vec![];
    let n = b.stmts.len();
    for (i, s) in b.stmts.iter().enumerate() {
      let last = i + 1 == n;
      match s {
        Stmt::Local(l) => {
          self.bind_pat(&l.pat);
          let p = self.at(l.span());
          let init = match &l.init { Some(i) => i, None => continue };
          if init.diverge.is_some() { out.push(sno(&p, "let ... else".into())); continue }
          let (mut pre, v) = self.expr(&init.expr);
          out.append(&mut pre);
          let v = if is_place(&v) { json!({"e": "copy", "x": v, "p": p}) } else { v };
          let to = self.target_pat(&l.pat, &p);
          out.push(json!({"s": "set", "p": p, "to": to, "x": v}));
        }
        Stmt::Expr(e, semi) => {
          let (mut pre, v) = self.expr(e);
          out.append(&mut pre);
          if last && semi.is_none() { return (out, v) }
          if v["e"] != "none" && v["e"] != "unit" { out.push(json!({"s": "expr", "p": self.at(e.span()), "x": v})) }
        }
        Stmt::Macro(m) => { let (mut pre, v) = self.mac(&m.mac, m.span()); out.append(&mut pre); if !v.is_null() && v["e"] != "unit" { out.push(json!({"s": "expr", "p": self.at(m.span()), "x": v})) } }
        Stmt::Item(it) => out.push(sno(&self.at(it.span()), "an item declared in a function".into())),
      }
    }
    (out, json!({"e": "unit", "p": self.at(b.span())}))
  }
  fn target_pat(&self, p: &Pat, at: &str) -> Value {
    match p {
      Pat::Ident(i) => json!({"e": "var", "n": i.ident.to_string(), "p": at}),
      Pat::Type(t) => self.target_pat(&t.pat, at),
      Pat::Tuple(t) => json!({"e": "tuple", "xs": t.elems.iter().map(|x| self.target_pat(x, at)).collect::<Vec<_>>(), "p": at}),
      Pat::Wild(_) => json!({"e": "var", "n": "_", "p": at}),
      _ => no(at, format!("{}: a pattern outside the subset", text(p))),
    }
  }

  // --- expressions: (statements before, the value) ----------------------------------------------------------------
  fn expr(&mut self, e: &Expr) -> (Vec<Value>, Value) {
    let p = self.at(e.span());
    let t = text(e);
    match e {
      Expr::Paren(x) => self.expr(&x.expr),
      Expr::Group(x) => self.expr(&x.expr),
      Expr::Lit(l) => (vec![], self.lit(&l.lit, &p).unwrap_or_else(|| no(&p, format!("{t}: a literal outside the subset")))),
      Expr::Path(x) => (vec![], self.path_expr(&x.path, &p, &t)),
      Expr::Reference(r) => { let (pre, v) = self.expr(&r.expr); (pre, json!({"e": "ref", "x": v, "p": p})) }
      Expr::Unary(u) => {
        let (pre, v) = self.expr(&u.expr);
        (pre, match u.op { UnOp::Neg(_) => json!({"e": "neg", "x": v, "p": p}), UnOp::Not(_) => json!({"e": "not", "x": v, "p": p, "strict": true}), UnOp::Deref(_) => v, _ => no(&p, format!("{t}: an operator outside the subset")) })
      }
      Expr::Binary(b) => self.binary(b, &p, &t),
      Expr::Assign(a) => {
        let (mut pre, v) = self.expr(&a.right);
        let (mut tp, to) = self.expr(&a.left);
        pre.append(&mut tp);
        let v = if is_place(&v) { json!({"e": "copy", "x": v, "p": p}) } else { v };
        pre.push(json!({"s": "set", "p": p, "to": to, "x": v}));
        (pre, json!({"e": "unit", "p": p}))
      }
      Expr::Field(f) => {
        let (pre, v) = self.expr(&f.base);
        match &f.member { syn::Member::Named(n) => (pre, json!({"e": "get", "x": v, "f": n.to_string(), "p": p, "text": t})), _ => (pre, no(&p, format!("{t}: a tuple's field"))) }
      }
      Expr::Index(i) => { let (mut pre, v) = self.expr(&i.expr); let (mut ip, k) = self.expr(&i.index); pre.append(&mut ip); (pre, json!({"e": "idx", "x": v, "i": k, "p": p, "text": t})) }
      Expr::Cast(c) => { let (pre, v) = self.expr(&c.expr); (pre, json!({"e": "cast", "x": v, "ty": self.ty(&c.ty), "p": p, "text": t})) }
      Expr::Tuple(tu) => {
        if tu.elems.is_empty() { return (vec![], json!({"e": "unit", "p": p})) }
        let mut pre = vec![]; let mut xs = vec![];
        for x in &tu.elems { let (mut a, v) = self.expr(x); pre.append(&mut a); xs.push(v) }
        (pre, json!({"e": "tuple", "xs": xs, "p": p}))
      }
      Expr::Block(b) => self.block(&b.block),
      Expr::Unsafe(b) => self.block(&b.block),
      Expr::Return(r) => {
        let (mut pre, v) = match &r.expr { Some(x) => self.expr(x), None => (vec![], json!({"e": "unit", "p": p})) };
        let v = if is_place(&v) { json!({"e": "copy", "x": v, "p": p}) } else { v };
        pre.push(json!({"s": "ret", "p": p, "x": v}));
        (pre, json!({"e": "unit", "p": p}))
      }
      Expr::Try(x) => {
        // `e?`: where e is an Err (or None), the function returns it; else its value.
        let (mut pre, v) = self.expr(&x.expr);
        let q = self.temp();
        pre.push(json!({"s": "set", "p": p, "to": {"e": "var", "n": q, "p": p}, "x": v}));
        pre.push(json!({"s": "if", "p": p, "c": {"e": "is", "x": {"e": "var", "n": q, "p": p}, "k": "bad", "p": p}, "then": [{"s": "ret", "p": p, "x": {"e": "bad", "x": {"e": "var", "n": q, "p": p}, "p": p}}], "else": []}));
        (pre, json!({"e": "unwrap", "x": {"e": "var", "n": q, "p": p}, "k": "good", "p": p}))
      }
      Expr::If(i) => self.if_expr(i, &p),
      Expr::Match(m) => self.match_expr(m, &p),
      // (a call's end too: a check stubs an answered one by rewriting it from its position to its end)
      Expr::Call(c) => { let (s, mut v) = self.call(c, &p, &t); if v["e"] == "call" { let l = c.span().end(); v["end"] = json!(format!("{}:{}", l.line, l.column + 1)); } (s, v) }
      Expr::MethodCall(m) => { let (s, mut v) = self.method(m, &p, &t); if v["e"] == "call" { let l = m.span().end(); v["end"] = json!(format!("{}:{}", l.line, l.column + 1)); } (s, v) }
      Expr::Struct(s) => {
        // An enum's variant with fields (an error's payload, say): a value the subset keeps only where nothing reads it.
        if s.path.segments.len() >= 2 && self.enums.contains_key(&s.path.segments[s.path.segments.len() - 2].ident.to_string()) {
          let mut pre = vec![];
          for f in &s.fields { let (mut a, _) = self.expr(&f.expr); pre.append(&mut a); }
          return (pre, json!({"e": "opaque", "why": format!("{t}: an enum variant with data"), "p": p}))
        }
        let name = last_ident(&s.path);
        let name = if name == "Self" { self.self_ty.clone().unwrap_or(name) } else { name };
        if self.record_collision(&name) { return (vec![], no(&p, format!("{name}: multiple source record declarations; module-qualified identity is outside the reader"))) }
        if s.rest.is_some() { return (vec![], no(&p, format!("{t}: a struct update (..rest)"))) }
        let mut pre = vec![]; let mut fields = vec![];
        for f in &s.fields {
          let n = match &f.member { syn::Member::Named(n) => n.to_string(), _ => return (vec![], no(&p, format!("{t}: a tuple struct"))) };
          let (mut a, v) = self.expr(&f.expr); pre.append(&mut a);
          let v = if is_place(&v) { json!({"e": "copy", "x": v, "p": p}) } else { v };
          fields.push(json!([n, v]));
        }
        self.rec(&name);
        (pre, json!({"e": "new", "rec": name, "fields": fields, "p": p, "text": t}))
      }
      Expr::Closure(c) => self.closure(c, &p),
      Expr::Macro(m) => { let (pre, v) = self.mac(&m.mac, m.span()); (pre, if v.is_null() { json!({"e": "unit", "p": p}) } else { v }) }
      Expr::Let(_) => (vec![], no(&p, format!("{t}: a let outside an if"))),
      Expr::Loop(_) | Expr::While(_) | Expr::ForLoop(_) => (vec![sno(&p, "a loop".into())], json!({"e": "unit", "p": p})),
      Expr::Await(_) | Expr::Async(_) => (vec![], no(&p, format!("{t}: async"))),
      _ => (vec![], no(&p, format!("{t}: an expression outside the subset"))),
    }
  }
  fn lit(&self, l: &Lit, p: &str) -> Option<Value> {
    match l {
      Lit::Int(i) => {
        let v: i128 = i.base10_parse().ok()?;
        let suffix = i.suffix();
        let mut o = json!({"e": "int", "v": v.to_string(), "p": p});
        if !suffix.is_empty() { o["ty"] = self.ty(&syn::parse_str::<Type>(suffix).ok()?); }
        Some(o)
      }
      Lit::Bool(b) => Some(json!({"e": "bool", "v": b.value, "p": p})),
      Lit::Str(s) => Some(json!({"e": "str", "v": s.value(), "p": p})),
      _ => None,
    }
  }
  fn path_expr(&mut self, path: &syn::Path, p: &str, t: &str) -> Value {
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    if let Some(last) = segs.last() {
      if ORDERINGS.contains(&last.as_str()) && segs.len() > 1 {
        let mut ty = path.clone(); ty.segments.pop(); ty.segments.pop_punct();
        if self.standard_atomic(&ty, "Ordering") { return ordering_variant(last, p) }
      }
    }
    if segs.len() == 1 {
      let n = &segs[0];
      if self.is_local(n) { return json!({"e": "var", "n": n, "p": p}) }
      if n == "None" { return json!({"e": "none", "p": p}) }
      if let Some(c) = self.consts.get(n) { let mut c = c.clone(); c["p"] = json!(p); return c }
      if self.free.contains_key(n) { return json!({"e": "fn", "id": n, "p": p}) }
      return json!({"e": "ext", "q": n, "text": t, "p": p})
    }
    let ty = if segs[0] == "Self" { self.self_ty.clone().unwrap_or_default() } else { segs[segs.len() - 2].clone() };
    let last = segs.last().unwrap();
    if let Some(e) = self.enums.get(&ty) {
      if e.values.contains(last) { return json!({"e": "variant", "enum": ty, "v": last, "values": e.values, "discs": e.discs, "p": p}) }
    }
    if let Some(c) = self.consts.get(last) { if segs.len() == 2 && (segs[0] == "Self" || self.structs.contains_key(&segs[0])) { let mut c = c.clone(); c["p"] = json!(p); return c } }
    if (ty == "Duration" && last == "ZERO") || (segs.len() >= 2 && segs[segs.len() - 2] == "Ordering") { return json!({"e": "int", "v": "0", "p": p, "ord": last}) }
    if self.structs.contains_key(&ty) { self.rec(&ty); return json!({"e": "fn", "id": format!("{ty}::{last}"), "p": p}) }
    // A method of an enum (an `impl From<u8> for State`, say): lowered as a function of its type.
    if self.enums.contains_key(&ty) && self.methods.get(&ty).map(|ms| ms.iter().any(|m| m.2.sig.ident == last)).unwrap_or(false) {
      let fid = format!("{ty}::{last}");
      if !self.funcs.contains_key(&fid) {
        self.funcs.insert(fid.clone(), Value::Null);
        let (mfile, _, m) = self.methods[&ty].iter().find(|m| m.2.sig.ident == last).cloned().unwrap();
        let saved = self.self_ty.replace(ty.clone());
        let f = self.func(&mfile, &m.sig, &m.block, &m.attrs, None, &fid);
        self.self_ty = saved;
        self.funcs.insert(fid.clone(), f);
      }
      return json!({"e": "fn", "id": fid, "p": p})
    }
    json!({"e": "ext", "q": segs.join("::"), "text": t, "p": p})
  }
  fn binary(&mut self, b: &syn::ExprBinary, p: &str, t: &str) -> (Vec<Value>, Value) {
    let compound = |op: &BinOp| -> Option<&'static str> { Some(match op { BinOp::AddAssign(_) => "+", BinOp::SubAssign(_) => "-", BinOp::MulAssign(_) => "*", BinOp::DivAssign(_) => "/", BinOp::RemAssign(_) => "%", _ => return None }) };
    if let Some(op) = compound(&b.op) {
      let (mut pre, v) = self.expr(&b.right);
      let (mut tp, to) = self.expr(&b.left);
      pre.append(&mut tp);
      let x = json!({"e": "bin", "op": op, "x": to.clone(), "y": v, "p": p, "text": t, "ovf": "trap", "div": "trunc"});
      pre.push(json!({"s": "set", "p": p, "to": to, "x": x}));
      return (pre, json!({"e": "unit", "p": p}))
    }
    let (mut pre, l) = self.expr(&b.left);
    let (rpre, r) = self.expr(&b.right);
    let logical = match b.op { BinOp::And(_) => Some("and"), BinOp::Or(_) => Some("or"), _ => None };
    if let Some(lg) = logical {
      if rpre.is_empty() { return (pre, json!({"e": lg, "xs": [l, r], "p": p, "strict": true})) }
      // The right side has statements: an if over a temporary, as the short circuit runs it.
      let tmp = self.temp();
      let var = json!({"e": "var", "n": tmp, "p": p});
      let mut then = rpre; then.push(json!({"s": "set", "p": p, "to": var, "x": r}));
      let short = json!({"s": "set", "p": p, "to": var, "x": {"e": "bool", "v": lg == "or", "p": p}});
      let (a, bb) = if lg == "and" { (then, vec![short]) } else { (vec![short], then) };
      pre.push(json!({"s": "if", "p": p, "c": l, "then": a, "else": bb}));
      return (pre, var)
    }
    let mut rpre = rpre; pre.append(&mut rpre);
    let arith = match b.op { BinOp::Add(_) => Some("+"), BinOp::Sub(_) => Some("-"), BinOp::Mul(_) => Some("*"), BinOp::Div(_) => Some("/"), BinOp::Rem(_) => Some("%"), _ => None };
    if let Some(op) = arith { return (pre, json!({"e": "bin", "op": op, "x": l, "y": r, "p": p, "text": t, "ovf": "trap", "div": "trunc"})) }
    let cmp = match b.op { BinOp::Lt(_) => "<", BinOp::Le(_) => "<=", BinOp::Gt(_) => ">", BinOp::Ge(_) => ">=", BinOp::Eq(_) => "==", BinOp::Ne(_) => "!=", _ => return (pre, no(p, format!("{t}: a bit operation"))) };
    (pre, json!({"e": "cmp", "op": cmp, "x": l, "y": r, "p": p, "text": t}))
  }
  // An if used as a statement or a value: its branches' statements, each ending by setting a temporary.
  fn if_expr(&mut self, i: &syn::ExprIf, p: &str) -> (Vec<Value>, Value) {
    let tmp = self.temp();
    let var = json!({"e": "var", "n": tmp, "p": p});
    let (mut pre, cond, binds) = self.cond(&i.cond, p);
    let (mut then, tv) = { self.locals.push(BTreeSet::new()); let r = self.block(&i.then_branch); self.locals.pop(); r };
    let mut tb = binds; tb.append(&mut then);
    tb.push(json!({"s": "set", "p": p, "to": var, "x": tv}));
    let mut eb = vec![];
    if let Some((_, e)) = &i.else_branch { let (mut s, v) = self.expr(e); eb.append(&mut s); eb.push(json!({"s": "set", "p": p, "to": var, "x": v})) }
    else { eb.push(json!({"s": "set", "p": p, "to": var, "x": {"e": "unit", "p": p}})) }
    pre.push(json!({"s": "if", "p": p, "c": cond, "then": tb, "else": eb}));
    (pre, var)
  }
  // A condition: a boolean, or `let PAT = e` (its test, and the bindings it makes where it holds).
  fn cond(&mut self, c: &Expr, p: &str) -> (Vec<Value>, Value, Vec<Value>) {
    if let Expr::Let(l) = c {
      let (mut pre, v) = self.expr(&l.expr);
      let tmp = self.temp();
      pre.push(json!({"s": "set", "p": p, "to": {"e": "var", "n": tmp, "p": p}, "x": v}));
      let (test, binds) = self.pattern(&l.pat, &json!({"e": "var", "n": tmp, "p": p}), p);
      return (pre, test, binds)
    }
    let (pre, v) = self.expr(c);
    (pre, v, vec![])
  }
  // A pattern against a value: the test, and the bindings (set where it holds).
  fn pattern(&mut self, pat: &Pat, v: &Value, p: &str) -> (Value, Vec<Value>) {
    let t = json!({"e": "bool", "v": true, "p": p});
    match pat {
      Pat::Wild(_) => (t, vec![]),
      Pat::Ident(i) if i.subpat.is_none() => {
        let n = i.ident.to_string();
        if n == "None" { return (json!({"e": "is", "x": v, "k": "none", "p": p}), vec![]) }
        self.bind_pat(pat);
        (t, vec![json!({"s": "set", "p": p, "to": {"e": "var", "n": n, "p": p}, "x": v})])
      }
      Pat::Ident(i) => { let (tt, mut b) = self.pattern(&i.subpat.as_ref().unwrap().1, v, p); self.bind_pat(pat); b.insert(0, json!({"s": "set", "p": p, "to": {"e": "var", "n": i.ident.to_string(), "p": p}, "x": v})); (tt, b) }
      Pat::Lit(l) => (json!({"e": "cmp", "op": "==", "x": v, "y": self.lit(&l.lit, p).unwrap_or_else(|| no(p, "a literal pattern".into())), "p": p}), vec![]),
      Pat::Or(o) => {
        let mut tests = vec![];
        for c in &o.cases { let (tt, b) = self.pattern(c, v, p); if !b.is_empty() { return (no(p, format!("{}: an or-pattern that binds", text(pat))), vec![]) } tests.push(tt) }
        (json!({"e": "or", "xs": tests, "p": p, "strict": true}), vec![])
      }
      Pat::Path(pp) => {
        let segs: Vec<String> = pp.path.segments.iter().map(|s| s.ident.to_string()).collect();
        if segs.len() == 1 && segs[0] == "None" { return (json!({"e": "is", "x": v, "k": "none", "p": p}), vec![]) }
        (json!({"e": "cmp", "op": "==", "x": v, "y": self.path_expr(&pp.path, p, &text(pat)), "p": p}), vec![])
      }
      Pat::TupleStruct(ts) => {
        let name = last_ident(&ts.path);
        let k = match name.as_str() { "Some" => "some", "Ok" => "ok", "Err" => "err", _ => return (no(p, format!("{}: a variant with data", text(pat))), vec![]) };
        if ts.elems.len() != 1 { return (no(p, format!("{}: a pattern of {} values", text(pat), ts.elems.len())), vec![]) }
        let inner = json!({"e": "unwrap", "x": v, "k": k, "p": p});
        let (tt, b) = self.pattern(&ts.elems[0], &inner, p);
        (json!({"e": "and", "xs": [{"e": "is", "x": v, "k": k, "p": p}, tt], "p": p, "strict": true}), b)
      }
      Pat::Reference(r) => self.pattern(&r.pat, v, p),
      Pat::Range(_) | Pat::Struct(_) | Pat::Tuple(_) | Pat::Slice(_) | _ => (no(p, format!("{}: a pattern outside the subset", text(pat))), vec![]),
    }
  }
  fn match_expr(&mut self, m: &syn::ExprMatch, p: &str) -> (Vec<Value>, Value) {
    let (mut pre, v) = self.expr(&m.expr);
    let scrut = self.temp();
    pre.push(json!({"s": "set", "p": p, "to": {"e": "var", "n": scrut, "p": p}, "x": v}));
    let sv = json!({"e": "var", "n": scrut, "p": p});
    let res = self.temp();
    let rv = json!({"e": "var", "n": res, "p": p});
    // Arms in order: each an if over the ones before it not matching (the last falling to a failure: Rust's match
    // is exhaustive, so that branch is unreachable where the types are the code's).
    let mut chain: Vec<Value> = vec![json!({"s": "fail", "p": p, "why": "a match no arm takes (unreachable for the code's own values)"})];
    for arm in m.arms.iter().rev() {
      let ap = self.at(arm.span());
      self.locals.push(BTreeSet::new());
      let (mut test, mut binds) = self.pattern(&arm.pat, &sv, &ap);
      let guard = arm.guard.as_ref().map(|(_, g)| self.expr(g));
      let (mut body, bv) = self.expr(&arm.body);
      self.locals.pop();
      let mut then = vec![];
      if let Some((gpre, gv)) = guard {
        // A guard reads the bindings: tested inside them, falling to the next arms where it fails.
        let mut inner = gpre; inner.append(&mut body); inner.push(json!({"s": "set", "p": ap, "to": rv, "x": bv}));
        then.append(&mut binds);
        then.push(json!({"s": "if", "p": ap, "c": gv, "then": inner, "else": chain.clone()}));
      } else { then.append(&mut binds); then.append(&mut body); then.push(json!({"s": "set", "p": ap, "to": rv, "x": bv})); }
      if test["e"] == "bool" && test["v"] == true { chain = then; continue }
      chain = vec![json!({"s": "if", "p": ap, "c": test, "then": then, "else": chain})];
    }
    pre.append(&mut chain);
    (pre, rv)
  }
  fn closure(&mut self, c: &syn::ExprClosure, p: &str) -> (Vec<Value>, Value) {
    // A closure: lifted to a function of its parameters and the locals it reads (by value at its making; one that
    // assigns to them is refused).
    let id = format!("{}#closure{}", self.fid, self.lifted.len() + 1);
    let mut params = vec![];
    let mut names = BTreeSet::new();
    for a in &c.inputs {
      match a {
        Pat::Ident(i) => { names.insert(i.ident.to_string()); params.push(json!({"name": i.ident.to_string(), "t": {"k": "any"}})) }
        Pat::Type(t) => { if let Pat::Ident(i) = &*t.pat { names.insert(i.ident.to_string()); params.push(json!({"name": i.ident.to_string(), "t": self.ty(&t.ty)})) } }
        _ => return (vec![], no(p, "a closure's pattern parameter".into())),
      }
    }
    let caps: Vec<String> = self.locals.iter().flatten().filter(|n| !n.starts_with('$') && !names.contains(*n) && mentions(&c.body, n)).cloned().collect::<BTreeSet<_>>().into_iter().collect();
    if caps.iter().any(|n| assigns(&c.body, n)) { return (vec![], no(p, "a closure that assigns to what it captures".into())) }
    for n in &caps { params.push(json!({"name": n, "t": {"k": "any"}, "cap": true})) }
    let mut scope: BTreeSet<String> = names; scope.extend(caps.iter().cloned());
    let saved_locals = std::mem::replace(&mut self.locals, vec![scope]);
    let saved_tmp = self.tmp;
    let saved_fid = std::mem::replace(&mut self.fid, id.clone());
    let (mut body, v) = match &*c.body { Expr::Block(b) => self.block(&b.block), e => self.expr(e) };
    body.push(json!({"s": "ret", "p": p, "x": v}));
    self.locals = saved_locals; self.tmp = saved_tmp; self.fid = saved_fid;
    let f = json!({"id": id, "name": id, "p": p, "span": [self.file, c.span().start().line, c.span().end().line], "params": params, "ret": {"k": "any"}, "body": body, "async": false, "static": true, "decorators": []});
    self.lifted.push((id.clone(), f));
    (vec![], json!({"e": "closure", "id": id, "caps": caps, "p": p}))
  }
  fn args(&mut self, xs: &syn::punctuated::Punctuated<Expr, syn::token::Comma>) -> (Vec<Value>, Vec<Value>) {
    let mut pre = vec![]; let mut out = vec![];
    for a in xs { let (mut s, v) = self.expr(a); pre.append(&mut s); out.push(if is_place(&v) { json!({"e": "copy", "x": v, "p": v["p"]}) } else { v }) }
    (pre, out)
  }
  // Only syntactically unshadowed primitive names enter this shortcut. Imports
  // with unknown exports and a disabled Ord prelude stay on ordinary resolution.
  fn primitive_integer(&self, name: &str) -> bool {
    if !["u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize"].contains(&name) { return false }
    fn imported(t: &syn::UseTree, name: &str, parent: &str) -> bool {
      match t {
        syn::UseTree::Path(p) => imported(&p.tree, name, &p.ident.to_string()),
        syn::UseTree::Name(n) => n.ident == name || (n.ident == "self" && parent == name),
        syn::UseTree::Rename(r) => r.rename == name,
        syn::UseTree::Group(g) => g.items.iter().any(|t| imported(t, name, parent)),
        syn::UseTree::Glob(_) => true,
      }
    }
    if self.structs.contains_key(name) || self.enums.contains_key(name) || self.files.iter().any(|f| f.no_implicit_prelude || f.module.split("::").any(|n| n == name)) { return false }
    !self.files.iter().filter(|f| f.rel == self.file).any(|f| f.items.iter().any(|it| match it {
      Item::Type(t) => t.ident == name,
      Item::Union(u) => u.ident == name,
      Item::Trait(t) => t.ident == name,
      Item::TraitAlias(t) => t.ident == name,
      Item::Mod(m) => m.ident == name,
      Item::Use(u) => imported(&u.tree, name, ""),
      Item::ExternCrate(e) => e.rename.as_ref().map(|(_, n)| n == name).unwrap_or(e.ident == name),
      _ => false,
    }))
  }
  fn closed_integer(&self, t: &Type) -> Option<String> {
    let Type::Path(t) = t else { return None };
    if t.qself.is_some() { return None }
    let n = t.path.get_ident()?.to_string();
    self.primitive_integer(&n).then_some(n)
  }
  fn closed_field(&self, e: &Expr) -> Option<String> {
    let Expr::Field(f) = unparen(e) else { return None };
    if !matches!(&*f.base, Expr::Path(p) if p.qself.is_none() && p.path.is_ident("self")) { return None }
    let syn::Member::Named(n) = &f.member else { return None };
    let (_, s) = self.structs.get(self.self_ty.as_ref()?)?;
    self.closed_integer(&s.fields.iter().find(|f| f.ident.as_ref() == Some(n))?.ty)
  }
  fn closed_assignment(&self, e: &Expr) -> bool {
    let Expr::Assign(a) = e else { return false };
    let Some(ty) = self.closed_field(&a.left) else { return false };
    let (field, literal) = match unparen(&a.right) {
      Expr::Binary(b) if matches!(b.op, BinOp::Add(_)) => (&*b.left, &*b.right),
      Expr::MethodCall(m) if m.method == "wrapping_add" && m.turbofish.is_none() && m.args.len() == 1 => (&*m.receiver, &m.args[0]),
      _ => return false,
    };
    let Expr::Lit(l) = unparen(literal) else { return false };
    let Lit::Int(i) = &l.lit else { return false };
    self.closed_field(field).as_ref() == Some(&ty) && (i.suffix().is_empty() || i.suffix() == ty)
  }
  // A verified fixed function item, not a general indirect-call resolver.
  fn closed_callee(&self, b: &syn::ExprBlock, arity: usize) -> Result<String, &'static str> {
    let shape = "closed callee: requires one primitive assignment and a bare function-item tail";
    if b.label.is_some() { return Err(shape) }
    let [Stmt::Expr(assignment, Some(_)), Stmt::Expr(Expr::Path(tail), None)] = b.block.stmts.as_slice() else { return Err(shape) };
    if tail.qself.is_some() { return Err(shape) }
    let Some(name) = tail.path.get_ident().map(|n| n.to_string()) else { return Err(shape) };
    if self.free_counts.get(&name) != Some(&1) { return Err("closed callee: requires exactly one loaded function declaration") }
    // Nested modules left unexpanded by the loader, absent files, attributes,
    // macros and any imports prevent a complete closed namespace claim.
    if self.files.iter().any(|f| !f.closed_source || f.items.iter().any(|i| matches!(i, Item::Mod(_)))) {
      return Err("closed callee: source namespace is not closed (module, attribute, macro or import)")
    }
    let Some(owner) = &self.self_ty else { return Err("closed callee: caller identity is not established") };
    let mut records = vec![];
    let mut callers = vec![];
    let mut targets = vec![];
    for f in &self.files { for item in &f.items { match item {
      Item::Struct(s) if s.ident == owner.as_str() => records.push((f, s)),
      Item::Impl(i) if matches!(&*i.self_ty, Type::Path(t) if t.qself.is_none() && t.path.is_ident(owner)) => {
        for m in &i.items { if let ImplItem::Fn(m) = m {
          if format!("{owner}::{}", m.sig.ident) == self.fid { callers.push((f, i, m)); }
        } }
      }
      Item::Fn(t) if t.sig.ident == name => targets.push((f, t)),
      _ => {}
    } } }
    let ([(rf, record)], [(cf, implementation, caller)], [(tf, target)]) = (records.as_slice(), callers.as_slice(), targets.as_slice()) else {
      return Err("closed callee: caller/target identity is not unique")
    };
    if cf.rel != self.file || cf.rel != tf.rel || cf.module != tf.module || rf.rel != cf.rel || rf.module != cf.module ||
      !record.generics.params.is_empty() || record.generics.where_clause.is_some() ||
      implementation.trait_.is_some() || !implementation.generics.params.is_empty() || implementation.generics.where_clause.is_some() ||
      !ordinary_function(&caller.sig) {
      return Err("closed callee: caller file/module or ordinary inherent identity is not established")
    }
    let mut bindings = ClosedBindings::default();
    bindings.visit_signature(&caller.sig);
    bindings.visit_block(&caller.block);
    if self.is_local(&name) || bindings.names.contains(&name) || bindings.items || self.files.iter().any(|f| f.items.iter().any(|i| match i {
      Item::Const(i) => i.ident == name, Item::Static(i) => i.ident == name,
      Item::Struct(i) => i.ident == name, Item::Enum(i) => i.ident == name,
      Item::Union(i) => i.ident == name, Item::Type(i) => i.ident == name,
      Item::Trait(i) => i.ident == name, Item::TraitAlias(i) => i.ident == name,
      _ => false,
    })) { return Err("closed callee: local/item or value-name ambiguity") }
    if !ordinary_function(&target.sig) || !matches!(target.vis, syn::Visibility::Inherited | syn::Visibility::Public(_)) ||
      target.sig.inputs.len() != arity || !target.sig.inputs.iter().all(|a| matches!(a, syn::FnArg::Typed(p) if
        matches!(&*p.pat, Pat::Ident(i) if i.by_ref.is_none() && i.subpat.is_none()) && self.closed_integer(&p.ty).is_some())) ||
      !matches!(&target.sig.output, ReturnType::Type(_, t) if self.closed_integer(t).is_some()) {
      return Err("closed callee: requires an ordinary nongeneric integer signature and exact arity")
    }
    if !self.closed_assignment(assignment) { return Err(shape) }
    Ok(name)
  }
  fn call(&mut self, c: &syn::ExprCall, p: &str, t: &str) -> (Vec<Value>, Value) {
    // Only assignment + path-tail candidates enter the new contract. Other
    // callee shapes retain their existing lowering, not a blanket language ban.
    let block = match unparen(&c.func) {
      Expr::Block(b) if matches!(b.block.stmts.as_slice(), [Stmt::Expr(Expr::Assign(_), Some(_)), Stmt::Expr(Expr::Path(_), None)]) => Some(b),
      _ => None,
    };
    if let Some(b) = block {
      let name = match self.closed_callee(b, c.args.len()) { Ok(n) => n, Err(why) => return (vec![], no(p, why.into())) };
      let Stmt::Expr(assignment, _) = &b.block.stmts[0] else { unreachable!() };
      let (mut pre, _) = self.expr(assignment);
      let mut args = vec![];
      for arg in &c.args {
        let (mut ap, value) = self.expr(arg);
        pre.append(&mut ap);
        let value = if is_place(&value) { json!({"e": "copy", "x": value, "p": value["p"]}) } else { value };
        let var = json!({"e": "var", "n": self.temp(), "p": p});
        pre.push(json!({"s": "set", "p": p, "to": var, "x": value})); args.push(var);
      }
      return (pre, json!({"e": "call", "f": {"e": "fn", "id": name, "p": p}, "args": args, "kw": [], "p": p, "text": t}));
    }
    // A resolved free function is a fixed callee, unlike a mutable local callable.
    // Materialize its arguments in source order, not after all their preludes.
    if let Expr::Path(x) = &*c.func {
      if x.qself.is_none() && x.path.leading_colon.is_none() && x.path.segments.len() == 1 &&
        matches!(x.path.segments[0].arguments, syn::PathArguments::None) {
        let f = self.path_expr(&x.path, p, t);
        if f["e"] == "fn" {
          let mut pre = vec![]; let mut args = vec![];
          for arg in &c.args {
            let (mut ap, value) = self.expr(arg);
            pre.append(&mut ap);
            let value = if is_place(&value) { json!({"e": "copy", "x": value, "p": value["p"]}) } else { value };
            let var = json!({"e": "var", "n": self.temp(), "p": p});
            pre.push(json!({"s": "set", "p": p, "to": var, "x": value})); args.push(var);
          }
          return (pre, json!({"e": "call", "f": f, "args": args, "kw": [], "p": p, "text": t}))
        }
      }
    }
    let (mut pre, args) = self.args(&c.args);
    let f = match &*c.func { Expr::Path(x) => x.path.clone(), _ => { let (mut fp, fv) = self.expr(&c.func); pre.append(&mut fp); return (pre, json!({"e": "call", "f": fv, "args": args, "kw": [], "p": p, "text": t})) } };
    let segs: Vec<String> = f.segments.iter().map(|s| s.ident.to_string()).collect();
    let name = segs.last().unwrap().as_str();
    let a0 = args.first().cloned().unwrap_or(Value::Null);
    let k = |kind: &str| json!({"e": kind, "x": a0, "p": p});
    let v = match (segs.len(), name) {
      (1, "Some") => k("some"), (1, "Ok") => k("ok"), (1, "Err") => k("err"),
      (2, "min") | (2, "max") if args.len() == 2 && self.primitive_integer(&segs[0]) &&
        matches!(&*c.func, Expr::Path(x) if x.qself.is_none()) && f.segments.iter().all(|s| matches!(s.arguments, syn::PathArguments::None)) =>
        json!({"e": "call", "f": {"e": "builtin", "n": name, "p": p}, "args": args, "kw": [], "p": p, "text": t}),
      (_, "max") | (_, "min") if segs.iter().any(|s| s == "cmp") || (segs.len() == 1 && !self.free.contains_key(name)) => json!({"e": "call", "f": {"e": "builtin", "n": name, "p": p}, "args": args, "kw": [], "p": p, "text": t}),
      (2, _) if segs[0] == "Instant" && name == "now" => json!({"e": "clock", "p": p}),
      // An atomic's or a lock's constructor: the value it holds (read and written as the field it is).
      (_, "new") if segs.len() >= 2 && (segs[segs.len() - 2].starts_with("Atomic") || ["Mutex", "RwLock", "Cell", "RefCell"].contains(&segs[segs.len() - 2].as_str())) => a0.clone(),
      (2, _) if segs[0] == "Duration" => {
        let unit = match name { "from_secs" => 1_000_000_000i64, "from_millis" => 1_000_000, "from_micros" => 1_000, "from_nanos" => 1, _ => 0 };
        if unit == 0 { no(p, format!("{t}: Duration::{name}")) } else { json!({"e": "bin", "op": "*", "x": a0, "y": {"e": "int", "v": unit.to_string(), "p": p}, "p": p, "text": t, "ovf": "trap", "dur": true}) }
      }
      (2, "from") if ["u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize"].contains(&segs[0].as_str()) => json!({"e": "cast", "x": a0, "ty": self.ty(&syn::parse_str::<Type>(&segs[0]).unwrap()), "p": p, "text": t}),
      _ => {
        let fv = self.path_expr(&f, p, t);
        if fv["e"] == "var" { json!({"e": "call", "f": fv, "args": args, "kw": [], "p": p, "text": t}) }
        else { json!({"e": "call", "f": fv, "args": args, "kw": [], "p": p, "text": t}) }
      }
    };
    (pre, v)
  }
  // Only fixed, directly named state fields: no computed receiver, trait dispatch,
  // generic instantiation or alias expansion enters this sequencing shortcut.
  fn fixed_method_field(&self, m: &syn::ExprMethodCall) -> bool {
    if m.turbofish.is_some() { return false }
    let Expr::Field(f) = &*m.receiver else { return false };
    if !matches!(&*f.base, Expr::Path(p) if p.qself.is_none() && p.path.is_ident("self")) { return false }
    let syn::Member::Named(member) = &f.member else { return false };
    let Some((_, owner)) = self.self_ty.as_ref().and_then(|n| self.structs.get(n)) else { return false };
    let Some(field) = owner.fields.iter().find(|fd| fd.ident.as_ref() == Some(member)) else { return false };
    let Type::Path(t) = &field.ty else { return false };
    if t.qself.is_some() { return false }
    let Some(ty) = t.path.get_ident().map(|n| n.to_string()) else { return false };
    let name = m.method.to_string();
    if self.primitive_integer(&ty) { return matches!(name.as_str(), "min" | "max") && m.args.len() == 1 }
    let Some((file, rec)) = self.structs.get(&ty) else { return false };
    if file != &self.file || !rec.generics.params.is_empty() ||
      self.smod.get(&ty) != self.self_ty.as_ref().and_then(|n| self.smod.get(n)) { return false }
    if self.methods.get(&ty).map(|ms| ms.iter().filter(|(_, _, f)| f.sig.ident == m.method).count()) != Some(1) { return false }
    self.files.iter().filter(|f| f.rel == self.file).any(|f| f.items.iter().any(|it| {
      let Item::Impl(im) = it else { return false };
      im.trait_.is_none() && im.generics.params.is_empty() &&
        matches!(&*im.self_ty, Type::Path(t) if t.qself.is_none() && t.path.is_ident(&ty)) &&
        im.items.iter().any(|it| matches!(it, ImplItem::Fn(f) if f.sig.ident == m.method &&
          f.sig.generics.params.is_empty() && f.sig.inputs.len() == m.args.len() + 1 &&
          matches!(f.sig.inputs.first(), Some(syn::FnArg::Receiver(r)) if r.reference.is_some())))
    }))
  }
  // D1 only: a direct primitive field plus a compatible integer literal is a
  // pure, statically typed receiver. Blocks, calls and other arithmetic stay out.
  fn literal_sum_receiver(&self, m: &syn::ExprMethodCall) -> bool {
    if m.turbofish.is_some() || m.args.len() != 1 || (m.method != "min" && m.method != "max") { return false }
    fn unparen(mut e: &Expr) -> &Expr { while let Expr::Paren(p) = e { e = &p.expr; } e }
    let Expr::Binary(b) = unparen(&m.receiver) else { return false };
    if !matches!(b.op, BinOp::Add(_)) { return false }
    let Expr::Field(f) = unparen(&b.left) else { return false };
    if !matches!(&*f.base, Expr::Path(p) if p.qself.is_none() && p.path.is_ident("self")) { return false }
    let syn::Member::Named(member) = &f.member else { return false };
    let Expr::Lit(lit) = unparen(&b.right) else { return false };
    let Lit::Int(lit) = &lit.lit else { return false };
    let Some((_, owner)) = self.self_ty.as_ref().and_then(|n| self.structs.get(n)) else { return false };
    let Some(field) = owner.fields.iter().find(|fd| fd.ident.as_ref() == Some(member)) else { return false };
    let Type::Path(t) = &field.ty else { return false };
    if t.qself.is_some() { return false }
    let Some(ty) = t.path.get_ident().map(|n| n.to_string()) else { return false };
    self.primitive_integer(&ty) && (lit.suffix().is_empty() || lit.suffix() == ty.as_str())
  }
  // D2: preserve the existing block prelude, then capture its known scalar
  // field tail before argument effects. Early exits still leave through the prelude.
  fn scalar_block_receiver(&self, m: &syn::ExprMethodCall) -> bool {
    if m.turbofish.is_some() || m.args.len() != 1 || (m.method != "min" && m.method != "max") { return false }
    fn unparen(mut e: &Expr) -> &Expr { while let Expr::Paren(p) = e { e = &p.expr; } e }
    let Expr::Block(b) = unparen(&m.receiver) else { return false };
    if b.label.is_some() { return false }
    let Some(Stmt::Expr(tail, None)) = b.block.stmts.last() else { return false };
    let Expr::Field(f) = unparen(tail) else { return false };
    if !matches!(&*f.base, Expr::Path(p) if p.qself.is_none() && p.path.is_ident("self")) { return false }
    let syn::Member::Named(member) = &f.member else { return false };
    let Some((_, owner)) = self.self_ty.as_ref().and_then(|n| self.structs.get(n)) else { return false };
    let Some(field) = owner.fields.iter().find(|fd| fd.ident.as_ref() == Some(member)) else { return false };
    let Type::Path(t) = &field.ty else { return false };
    if t.qself.is_some() { return false }
    let Some(ty) = t.path.get_ident().map(|n| n.to_string()) else { return false };
    self.primitive_integer(&ty)
  }
  fn method(&mut self, m: &syn::ExprMethodCall, p: &str, t: &str) -> (Vec<Value>, Value) {
    let (mut pre, r) = self.expr(&m.receiver);
    let name = m.method.to_string();
    if ((name == "load" && m.args.len() == 1) || (name == "store" && m.args.len() == 2)) && self.atomic_field(&m.receiver) {
      // Rust evaluates arguments left to right. Capture each value (including
      // any failure) after its own prelude, before the next argument's effects.
      let mut values = vec![];
      for arg in &m.args {
        let (mut ap, value) = self.expr(arg);
        pre.append(&mut ap);
        let value = if is_place(&value) { json!({"e": "copy", "x": value, "p": value["p"]}) } else { value };
        let var = json!({"e": "var", "n": self.temp(), "p": p});
        pre.push(json!({"s": "set", "p": p, "to": var, "x": value})); values.push(var);
      }
      let allowed = if name == "load" { ["Relaxed", "Acquire", "SeqCst"] } else { ["Relaxed", "Release", "SeqCst"] };
      let tests: Vec<Value> = allowed.iter().map(|order| json!({"e": "cmp", "op": "==", "x": values.last().unwrap(), "y": ordering_variant(order, p), "p": p})).collect();
      pre.push(json!({"s": "if", "p": p, "c": {"e": "or", "xs": tests, "strict": true, "p": p}, "then": [], "else": [{"s": "fail", "p": p, "why": format!("atomic {name}: invalid memory ordering")}]}));
      return (pre, json!({"e": "rmw", "op": name, "place": r, "args": values[..values.len()-1].to_vec(), "p": p, "text": t}));
    }
    let (r, args) = if self.fixed_method_field(m) || self.literal_sum_receiver(m) || self.scalar_block_receiver(m) {
      // A scalar receiver is captured by value; a borrowed record keeps its
      // identity (no copy node). Then materialize each argument in source order.
      let receiver = json!({"e": "var", "n": self.temp(), "p": p});
      pre.push(json!({"s": "set", "p": p, "to": receiver, "x": r}));
      let mut args = vec![];
      for arg in &m.args {
        let (mut ap, value) = self.expr(arg);
        pre.append(&mut ap);
        let value = if is_place(&value) { json!({"e": "copy", "x": value, "p": value["p"]}) } else { value };
        let var = json!({"e": "var", "n": self.temp(), "p": p});
        pre.push(json!({"s": "set", "p": p, "to": var, "x": value})); args.push(var);
      }
      (receiver, args)
    } else {
      let (mut ap, args) = self.args(&m.args);
      pre.append(&mut ap);
      (r, args)
    };
    let a = |i: usize| args.get(i).cloned().unwrap_or(Value::Null);
    let bin = |op: &str, ovf: &str| json!({"e": "bin", "op": op, "x": r, "y": a(0), "p": p, "text": t, "ovf": ovf, "div": "trunc"});
    let v = match name.as_str() {
      // Options and Results.
      "is_some" => json!({"e": "is", "x": r, "k": "some", "p": p}), "is_none" => json!({"e": "is", "x": r, "k": "none", "p": p}),
      "is_ok" => json!({"e": "is", "x": r, "k": "ok", "p": p}), "is_err" => json!({"e": "is", "x": r, "k": "err", "p": p}),
      "unwrap" | "expect" if m.receiver.to_token_stream().to_string().ends_with("lock ()") => r,
      "unwrap" | "expect" => json!({"e": "expect", "x": r, "p": p, "text": t}),
      "unwrap_or" => json!({"e": "opt_or", "x": r, "d": a(0), "p": p}),
      "unwrap_or_default" => json!({"e": "opt_or", "x": r, "d": {"e": "zero", "p": p}, "p": p}),
      "ok" => json!({"e": "res_ok", "x": r, "p": p}),
      // Integers (and Durations and Instants, which are integers here).
      "min" | "max" => json!({"e": "call", "f": {"e": "builtin", "n": name, "p": p}, "args": [r, a(0)], "kw": [], "p": p, "text": t}),
      "abs" => json!({"e": "call", "f": {"e": "builtin", "n": "abs", "p": p}, "args": [r], "kw": [], "p": p, "text": t}),
      "saturating_add" => bin("+", "sat"), "saturating_sub" => bin("-", "sat"), "saturating_mul" => bin("*", "sat"),
      "wrapping_add" => bin("+", "wrap"), "wrapping_sub" => bin("-", "wrap"), "wrapping_mul" => bin("*", "wrap"),
      "checked_add" => bin("+", "checked"), "checked_sub" => bin("-", "checked"), "checked_mul" => bin("*", "checked"), "checked_div" => bin("/", "checked"),
      "duration_since" | "saturating_duration_since" => bin("-", "sat0"),
      "checked_duration_since" => bin("-", "checked0"),
      "elapsed" => json!({"e": "bin", "op": "-", "x": {"e": "clock", "p": p}, "y": r, "p": p, "text": t, "ovf": "sat0"}),
      "as_nanos" => r, "as_micros" => json!({"e": "bin", "op": "/", "x": r, "y": {"e": "int", "v": "1000", "p": p}, "p": p, "ovf": "trap", "div": "trunc"}),
      "as_millis" => json!({"e": "bin", "op": "/", "x": r, "y": {"e": "int", "v": "1000000", "p": p}, "p": p, "ovf": "trap", "div": "trunc"}),
      "as_secs" => json!({"e": "bin", "op": "/", "x": r, "y": {"e": "int", "v": "1000000000", "p": p}, "p": p, "ovf": "trap", "div": "trunc"}),
      "is_zero" => json!({"e": "cmp", "op": "==", "x": r, "y": {"e": "int", "v": "0", "p": p}, "p": p}),
      // Atomics: a read-modify-write of the field they are (one step is one call: the claim is for calls that don't
      // interleave).
      "load" | "store" | "fetch_add" | "fetch_sub" | "swap" | "compare_exchange" | "compare_exchange_weak" | "fetch_max" | "fetch_min" if args.iter().any(|x| x.get("ord").is_some()) =>
        json!({"e": "rmw", "op": name, "place": r, "args": args.iter().filter(|x| x.get("ord").is_none()).cloned().collect::<Vec<_>>(), "p": p, "text": t}),
      // A Mutex's lock is its value (a step holds it to its end).
      "lock" | "read" | "write" if args.is_empty() => json!({"e": "lock", "x": r, "p": p}),
      "clone" | "to_owned" | "into" | "to_string" | "as_str" if args.is_empty() => json!({"e": "copy", "x": r, "p": p}),
      _ => json!({"e": "call", "f": {"e": "get", "x": r, "f": name, "p": p, "text": format!("{}.{name}", text(&m.receiver))}, "args": args, "kw": [], "p": p, "text": t}),
    };
    (pre, v)
  }
  fn mac(&mut self, m: &syn::Macro, s: Span) -> (Vec<Value>, Value) {
    let p = self.at(s);
    let name = last_ident(&m.path);
    let args: Vec<Expr> = m.parse_body_with(syn::punctuated::Punctuated::<Expr, syn::token::Comma>::parse_terminated).map(|x| x.into_iter().collect()).unwrap_or_default();
    let fail = |why: String| json!({"s": "fail", "p": p, "why": why});
    match name.as_str() {
      "panic" | "unreachable" | "todo" | "unimplemented" => (vec![fail(format!("{name}!"))], Value::Null),
      "assert" | "debug_assert" if !args.is_empty() => {
        let (mut pre, c) = self.expr(&args[0]);
        pre.push(json!({"s": "if", "p": p, "c": c, "then": [], "else": [fail(format!("{name}!({})", text(&args[0])))]}));
        (pre, Value::Null)
      }
      "assert_eq" | "assert_ne" | "debug_assert_eq" | "debug_assert_ne" if args.len() >= 2 => {
        let (mut pre, a) = self.expr(&args[0]); let (mut bp, b) = self.expr(&args[1]); pre.append(&mut bp);
        let op = if name.ends_with("_eq") { "==" } else { "!=" };
        pre.push(json!({"s": "if", "p": p, "c": {"e": "cmp", "op": op, "x": a, "y": b, "p": p}, "then": [], "else": [fail(format!("{name}!"))]}));
        (pre, Value::Null)
      }
      "format" | "println" | "eprintln" | "print" | "eprint" | "write" | "writeln" | "trace" | "debug" | "info" | "warn" | "error" => (vec![], json!({"e": "opaque", "why": format!("{name}!(...): a formatted string or a log line"), "p": p})),
      "matches" if args.len() >= 1 => (vec![], no(&p, "matches!".into())),
      _ => (vec![], no(&p, format!("{name}!: a macro the subset doesn't read"))),
    }
  }
}
fn mentions(e: &Expr, n: &str) -> bool { e.to_token_stream().into_iter().any(|t| tok_has(&t, n)) }
fn tok_has(t: &proc_macro2::TokenTree, n: &str) -> bool { match t { proc_macro2::TokenTree::Ident(i) => i == n, proc_macro2::TokenTree::Group(g) => g.stream().into_iter().any(|x| tok_has(&x, n)), _ => false } }
fn assigns(e: &Expr, n: &str) -> bool {
  let s = e.to_token_stream().to_string();
  let mut i = 0;
  while let Some(k) = s[i..].find(n) {
    let at = i + k; let rest = &s[at + n.len()..];
    let before_ok = at == 0 || !s[..at].ends_with(|c: char| c.is_alphanumeric() || c == '_' || c == '.');
    if before_ok && (rest.starts_with(" = ") || rest.starts_with(" += ") || rest.starts_with(" -= ") || rest.starts_with(" *= ")) { return true }
    i = at + n.len();
  }
  false
}

const MAX_DEPTH: i64 = 1000;
// The reader on a thread of 1 GiB of stack (reserved, not used): MAX_DEPTH levels of syn's recursion fit in it.
fn main() {
  let t = std::thread::Builder::new().stack_size(1 << 30).spawn(run).expect("a thread");
  if t.join().is_err() { std::process::exit(101) }
}
fn run() {
  let req: Value = serde_json::from_str(&std::env::args().nth(1).expect("a request")).expect("JSON");
  let root = PathBuf::from(req["root"].as_str().unwrap());
  let files = match Reader::load(&root) { Ok(f) => f, Err(e) => { println!("{}", json!({"error": e})); return } };
  // Choose crate-root bridge names BEFORE rewriting calls. Reallocating after
  // insertion would count the chosen references and could choose another suffix.
  if let Some(scope) = req.get("harness_bridges") {
    let roots: Vec<_> = files.iter().filter(|f| f.module == "crate" && Some(f.rel.as_str()) == scope["file"].as_str()).collect();
    if let [f] = roots.as_slice() {
      let names = native_helper_name(&files, f, "__gdp_now", true).and_then(|now|
        native_helper_name(&files, f, "__gdp_answer", true).map(|answer| (now, answer)));
      match names {
        Ok((now, answer)) => println!("{}", json!({"now": now, "answer": answer})),
        Err(why) => println!("{}", json!({"error": why})),
      }
    } else {
      println!("{}", json!({"error": "native replay requires one known crate-root bridge scope"}));
    }
    return;
  }
  // Native replay reparses the rewritten copy, so answer/clock edits cannot
  // stale an inline module's byte position. This does not alter reader admission.
  if let Some(scope) = req.get("harness_scope") {
    let matches: Vec<_> = files.iter().filter(|f| Some(f.rel.as_str()) == scope["file"].as_str() && Some(f.module.as_str()) == scope["module"].as_str()).collect();
    if let [f] = matches.as_slice() {
      match native_helper_name(&files, f, "__gdp_harness", false) {
        Ok(name) => println!("{}", json!({"inline_end": f.inline_end, "harness_name": name})),
        Err(why) => println!("{}", json!({"error": why})),
      }
    } else {
      println!("{}", json!({"error": "native replay requires one known file/module scope"}));
    }
    return;
  }
  let mut r = Reader { files, smod: BTreeMap::new(), structs: BTreeMap::new(), enums: BTreeMap::new(), consts: BTreeMap::new(), recs: Map::new(), funcs: Map::new(), methods: BTreeMap::new(), free: BTreeMap::new(), fmod: BTreeMap::new(), free_counts: BTreeMap::new(), file: String::new(), tmp: 0, locals: vec![], self_ty: None, lifted: vec![], fid: String::new() };
  r.index();
  for n in r.structs.keys().cloned().collect::<Vec<_>>() { r.rec(&n); }
  let mut entries = vec![];
  let mut entry_file = String::new();
  // (no names: every struct of the crate, for the entry inferred)
  let all: Vec<Value> = r.structs.keys().map(|k| json!(k)).collect();
  let names = req["names"].as_array().unwrap();
  for n in if names.is_empty() { &all } else { names } {
    let n = n.as_str().unwrap();
    if r.structs.contains_key(n) { entry_file = r.structs[n].0.clone(); r.rec(n); entries.push(json!({"k": "class", "rec": n})); }
    else if let Some((file, f)) = r.free.get(n).cloned() { entry_file = file.clone(); let fv = r.func(&file, &f.sig, &f.block, &f.attrs, None, n); r.funcs.insert(n.to_string(), fv); entries.push(json!({"k": "func", "id": n})); }
    else { entries.push(json!({"k": "missing", "name": n})); }
  }
  // The crate's free functions, for the calls the entries make.
  for (n, (file, f)) in r.free.clone() { if !r.funcs.contains_key(&n) { let fv = r.func(&file, &f.sig, &f.block, &f.attrs, None, &n); r.funcs.insert(n, fv); } }
  for (id, f) in std::mem::take(&mut r.lifted) { r.funcs.insert(id, f); }
  let recs: Map<String, Value> = r.recs.into_iter().filter(|(_, v)| !v.is_null()).collect();
  let enums: Map<String, Value> = r.enums.iter().map(|(k, e)| (k.clone(), json!({"values": e.values, "discs": e.discs, "data": e.data}))).collect();
  println!("{}", json!({"lang": "rust", "file": Path::new(&entry_file).file_name().map(|x| x.to_string_lossy().to_string()).unwrap_or_default(), "path": root.join(&entry_file).display().to_string(), "module": "crate", "root": root.display().to_string(), "entries": entries, "fmods": r.fmod, "recs": recs, "funcs": r.funcs, "enums": enums}));
}
