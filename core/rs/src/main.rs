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
use syn::{BinOp, Expr, Fields, ImplItem, Item, Lit, Pat, ReturnType, Stmt, Type, UnOp};

struct File { rel: String, items: Vec<Item>, module: String }
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
fn last_ident(p: &syn::Path) -> String { p.segments.last().map(|s| s.ident.to_string()).unwrap_or_default() }
fn path_str(p: &syn::Path) -> String { p.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::") }
fn is_place(v: &Value) -> bool { matches!(v["e"].as_str(), Some("var") | Some("get") | Some("idx")) }

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
    let f = syn::parse_file(&src).map_err(|e| format!("{}: {e}", rel.display()))?;
    let dir: PathBuf = if rel.file_name().map(|n| n == "lib.rs" || n == "main.rs" || n == "mod.rs").unwrap_or(false) { rel.parent().unwrap().to_path_buf() } else { rel.with_extension("") };
    let mut items = vec![];
    for it in f.items {
      if let Item::Mod(m) = &it {
        if m.attrs.iter().any(|a| a.path().is_ident("cfg") && text(&a.meta).contains("test")) { continue }
        let name = m.ident.to_string();
        let sub = format!("{module}::{name}");
        match &m.content {
          Some((_, inner)) => { out.push(File { rel: rel.display().to_string(), items: inner.clone(), module: sub }); }
          None => {
            let a = dir.join(format!("{name}.rs"));
            let b = dir.join(&name).join("mod.rs");
            let r = if root.join(&a).exists() { a } else if root.join(&b).exists() { b } else { continue };
            Self::load_file(root, &r, &sub, out)?;
          }
        }
        continue
      }
      items.push(it);
    }
    out.push(File { rel: rel.display().to_string(), items, module: module.to_string() });
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
          Item::Fn(fun) => { self.free.insert(fun.sig.ident.to_string(), (f.rel.clone(), fun.clone())); self.fmod.insert(fun.sig.ident.to_string(), f.module.clone()); }
          Item::Const(c) => { if let Expr::Lit(l) = &*c.expr { if let Some(v) = self.lit(&l.lit, "") { self.consts.insert(c.ident.to_string(), v); } } }
          _ => {}
        }
      }
    }
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
  fn named(&self, name: &str, t: &Type) -> Value {
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
    let generic = !s.generics.params.is_empty();
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
    let (mut body, tail) = self.block(block);
    if !tail.is_null() && tail["e"] != "none" { body.push(json!({"s": "ret", "p": self.at(block.span()), "x": tail})) }
    let ret = match &sig.output { ReturnType::Default => json!({"k": "none"}), ReturnType::Type(_, t) => self.ty(t) };
    let generic = !sig.generics.params.is_empty();
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
      Expr::Call(c) => self.call(c, &p, &t),
      Expr::MethodCall(m) => self.method(m, &p, &t),
      Expr::Struct(s) => {
        // An enum's variant with fields (an error's payload, say): a value the subset keeps only where nothing reads it.
        if s.path.segments.len() >= 2 && self.enums.contains_key(&s.path.segments[s.path.segments.len() - 2].ident.to_string()) {
          let mut pre = vec![];
          for f in &s.fields { let (mut a, _) = self.expr(&f.expr); pre.append(&mut a); }
          return (pre, json!({"e": "opaque", "why": format!("{t}: an enum variant with data"), "p": p}))
        }
        let name = last_ident(&s.path);
        let name = if name == "Self" { self.self_ty.clone().unwrap_or(name) } else { name };
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
      let (mut body, bv) = self.expr(&arm.body);
      self.locals.pop();
      let mut then = vec![];
      if let Some((_, g)) = &arm.guard {
        // A guard reads the bindings: tested inside them, falling to the next arms where it fails.
        let (gpre, gv) = self.expr(g);
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
  fn call(&mut self, c: &syn::ExprCall, p: &str, t: &str) -> (Vec<Value>, Value) {
    let (mut pre, args) = self.args(&c.args);
    let f = match &*c.func { Expr::Path(x) => x.path.clone(), _ => { let (mut fp, fv) = self.expr(&c.func); pre.append(&mut fp); return (pre, json!({"e": "call", "f": fv, "args": args, "kw": [], "p": p, "text": t})) } };
    let segs: Vec<String> = f.segments.iter().map(|s| s.ident.to_string()).collect();
    let name = segs.last().unwrap().as_str();
    let a0 = args.first().cloned().unwrap_or(Value::Null);
    let k = |kind: &str| json!({"e": kind, "x": a0, "p": p});
    let v = match (segs.len(), name) {
      (1, "Some") => k("some"), (1, "Ok") => k("ok"), (1, "Err") => k("err"),
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
  fn method(&mut self, m: &syn::ExprMethodCall, p: &str, t: &str) -> (Vec<Value>, Value) {
    let (mut pre, r) = self.expr(&m.receiver);
    let (mut ap, args) = self.args(&m.args);
    pre.append(&mut ap);
    let name = m.method.to_string();
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

fn main() {
  let req: Value = serde_json::from_str(&std::env::args().nth(1).expect("a request")).expect("JSON");
  let root = PathBuf::from(req["root"].as_str().unwrap());
  let files = match Reader::load(&root) { Ok(f) => f, Err(e) => { println!("{}", json!({"error": e})); return } };
  let mut r = Reader { files, smod: BTreeMap::new(), structs: BTreeMap::new(), enums: BTreeMap::new(), consts: BTreeMap::new(), recs: Map::new(), funcs: Map::new(), methods: BTreeMap::new(), free: BTreeMap::new(), fmod: BTreeMap::new(), file: String::new(), tmp: 0, locals: vec![], self_ty: None, lifted: vec![], fid: String::new() };
  r.index();
  for n in r.structs.keys().cloned().collect::<Vec<_>>() { r.rec(&n); }
  let mut entries = vec![];
  let mut entry_file = String::new();
  for n in req["names"].as_array().unwrap() {
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
