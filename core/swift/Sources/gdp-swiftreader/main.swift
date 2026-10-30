// The extractor's Swift reader (core/extract-swift.ts): a package's sources read through swift-syntax's parser and
// lowered into the shared step IR (core/extract-step.ts's SModule, as JSON on stdout), which the shared executor runs
// into the rule. Types are the code's declared ones (a property's annotation or its literal initializer, a parameter's,
// a result's, a protocol's requirements), never inferred past what the declarations say: a value of no declared type
// is opaque, refused where a step reads it. Nothing here decides the subset beyond the syntax: a construct the IR has no
// node for becomes {"e": "no"} / {"s": "no"} with the reason, refused only where a step reaches it. Integer semantics
// are the IR's own operations: `+ - *` trap past the type's range (Swift's default), `&+ &- &*` wrap, `/ %` truncate,
// Int32(x) traps where x doesn't fit, Int32(truncatingIfNeeded:) wraps, Int32(clamping:) saturates.
//
//   gdp-swiftreader <root> <entry file or -> <names,comma-separated or -> <ctor arity or -> <file>...
import Foundation
import SwiftOperators
import SwiftParser
import SwiftSyntax

// --- JSON ----------------------------------------------------------------------------------------------------------
indirect enum J: ExpressibleByStringLiteral, ExpressibleByIntegerLiteral, ExpressibleByBooleanLiteral, ExpressibleByArrayLiteral, ExpressibleByDictionaryLiteral, ExpressibleByNilLiteral {
  case null, b(Bool), i(Int), s(String), a([J]), o([(String, J)])
  init(stringLiteral v: String) { self = .s(v) }
  init(integerLiteral v: Int) { self = .i(v) }
  init(booleanLiteral v: Bool) { self = .b(v) }
  init(arrayLiteral xs: J...) { self = .a(xs) }
  init(dictionaryLiteral kv: (String, J)...) { self = .o(kv.filter { if case .null = $0.1 { return false }; return true }) }
  init(nilLiteral: ()) { self = .null }
  subscript(k: String) -> J {
    get { if case .o(let kv) = self { return kv.first { $0.0 == k }?.1 ?? .null }; return .null }
    set {
      guard case .o(var kv) = self else { return }
      if let i = kv.firstIndex(where: { $0.0 == k }) { kv[i].1 = newValue } else { kv.append((k, newValue)) }
      self = .o(kv)
    }
  }
  var str: String? { if case .s(let s) = self { return s }; return nil }
  var isNull: Bool { if case .null = self { return true }; return false }
  var arr: [J] { if case .a(let xs) = self { return xs }; return [] }
  func write(_ out: inout String) {
    switch self {
    case .null: out += "null"
    case .b(let b): out += b ? "true" : "false"
    case .i(let i): out += String(i)
    case .s(let s):
      out += "\""
      for u in s.unicodeScalars {
        switch u {
        case "\"": out += "\\\""
        case "\\": out += "\\\\"
        case "\n": out += "\\n"
        case "\r": out += "\\r"
        case "\t": out += "\\t"
        default: if u.value < 0x20 { out += String(format: "\\u%04x", u.value) } else { out.unicodeScalars.append(u) }
        }
      }
      out += "\""
    case .a(let xs): out += "["; for (i, x) in xs.enumerated() { if i > 0 { out += "," }; x.write(&out) }; out += "]"
    case .o(let kv): out += "{"; for (i, (k, v)) in kv.enumerated() { if i > 0 { out += "," }; J.s(k).write(&out); out += ":"; v.write(&out) }; out += "}"
    }
  }
}
func X(_ e: String, _ p: String, _ kv: [(String, J)] = []) -> J { .o([("e", .s(e)), ("p", .s(p))] + kv.filter { !$0.1.isNull }) }
func S(_ s: String, _ p: String, _ kv: [(String, J)] = []) -> J { .o([("s", .s(s)), ("p", .s(p))] + kv.filter { !$0.1.isNull }) }
func no(_ p: String, _ why: String) -> J { X("no", p, [("why", .s(why))]) }
func sno(_ p: String, _ why: String) -> J { S("no", p, [("why", .s(why))]) }
func v(_ n: String, _ p: String) -> J { X("var", p, [("n", .s(n))]) }
func isPlace(_ x: J) -> Bool { ["var", "get", "idx"].contains(x["e"].str ?? "") }
func short(_ t: String) -> String { let s = t.split(whereSeparator: { $0.isWhitespace }).joined(separator: " "); return s.count <= 60 ? s : String(s.prefix(57)) + "..." }

// --- types, read from their text (the declared ones only) ---------------------------------------------------------
indirect enum TT: Equatable {
  case n(String, [TT]), opt(TT), dict(TT, TT), arr(TT), tup([TT]), fn, bad(String)
  var name: String? { if case .n(let n, _) = self { return n }; return nil }
}
func parseType(_ text: String) -> TT {
  var toks: [String] = []
  var i = text.startIndex
  while i < text.endIndex {
    let c = text[i]
    if c.isWhitespace { i = text.index(after: i); continue }
    if c.isLetter || c == "_" || c == "@" {
      var j = text.index(after: i)
      while j < text.endIndex, text[j].isLetter || text[j].isNumber || text[j] == "_" || text[j] == "." { j = text.index(after: j) }
      toks.append(String(text[i..<j])); i = j; continue
    }
    if c == "-", text.index(after: i) < text.endIndex, text[text.index(after: i)] == ">" { toks.append("->"); i = text.index(i, offsetBy: 2); continue }
    toks.append(String(c)); i = text.index(after: i)
  }
  var k = 0
  func peek() -> String? { k < toks.count ? toks[k] : nil }
  func type() -> TT {
    while let t = peek(), ["any", "some", "inout", "borrowing", "consuming", "sending", "__owned", "__shared"].contains(t) || t.hasPrefix("@") { k += 1 }
    var out: TT
    guard let t = peek() else { return .bad(text) }
    if t == "[" {
      k += 1
      let a = type()
      if peek() == ":" { k += 1; let b = type(); if peek() == "]" { k += 1 }; out = .dict(a, b) } else { if peek() == "]" { k += 1 }; out = .arr(a) }
    } else if t == "(" {
      k += 1
      var xs: [TT] = []
      while let p = peek(), p != ")" { if p == "," { k += 1; continue }; if k + 1 < toks.count, toks[k + 1] == ":" { k += 2 }; xs.append(type()) }
      k += 1
      if peek() == "->" || peek() == "throws" || peek() == "async" { return .fn }
      out = xs.count == 1 ? xs[0] : .tup(xs)
    } else if t.first?.isLetter == true || t.first == "_" {
      k += 1
      var name = t.hasPrefix("Swift.") ? String(t.dropFirst(6)) : t
      var args: [TT] = []
      if peek() == "<" { k += 1; while let p = peek(), p != ">" { if p == "," { k += 1; continue }; args.append(type()) }; k += 1 }
      if name.hasSuffix(".Type") || name.hasSuffix(".Protocol") { name = "?meta" }
      if name == "Optional", args.count == 1 { out = .opt(args[0]) }
      else if name == "Dictionary", args.count == 2 { out = .dict(args[0], args[1]) }
      else if name == "Array", args.count == 1 { out = .arr(args[0]) }
      else { out = .n(name, args) }
    } else { return .bad(text) }
    while let p = peek(), p == "?" || p == "!" { k += 1; out = .opt(out) }
    if peek() == "->" { return .fn }
    return out
  }
  let t = type()
  return k < toks.count && toks[k] != "throws" ? .bad(text) : t
}
let INTS: [String: (Int, Bool)] = ["Int": (64, true), "Int64": (64, true), "Int32": (32, true), "Int16": (16, true), "Int8": (8, true),
  "UInt": (64, false), "UInt64": (64, false), "UInt32": (32, false), "UInt16": (16, false), "UInt8": (8, false)]
func swiftText(_ t: TT) -> String {
  switch t {
  case .n(let n, let a): return a.isEmpty ? n : "\(n)<\(a.map(swiftText).joined(separator: ", "))>"
  case .opt(let x): return "\(swiftText(x))?"
  case .dict(let a, let b): return "[\(swiftText(a)): \(swiftText(b))]"
  case .arr(let x): return "[\(swiftText(x))]"
  case .tup(let xs): return "(\(xs.map(swiftText).joined(separator: ", ")))"
  case .fn: return "() -> Void"
  case .bad(let s): return s
  }
}

// --- the package, indexed ------------------------------------------------------------------------------------------
struct Case { let name: String; var params: [(label: String?, t: TT)]; var raw: J }
final class Ty {
  let name: String; var qual: String; var kind: String; var file: String; var line: Int
  var generic = false; var inherits: [String] = []; var priv = false
  var members: [(file: String, decl: DeclSyntax)] = []
  var cases: [Case] = []
  var rawType: TT?
  var outer: Ty?
  init(name: String, qual: String, kind: String, file: String, line: Int) { self.name = name; self.qual = qual; self.kind = kind; self.file = file; self.line = line }
}
struct SrcFile { let rel: String; let tree: SourceFileSyntax; let conv: SourceLocationConverter }
// A stored property: its name, type, initializer, `let`, where its binding keyword is (the check's copy writes `var`).
struct Prop {
  let name: String; let t: TT; let ttext: String; let initv: ExprSyntax?; let isLet: Bool; let kw: String; let observers: Bool; let priv: Bool
  // (a `var` of an Optional type with no initial value starts nil)
  var nilInit: Bool { initv == nil && !isLet && { if case .opt = t { return true }; return false }() }
  var hasInit: Bool { initv != nil || nilInit }
}
// A method: its key (the request's name), its base name, labels, the declaration.
struct Meth { let key: String; let base: String; let labels: [String]; let decl: DeclSyntax; let file: String; let isStatic: Bool; let priv: Bool }

final class Reader {
  let root: String
  var files: [SrcFile] = []
  var types: [String: [Ty]] = [:]
  var allTypes: [Ty] = []
  var aliases: [String: TT] = [:]
  var consts: [String: (J, TT)] = [:]
  var free: [String: (String, FunctionDeclSyntax)] = [:]
  var recs: [(String, J)] = []
  var recSeen: Set<String> = []
  var funcs: [(String, J)] = []
  var funcSeen: Set<String> = []
  var enumsOut: [(String, J)] = []
  var ctorArity: Int?
  var ctorSig: String?
  // per function
  var file = ""
  var conv: SourceLocationConverter?
  var tmp = 0
  var scopes: [[String: TT]] = []
  var selfTy: Ty?
  var inActor = false
  var retT: TT = .tup([])

  init(root: String) { self.root = root }

  func at(_ n: some SyntaxProtocol) -> String {
    guard let c = conv else { return "\(file):1:1" }
    let l = n.startLocation(converter: c, afterLeadingTrivia: true)
    return "\(file):\(l.line):\(l.column)"
  }
  func end(_ n: some SyntaxProtocol) -> String {
    guard let c = conv else { return "1:1" }
    let l = n.endLocation(converter: c, afterTrailingTrivia: false)
    return "\(l.line):\(l.column)"
  }
  func with<T>(file f: String, _ body: () -> T) -> T {
    let saved = (file, conv)
    file = f; conv = files.first { $0.rel == f }?.conv
    defer { (file, conv) = saved }
    return body()
  }

  // --- the index: every type of the files read (nested ones too), extensions merged, constants, free functions ----
  func load(_ paths: [String]) {
    for p in paths {
      guard let src = try? String(contentsOfFile: p, encoding: .utf8) else { continue }
      let parsed = Parser.parse(source: src)
      let folded = OperatorTable.standardOperators.foldAll(parsed) { _ in }.as(SourceFileSyntax.self) ?? parsed
      let rel = p.hasPrefix(root + "/") ? String(p.dropFirst(root.count + 1)) : p
      files.append(SrcFile(rel: rel, tree: folded, conv: SourceLocationConverter(fileName: rel, tree: folded)))
    }
    for f in files { with(file: f.rel) { for item in f.tree.statements { if case .decl(let d) = item.item { declare(d, outer: nil) } } } }
    for f in files { with(file: f.rel) { for item in f.tree.statements { if case .decl(let d) = item.item { extend(d) } } } }
    for f in files { with(file: f.rel) { for item in f.tree.statements { if case .decl(let d) = item.item { constant(d, owner: nil) } } } }
    for t in allTypes { for (mf, d) in t.members { with(file: mf) { constant(d, owner: t) } } }
  }
  func line(_ n: some SyntaxProtocol) -> Int { conv.map { n.startLocation(converter: $0, afterLeadingTrivia: true).line } ?? 1 }
  func isPrivate(_ mods: DeclModifierListSyntax) -> Bool { mods.contains { ["private", "fileprivate"].contains($0.name.text) } }
  func declare(_ d: DeclSyntax, outer: Ty?) {
    var made: Ty?
    let mk = { (name: String, kind: String, mods: DeclModifierListSyntax, gen: Bool, inh: InheritanceClauseSyntax?, members: MemberBlockSyntax) in
      let t = Ty(name: name, qual: outer.map { "\($0.qual).\(name)" } ?? name, kind: kind, file: self.file, line: self.line(d))
      t.generic = gen; t.outer = outer; t.priv = self.isPrivate(mods)
      t.inherits = inh?.inheritedTypes.map { $0.type.trimmedDescription } ?? []
      for m in members.members { t.members.append((self.file, m.decl)) }
      self.types[name, default: []].append(t); self.allTypes.append(t)
      made = t
    }
    if let c = d.as(ClassDeclSyntax.self) { mk(c.name.text, "class", c.modifiers, c.genericParameterClause != nil, c.inheritanceClause, c.memberBlock) }
    else if let s = d.as(StructDeclSyntax.self) { mk(s.name.text, "struct", s.modifiers, s.genericParameterClause != nil, s.inheritanceClause, s.memberBlock) }
    else if let a = d.as(ActorDeclSyntax.self) { mk(a.name.text, "actor", a.modifiers, a.genericParameterClause != nil, a.inheritanceClause, a.memberBlock) }
    else if let e = d.as(EnumDeclSyntax.self) { mk(e.name.text, "enum", e.modifiers, e.genericParameterClause != nil, e.inheritanceClause, e.memberBlock) }
    else if let p = d.as(ProtocolDeclSyntax.self) { mk(p.name.text, "protocol", p.modifiers, p.primaryAssociatedTypeClause != nil, p.inheritanceClause, p.memberBlock) }
    else if let ta = d.as(TypeAliasDeclSyntax.self) { aliases[ta.name.text] = parseType(ta.initializer.value.trimmedDescription) }
    else if let f = d.as(FunctionDeclSyntax.self), outer == nil { free[f.name.text] = (file, f) }
    guard let t = made else { return }
    for (_, m) in t.members { declare(m, outer: t) }
  }
  func extend(_ d: DeclSyntax) {
    guard let e = d.as(ExtensionDeclSyntax.self) else { return }
    let name = e.extendedType.trimmedDescription.split(separator: ".").last.map(String.init) ?? ""
    guard let t = types[name]?.first, e.genericWhereClause == nil else { return }
    for m in e.memberBlock.members { t.members.append((file, m.decl)); declare(m.decl, outer: t) }
    t.inherits += e.inheritanceClause?.inheritedTypes.map { $0.type.trimmedDescription } ?? []
  }
  // A constant: a `let` (static, or at the file's top) whose value is a literal integer, boolean or string (or a fixed
  // width's max or min, or arithmetic of those).
  func constant(_ d: DeclSyntax, owner: Ty?) {
    if let ec = d.as(EnumCaseDeclSyntax.self), let t = owner, t.kind == "enum" {
      for el in ec.elements {
        let params = el.parameterClause?.parameters.map { (label: $0.firstName?.text, t: parseType($0.type.trimmedDescription)) } ?? []
        var raw: J = .null
        if let rv = el.rawValue?.value { raw = constValue(rv)?.0 ?? .null }
        t.cases.append(Case(name: el.name.text, params: params, raw: raw))
      }
      return
    }
    if let e = d.as(EnumDeclSyntax.self), let t = types[e.name.text]?.first(where: { $0.file == file }) ?? types[e.name.text]?.first {
      if let first = e.inheritanceClause?.inheritedTypes.first { let r = parseType(first.type.trimmedDescription); if case .n(let n, _) = r, INTS[n] != nil || n == "String" { t.rawType = r } }
    }
    guard let vd = d.as(VariableDeclSyntax.self), vd.bindingSpecifier.text == "let" else { return }
    let isStatic = vd.modifiers.contains { $0.name.text == "static" || $0.name.text == "class" }
    if owner != nil && !isStatic { return }
    for b in vd.bindings {
      guard let id = b.pattern.as(IdentifierPatternSyntax.self), let iv = b.initializer?.value, b.accessorBlock == nil else { continue }
      guard var (val, t) = constValue(iv) else { continue }
      if let ann = b.typeAnnotation?.type { t = parseType(ann.trimmedDescription) }
      if case .n(let n, _) = t, let (bits, signed) = INTS[n] { val["ty"] = ["k": "int", "bits": .i(bits), "signed": .b(signed), "sw": .s(n)] }
      consts[owner.map { "\($0.name).\(id.identifier.text)" } ?? id.identifier.text] = (val, t)
    }
  }
  func constValue(_ e: ExprSyntax) -> (J, TT)? {
    if let i = e.as(IntegerLiteralExprSyntax.self), let n = intLit(i.literal.text) { return (X("int", "", [("v", .s(String(n)))]), .n("Int", [])) }
    if let b = e.as(BooleanLiteralExprSyntax.self) { return (X("bool", "", [("v", .b(b.literal.text == "true"))]), .n("Bool", [])) }
    if let s = e.as(StringLiteralExprSyntax.self), s.segments.count == 1, case .stringSegment(let seg) = s.segments.first! { return (X("str", "", [("v", .s(seg.content.text))]), .n("String", [])) }
    if let p = e.as(PrefixOperatorExprSyntax.self), p.operator.text == "-", let (x, t) = constValue(p.expression), let n = Int(x["v"].str ?? "") { return (X("int", "", [("v", .s(String(-n)))]), t) }
    if let m = e.as(MemberAccessExprSyntax.self), let base = m.base?.trimmedDescription, let (bits, signed) = INTS[base] {
      let n = m.declName.baseName.text
      let v: Int? = n == "max" ? (bits == 64 ? (signed ? Int.max : nil) : (signed ? (1 << (bits - 1)) - 1 : (1 << bits) - 1)) : n == "min" ? (signed ? (bits == 64 ? Int.min : -(1 << (bits - 1))) : 0) : nil
      if let v { return (X("int", "", [("v", .s(String(v)))]), .n(base, [])) }
    }
    if let c = e.as(FunctionCallExprSyntax.self), let callee = c.calledExpression.as(DeclReferenceExprSyntax.self), INTS[callee.baseName.text] != nil, c.arguments.count == 1, c.arguments.first!.label == nil, let (x, _) = constValue(c.arguments.first!.expression) { return (x, .n(callee.baseName.text, [])) }
    if let inf = e.as(InfixOperatorExprSyntax.self), let op = inf.operator.as(BinaryOperatorExprSyntax.self)?.operator.text, let (a, ta) = constValue(inf.leftOperand), let (b, _) = constValue(inf.rightOperand), let x = Int(a["v"].str ?? ""), let y = Int(b["v"].str ?? "") {
      let r: Int? = op == "+" ? x &+ y : op == "-" ? x &- y : op == "*" ? x &* y : op == "<<" && y < 62 ? x << y : op == "/" && y != 0 ? x / y : nil
      if let r { return (X("int", "", [("v", .s(String(r)))]), ta) }
    }
    if let t = e.as(TupleExprSyntax.self), t.elements.count == 1 { return constValue(t.elements.first!.expression) }
    if let r = e.as(DeclReferenceExprSyntax.self), let c = consts[r.baseName.text] { return c }
    return nil
  }
  func intLit(_ s: String) -> Int? {
    let t = s.replacingOccurrences(of: "_", with: "")
    if t.hasPrefix("0x") { return Int(t.dropFirst(2), radix: 16) }
    if t.hasPrefix("0b") { return Int(t.dropFirst(2), radix: 2) }
    if t.hasPrefix("0o") { return Int(t.dropFirst(2), radix: 8) }
    return Int(t)
  }
  func ty(named n: String, from: Ty? = nil) -> Ty? {
    let last = n.split(separator: ".").last.map(String.init) ?? n
    guard let cands = types[last], !cands.isEmpty else { return nil }
    if cands.count == 1 { return cands[0] }
    if let q = cands.first(where: { $0.qual == n || $0.qual.hasSuffix(".\(n)") }) { return q }
    var o = from
    while let x = o { if let c = cands.first(where: { $0.outer === x }) { return c }; o = x.outer }
    return cands.first { $0.outer == nil } ?? cands[0]
  }
  func resolve(_ t: TT) -> TT { if case .n(let n, let a) = t, a.isEmpty, let x = aliases[n], x != t { return resolve(x) }; return t }

  // --- the IR's types ---------------------------------------------------------------------------------------------------
  func stype(_ t0: TT) -> J {
    let t = resolve(t0)
    switch t {
    case .opt(let x): return ["k": "opt", "of": stype(x)]
    case .dict(let a, let b): return ["k": "map", "key": stype(a), "val": stype(b)]
    case .arr: return ["k": "opaque", "why": .s("\(swiftText(t)), an Array (lists are outside the Swift subset)")]
    case .tup, .fn, .bad: return ["k": "opaque", "why": .s("\(swiftText(t)), a type outside the subset")]
    case .n(let n, let args):
      if let (bits, signed) = INTS[n] { return ["k": "int", "bits": .i(bits), "signed": .b(signed), "sw": .s(n)] }
      if n == "Bool" { return ["k": "bool"] }
      if n == "String" || n == "Substring" || n == "Character" { return ["k": "str"] }
      if n == "Double" || n == "Float" || n == "CGFloat" || n == "Float80" { return ["k": "opaque", "why": .s("\(n), a float (a binary fraction that rounds; the subset reads integers)")] }
      if n == "Void" { return ["k": "none"] }
      if n == "Self", let s = selfTy { return named(s) }
      if let x = ty(named: n, from: selfTy), args.isEmpty { return named(x) }
      return ["k": "opaque", "why": .s("\(swiftText(t)), a type of other code")]
    }
  }
  func named(_ x: Ty) -> J {
    switch x.kind {
    case "enum":
      if x.cases.contains(where: { !$0.params.isEmpty }) { return ["k": "opaque", "why": .s("\(x.qual), an enum with associated values")] }
      enumOut(x)
      return ["k": "choice", "values": .a(x.cases.map { .s($0.name) }), "discs": .a(discs(x).map { .i($0) }), "enum": .s(x.qual)]
    case "protocol": rec(x); return ["k": "rec", "name": .s(x.qual)]
    default:
      if x.generic { return ["k": "opaque", "why": .s("\(x.qual), a generic type")] }
      rec(x); return ["k": "rec", "name": .s(x.qual)]
    }
  }
  func discs(_ x: Ty) -> [Int] {
    var next = 0
    return x.cases.map { c in
      if case .n(let rn, _)? = x.rawType, INTS[rn] != nil, let r = Int(c.raw["v"].str ?? "") { next = r }
      defer { next += 1 }
      return next
    }
  }
  func enumOut(_ x: Ty) {
    if enumsOut.contains(where: { $0.0 == x.qual }) { return }
    enumsOut.append((x.qual, ["values": .a(x.cases.map { .s($0.name) }), "discs": .a(discs(x).map { .i($0) }), "data": false]))
  }

  // --- a type's members: stored properties, methods (keys unique in the type), computed properties ---------------------
  func props(_ t: Ty) -> [Prop] {
    var out: [Prop] = []
    for (mf, d) in t.members {
      guard let vd = d.as(VariableDeclSyntax.self), !vd.modifiers.contains(where: { ["static", "class"].contains($0.name.text) }) else { continue }
      for b in vd.bindings {
        guard let id = b.pattern.as(IdentifierPatternSyntax.self) else { continue }
        var observers = false
        if let ab = b.accessorBlock {
          guard case .accessors(let acc) = ab.accessors, acc.allSatisfy({ ["willSet", "didSet"].contains($0.accessorSpecifier.text) }) else { continue }
          observers = true
        }
        let tt: TT = b.typeAnnotation.map { parseType($0.type.trimmedDescription) } ?? b.initializer.flatMap { ini in with(file: mf) { literalType(ini.value) } } ?? .bad("no declared type")
        let kw = with(file: mf) { at(vd.bindingSpecifier) }
        out.append(Prop(name: id.identifier.text, t: tt, ttext: b.typeAnnotation?.type.trimmedDescription ?? swiftText(tt), initv: b.initializer?.value, isLet: vd.bindingSpecifier.text == "let", kw: kw, observers: observers, priv: isPrivate(vd.modifiers)))
      }
    }
    return out
  }
  // The type of an initializer the declaration doesn't annotate: a literal's, a fixed width's conversion, a type's
  // member or init (Swift infers no more than this from a property's initializer without its context).
  func literalType(_ e: ExprSyntax) -> TT? {
    if e.is(IntegerLiteralExprSyntax.self) { return .n("Int", []) }
    if e.is(BooleanLiteralExprSyntax.self) { return .n("Bool", []) }
    if e.is(StringLiteralExprSyntax.self) { return .n("String", []) }
    if let c = e.as(FunctionCallExprSyntax.self), let r = c.calledExpression.as(DeclReferenceExprSyntax.self), r.baseName.text.first?.isUppercase == true { return .n(r.baseName.text, []) }
    if let m = e.as(MemberAccessExprSyntax.self), let b = m.base?.trimmedDescription, b.first?.isUppercase == true { if INTS[b] != nil { return .n(b, []) }; if let x = ty(named: b), x.kind == "enum" { return .n(x.qual, []) } }
    if let p = e.as(PrefixOperatorExprSyntax.self), p.operator.text == "-" { return literalType(p.expression) }
    return nil
  }
  func methods(_ t: Ty) -> [Meth] {
    var raw: [(String, [String], DeclSyntax, String, Bool, Bool)] = []
    for (mf, d) in t.members {
      if let f = d.as(FunctionDeclSyntax.self) {
        let labels = f.signature.parameterClause.parameters.map { $0.firstName.text }
        raw.append((f.name.text, labels, d, mf, f.modifiers.contains { ["static", "class"].contains($0.name.text) }, isPrivate(f.modifiers)))
      }
    }
    var out: [Meth] = []
    for (base, labels, d, mf, st, pv) in raw {
      let over = raw.filter { $0.0 == base }.count > 1
      var key = over ? ([base] + labels.map { $0 == "_" ? "" : $0 }).joined(separator: "_") : base
      if st { key = "_static_\(key)" } else if pv { key = "_\(key)" }
      out.append(Meth(key: key, base: base, labels: labels, decl: d, file: mf, isStatic: st, priv: pv))
    }
    return out
  }
  func computed(_ t: Ty) -> [(String, TT, CodeBlockItemListSyntax?, ExprSyntax?, String, Bool)] {
    var out: [(String, TT, CodeBlockItemListSyntax?, ExprSyntax?, String, Bool)] = []
    for (mf, d) in t.members {
      guard let vd = d.as(VariableDeclSyntax.self), !vd.modifiers.contains(where: { $0.name.text == "static" }) else { continue }
      for b in vd.bindings {
        guard let id = b.pattern.as(IdentifierPatternSyntax.self), let ab = b.accessorBlock, let ann = b.typeAnnotation?.type else { continue }
        switch ab.accessors {
        case .getter(let items): out.append((id.identifier.text, parseType(ann.trimmedDescription), items, nil, mf, isPrivate(vd.modifiers)))
        case .accessors(let acc):
          if let g = acc.first(where: { $0.accessorSpecifier.text == "get" }), let body = g.body { out.append((id.identifier.text, parseType(ann.trimmedDescription), body.statements, nil, mf, isPrivate(vd.modifiers))) }
        }
      }
    }
    return out
  }
  func isComputed(_ t: Ty, _ n: String) -> Bool { computed(t).contains { $0.0 == n } }
  func isStored(_ t: Ty, _ n: String) -> Bool { props(t).contains { $0.name == n } }
  func methodKey(_ t: Ty, _ base: String, _ labels: [String]) -> Meth? {
    let ms = methods(t).filter { $0.base == base }
    if ms.count <= 1 { return ms.first }
    return ms.first { $0.labels.map { $0 == "_" ? nil : $0 } == labels.map { $0 == "_" ? nil : $0 } } ?? ms.first { $0.labels.count == labels.count }
  }

  // --- a record: the type read (its fields, its init as __init__, its methods), once -----------------------------------
  func rec(_ t: Ty) {
    if recSeen.contains(t.qual) { return }
    recSeen.insert(t.qual)
    let saved = (selfTy, inActor)
    selfTy = t; inActor = t.kind == "actor"
    defer { (selfTy, inActor) = saved }
    if t.kind == "protocol" {
      // A protocol: its requirements' declared results (an answer's type) and their text (the check's fake conforms).
      var methodsJ: [(String, J)] = [], rets: [(String, J)] = [], reqs: [J] = []
      var assoc = false
      for (mf, d) in t.members {
        if d.is(AssociatedTypeDeclSyntax.self) { assoc = true }
        if let f = d.as(FunctionDeclSyntax.self) {
          let n = f.name.text
          methodsJ.append((n, .null))
          let r = f.signature.returnClause.map { parseType($0.type.trimmedDescription) } ?? .n("Void", [])
          rets.append((n, stype(r)))
          reqs.append(["kind": "func", "name": .s(n), "decl": .s(with(file: mf) { f.with(\.body, nil).with(\.leadingTrivia, []).trimmedDescription }), "ret": .s(swiftText(r)),
            "params": .a(f.signature.parameterClause.parameters.map { ["label": .s($0.firstName.text), "name": .s(($0.secondName ?? $0.firstName).text), "t": .s($0.type.trimmedDescription)] }),
            "throws": .b(f.signature.effectSpecifiers?.trimmedDescription.contains("throws") ?? false), "async": .b(f.signature.effectSpecifiers?.trimmedDescription.contains("async") ?? false),
            "mutating": .b(f.modifiers.contains { $0.name.text == "mutating" }), "static": .b(f.modifiers.contains { $0.name.text == "static" })])
        }
        if let vd = d.as(VariableDeclSyntax.self) {
          for b in vd.bindings { if let id = b.pattern.as(IdentifierPatternSyntax.self), let ann = b.typeAnnotation?.type { reqs.append(["kind": "var", "name": .s(id.identifier.text), "ret": .s(ann.trimmedDescription), "set": .b(b.accessorBlock?.trimmedDescription.contains("set") ?? false)]) } }
        }
      }
      recs.append((t.qual, ["name": .s(t.qual), "short": .s(t.name), "fields": [], "methods": .o(methodsJ), "kinds": ["protocol"], "own": false, "module": "", "p": .s("\(t.file):\(t.line):1"), "rets": .o(rets),
        "swift": ["kind": "protocol", "qual": .s(t.qual), "reqs": .a(reqs), "assoc": .b(assoc), "inherits": .a(t.inherits.map { .s($0) })]]))
      return
    }
    let ps = props(t)
    var fields: [J] = []
    for p in ps {
      var st = stype(p.t)
      if p.observers { st = ["k": "opaque", "why": .s("\(p.name): a property with observers (willSet, didSet)")] }
      fields.append(["name": .s(p.name), "t": st])
    }
    var methodsJ: [(String, J)] = []
    var sigs: [(String, J)] = []
    // The initializer: the one there is, or the one of the arity asked for (ctor); none: the memberwise one (a struct's)
    // or the default one (a class's whose properties all have initial values).
    var inits: [(InitializerDeclSyntax, String)] = []
    for (mf, d) in t.members { if let i = d.as(InitializerDeclSyntax.self), i.optionalMark == nil { inits.append((i, mf)) } }
    let initId = "\(t.qual).__init__"
    var ctorJ: J = .null
    let bare = { (s: String) in s.filter { !$0.isWhitespace } }
    let pick = ctorSig.map { sig in inits.filter { bare($0.0.signature.parameterClause.trimmedDescription) == bare(sig) } } ?? ctorArity.map { n in inits.filter { $0.0.signature.parameterClause.parameters.count == n } } ?? inits
    if inits.isEmpty {
      let mw = ps.filter { !$0.hasInit }
      if t.kind != "struct" && !mw.isEmpty { funcs.append((initId, stub(initId, "__init__", t, "a class with no init whose properties have no initial values"))) }
      else { funcs.append((initId, memberwise(t, ps, mw))) }
      ctorJ = ["labels": .a(t.kind == "struct" ? mw.map { .s($0.name) } : []), "throws": false, "types": .a(t.kind == "struct" ? mw.map { .s(swiftText($0.t)) } : [])]
      methodsJ.append(("__init__", .s(initId)))
    } else if pick.count != 1 {
      funcs.append((initId, stub(initId, "__init__", t, pick.isEmpty ? "no init of the arity or parameters asked for (ctor)" : "a type with \(pick.count) inits (name one by its arity or its parameters: ctor, e.g. \"(limit: Int)\")")))
      methodsJ.append(("__init__", .s(initId)))
    } else {
      let (i, mf) = pick[0]
      funcs.append((initId, with(file: mf) { initFunc(i, t, ps, initId) }))
      methodsJ.append(("__init__", .s(initId)))
      for (o, of) in inits where o != i {
        let labels = o.signature.parameterClause.parameters.map { $0.firstName.text }
        let oid = "\(t.qual).__init__/\(labels.joined(separator: ":"))"
        funcs.append((oid, with(file: of) { initFunc(o, t, ps, oid) }))
        methodsJ.append(("__init__/\(labels.joined(separator: ":"))", .s(oid)))
      }
      ctorJ = ["labels": .a(i.signature.parameterClause.parameters.map { .s($0.firstName.text) }), "throws": .b(i.signature.effectSpecifiers?.trimmedDescription.contains("throws") ?? false),
        "types": .a(i.signature.parameterClause.parameters.map { .s($0.type.trimmedDescription) })]
    }
    for m in methods(t) {
      guard let f = m.decl.as(FunctionDeclSyntax.self) else { continue }
      let fid = "\(t.qual).\(m.key)"
      methodsJ.append((m.key, .s(fid)))
      funcs.append((fid, with(file: m.file) { function(f, t, fid, m.key, m.isStatic) }))
      sigs.append((m.key, ["name": .s(m.base), "labels": .a(m.labels.map { .s($0) }), "static": .b(m.isStatic), "mutating": .b(f.modifiers.contains { $0.name.text == "mutating" }),
        "throws": .b(f.signature.effectSpecifiers?.trimmedDescription.contains("throws") ?? false), "async": .b(f.signature.effectSpecifiers?.trimmedDescription.contains("async") ?? false),
        "types": .a(f.signature.parameterClause.parameters.map { .s($0.type.trimmedDescription) }), "ret": .s(f.signature.returnClause.map { $0.type.trimmedDescription } ?? "Void")]))
    }
    for (n, tt, items, _, mf, _) in computed(t) {
      let fid = "\(t.qual)._get_\(n)"
      methodsJ.append(("_get_\(n)", .s(fid)))
      funcs.append((fid, with(file: mf) { getter(n, tt, items, t, fid) }))
    }
    var kinds: [J] = []
    if t.kind == "struct" { kinds.append("value") }
    if t.generic { kinds.append(.s("generic:\(t.name)")) }
    let own = t.inherits.compactMap { ty(named: $0, from: t) }.filter { $0.kind == "class" }
    var inits0: J = .null
    if !own.isEmpty { inits0 = .s("a subclass of \(own[0].qual) (the subset reads a class with no superclass of the code's own)") }
    recs.append((t.qual, ["name": .s(t.qual), "short": .s(t.name), "fields": .a(fields), "methods": .o(methodsJ), "kinds": .a(kinds), "own": true, "module": "", "p": .s("\(t.file):\(t.line):1"),
      "swift": ["kind": .s(t.kind), "qual": .s(t.qual), "file": .s(t.file), "priv": .b(t.priv), "ctor": ctorJ, "sigs": .o(sigs), "refused": inits0,
        "props": .a(ps.map { ["name": .s($0.name), "t": .s($0.ttext), "let": .b($0.isLet), "kw": .s($0.kw), "init": .b($0.hasInit)] })]]))
    if !inits0.isNull { funcs.removeAll { $0.0 == initId }; funcs.append((initId, stub(initId, "__init__", t, inits0.str!))) }
  }
  func stub(_ id: String, _ name: String, _ t: Ty, _ why: String) -> J {
    let p = "\(t.file):\(t.line):1"
    return ["id": .s(id), "name": .s(name), "cls": .s(t.qual), "p": .s(p), "span": [.s(t.file), .i(t.line), .i(t.line)], "params": [["name": "self", "t": ["k": "any"], "self": true]], "ret": ["k": "none"], "body": [sno(p, why)], "decorators": []]
  }
  // The properties' initial values, in their order (what every init of the type runs first).
  func propInits(_ t: Ty, _ ps: [Prop]) -> [J] {
    var out: [J] = []
    for p in ps {
      if p.nilInit { let at0 = "\(t.file):\(t.line):1"; out.append(S("set", at0, [("to", X("get", at0, [("x", v("self", at0)), ("f", .s(p.name)), ("text", .s("self.\(p.name)"))])), ("x", X("none", at0))])); continue }
      guard let iv = p.initv else { continue }
      let mf = t.members.first { m in m.decl.as(VariableDeclSyntax.self)?.bindings.contains { $0.pattern.as(IdentifierPatternSyntax.self)?.identifier.text == p.name } ?? false }?.file ?? t.file
      with(file: mf) {
        let (pre, x) = expr(iv, expect: p.t)
        out += pre
        out.append(S("set", at(iv), [("to", X("get", at(iv), [("x", v("self", at(iv))), ("f", .s(p.name)), ("text", .s("self.\(p.name)"))])), ("x", x)]))
      }
    }
    return out
  }
  func memberwise(_ t: Ty, _ ps: [Prop], _ mw: [Prop]) -> J {
    let p = "\(t.file):\(t.line):1"
    let saved = scopes
    defer { scopes = saved }
    scopes = [Dictionary(uniqueKeysWithValues: mw.map { ($0.name, $0.t) })]
    var body = with(file: t.file) { propInits(t, ps) }
    for m in mw { body.append(S("set", p, [("to", X("get", p, [("x", v("self", p)), ("f", .s(m.name)), ("text", .s("self.\(m.name)"))])), ("x", v(m.name, p))])) }
    return ["id": .s("\(t.qual).__init__"), "name": "__init__", "cls": .s(t.qual), "p": .s(p), "span": [.s(t.file), .i(t.line), .i(t.line)],
      "params": .a([["name": "self", "t": ["k": "any"], "self": true]] + mw.map { ["name": .s($0.name), "t": stype($0.t)] }), "ret": ["k": "none"], "body": .a(body), "decorators": []]
  }
  func params(_ ps: FunctionParameterListSyntax) -> ([J], [String: TT], J?) {
    var out: [J] = [["name": "self", "t": ["k": "any"], "self": true]]
    var names: [String: TT] = [:]
    for (i, pa) in ps.enumerated() {
      let n = (pa.secondName ?? pa.firstName).text == "_" ? "_arg\(i)" : (pa.secondName ?? pa.firstName).text
      let tt = parseType(pa.type.trimmedDescription)
      names[n] = tt
      if pa.type.trimmedDescription.hasPrefix("inout ") { return (out, names, sno(at(pa), "\(pa.trimmedDescription): an inout parameter")) }
      if pa.ellipsis != nil { return (out, names, sno(at(pa), "\(pa.trimmedDescription): a variadic parameter")) }
      var j: J = ["name": .s(n), "t": stype(tt)]
      if let dv = pa.defaultValue?.value { let (pre, x) = expr(dv, expect: tt); if pre.isEmpty { j["dflt"] = x } }
      out.append(j)
    }
    return (out, names, nil)
  }
  func initFunc(_ i: InitializerDeclSyntax, _ t: Ty, _ ps: [Prop], _ id: String) -> J {
    tmp = 0
    scopes = []
    let (pj, names, bad) = params(i.signature.parameterClause.parameters)
    scopes = [names]
    let delegates = i.body.map { b in b.statements.contains { $0.trimmedDescription.hasPrefix("self.init(") } } ?? false
    var body: [J] = delegates ? [] : propInits(t, ps)
    if let bad { body.append(bad) }
    if let b = i.body { body += block(b.statements) } else { body.append(sno(at(i), "an init with no body")) }
    let p = at(i)
    return ["id": .s(id), "name": "__init__", "cls": .s(t.qual), "p": .s(p), "span": [.s(file), .i(line(i)), .i(i.body.map { b in conv.map { c in b.endLocation(converter: c).line } ?? 1 } ?? 1)],
      "params": .a(pj), "ret": ["k": "none"], "body": .a(body), "decorators": []]
  }
  func function(_ f: FunctionDeclSyntax, _ t: Ty?, _ id: String, _ key: String, _ isStatic: Bool) -> J {
    tmp = 0
    let (pj0, names, bad) = params(f.signature.parameterClause.parameters)
    var pj = pj0
    if isStatic || t == nil { pj.removeFirst() }
    scopes = [names]
    retT = f.signature.returnClause.map { parseType($0.type.trimmedDescription) } ?? .tup([])
    var body: [J] = []
    if let bad { body.append(bad) }
    if f.genericParameterClause != nil { body.append(sno(at(f), "\(f.name.text): a generic function")) }
    if let b = f.body { body += block(b.statements) } else { body.append(sno(at(f), "\(f.name.text): no body")) }
    let effects = f.signature.effectSpecifiers?.trimmedDescription ?? ""
    let ret: J = f.signature.returnClause.map { stype(parseType($0.type.trimmedDescription)) } ?? ["k": "none"]
    let endLine = f.body.map { b in conv.map { b.endLocation(converter: $0).line } ?? 1 } ?? line(f)
    return ["id": .s(id), "name": .s(key), "cls": t.map { .s($0.qual) } ?? .null, "p": .s(at(f.name)), "span": [.s(file), .i(line(f)), .i(endLine)], "params": .a(pj), "ret": ret, "body": .a(body),
      "async": .b(effects.contains("async")), "static": .b(isStatic || t == nil), "decorators": [], "generic": .b(f.genericParameterClause != nil)]
  }
  func getter(_ n: String, _ tt: TT, _ items: CodeBlockItemListSyntax?, _ t: Ty, _ id: String) -> J {
    tmp = 0
    scopes = [[:]]
    retT = tt
    var body: [J] = []
    if let items {
      // (a single expression is the getter's result)
      if items.count == 1, case .expr(let e) = items.first!.item, !e.is(IfExprSyntax.self), !e.is(SwitchExprSyntax.self) { let (pre, x) = expr(e, expect: tt); body = pre + [S("ret", at(e), [("x", x)])] }
      else { body = block(items) }
    }
    let p = "\(t.file):\(t.line):1"
    return ["id": .s(id), "name": .s("_get_\(n)"), "cls": .s(t.qual), "p": .s(p), "span": [.s(file), .i(t.line), .i(t.line)], "params": [["name": "self", "t": ["k": "any"], "self": true]], "ret": stype(tt), "body": .a(body), "decorators": []]
  }

  // --- locals ----------------------------------------------------------------------------------------------------------
  func local(_ n: String) -> TT?? { for s in scopes.reversed() { if let t = s[n] { return .some(t) } }; return nil }
  func bind(_ n: String, _ t: TT?) { if scopes.isEmpty { scopes = [[:]] }; scopes[scopes.count - 1][n] = t ?? .bad("unknown") }
  func temp() -> String { tmp += 1; let n = "$t\(tmp)"; bind(n, nil); return n }
  func scoped<T>(_ body: () -> T) -> T { scopes.append([:]); defer { scopes.removeLast() }; return body() }

  // --- statements ------------------------------------------------------------------------------------------------------
  func block(_ items: CodeBlockItemListSyntax) -> [J] {
    var out: [J] = []
    for it in items {
      switch it.item {
      case .decl(let d): out += decl(d)
      case .stmt(let s): out += stmt(s)
      case .expr(let e): out += exprStmt(e)
      }
    }
    return out
  }
  func decl(_ d: DeclSyntax) -> [J] {
    let p = at(d)
    guard let vd = d.as(VariableDeclSyntax.self) else { return [sno(p, "\(short(d.trimmedDescription)): a declaration in a function")] }
    var out: [J] = []
    for b in vd.bindings {
      let ann = b.typeAnnotation.map { parseType($0.type.trimmedDescription) }
      if b.accessorBlock != nil { out.append(sno(p, "a computed local")); continue }
      if let id = b.pattern.as(IdentifierPatternSyntax.self) {
        let n = id.identifier.text
        guard let iv = b.initializer?.value else { bind(n, ann); continue }
        let (pre, x0) = expr(iv, expect: ann)
        out += pre
        bind(n, ann ?? typeOf(iv))
        out.append(S("set", p, [("to", v(n, p)), ("x", copied(x0, iv))]))
      } else if let tp = b.pattern.as(TuplePatternSyntax.self), let iv = b.initializer?.value {
        let (pre, x0) = expr(iv, expect: nil)
        out += pre
        var xs: [J] = []
        for el in tp.elements {
          if let id = el.pattern.as(IdentifierPatternSyntax.self) { bind(id.identifier.text, nil); xs.append(v(id.identifier.text, p)) } else { xs.append(v("_", p)) }
        }
        out.append(S("set", p, [("to", X("tuple", p, [("xs", .a(xs))])), ("x", x0)]))
      } else if b.pattern.is(WildcardPatternSyntax.self), let iv = b.initializer?.value { let (pre, x) = expr(iv, expect: nil); out += pre + [S("expr", p, [("x", x)])] }
      else { out.append(sno(p, "\(short(b.trimmedDescription)): a pattern outside the subset")) }
    }
    return out
  }
  // A value read by value: a struct copied (Swift's value semantics), never one of a class (a reference).
  func copied(_ x: J, _ e: ExprSyntax) -> J {
    guard isPlace(x) else { return x }
    if case .n(let n, _)? = typeOf(e), let t = ty(named: n, from: selfTy), t.kind != "struct" { return x }
    return X("copy", x["p"].str ?? "", [("x", x)])
  }
  func stmt(_ s: StmtSyntax) -> [J] {
    let p = at(s)
    if let r = s.as(ReturnStmtSyntax.self) {
      guard let e = r.expression else { return [S("ret", p)] }
      let (pre, x) = expr(e, expect: retT)
      return pre + [S("ret", p, [("x", copied(x, e))])]
    }
    if let t = s.as(ThrowStmtSyntax.self) { return [S("fail", p, [("why", .s("throw \(short(t.expression.trimmedDescription))"))])] }
    if let g = s.as(GuardStmtSyntax.self) { return guardStmt(g) }
    if let e = s.as(ExpressionStmtSyntax.self) { return exprStmt(e.expression) }
    if s.is(BreakStmtSyntax.self) { return [S("break", p)] }
    if s.is(ForStmtSyntax.self) || s.is(WhileStmtSyntax.self) || s.is(RepeatStmtSyntax.self) { return [sno(p, "a loop")] }
    if s.is(DeferStmtSyntax.self) { return [sno(p, "defer")] }
    if s.is(DoStmtSyntax.self) { return [sno(p, "do ... catch")] }
    if s.is(FallThroughStmtSyntax.self) { return [sno(p, "fallthrough")] }
    if s.is(ContinueStmtSyntax.self) { return [sno(p, "continue")] }
    return [sno(p, "\(short(s.trimmedDescription)): a statement outside the subset")]
  }
  func exprStmt(_ e: ExprSyntax) -> [J] {
    let p = at(e)
    if let i = e.as(IfExprSyntax.self) { return ifStmt(i, into: nil) }
    if let sw = e.as(SwitchExprSyntax.self) { return switchStmt(sw, into: nil) }
    if let inf = e.as(InfixOperatorExprSyntax.self) {
      if inf.operator.is(AssignmentExprSyntax.self) { return assign(inf.leftOperand, inf.rightOperand, p) }
      if let op = inf.operator.as(BinaryOperatorExprSyntax.self)?.operator.text, ["+=", "-=", "*=", "/=", "%=", "&+=", "&-=", "&*="].contains(op) { return compound(inf.leftOperand, String(op.dropLast()), inf.rightOperand, p, e) }
    }
    if let t = e.as(TryExprSyntax.self), t.questionOrExclamationMark?.text != "?" { return exprStmt(t.expression) }
    let (pre, x) = expr(e, expect: nil)
    if ["unit", "none"].contains(x["e"].str ?? "") { return pre }
    return pre + [S("expr", p, [("x", x)])]
  }
  func target(_ l: ExprSyntax) -> ([J], J) {
    let p = at(l)
    if l.is(DiscardAssignmentExprSyntax.self) { return ([], v("_", p)) }
    if let r = l.as(DeclReferenceExprSyntax.self) {
      let n = r.baseName.text
      if local(n) != nil { return ([], v(n, p)) }
      if let st = selfTy, isStored(st, n) { return ([], X("get", p, [("x", v("self", p)), ("f", .s(n)), ("text", .s(n))])) }
      return ([], no(p, "\(n): an assignment to other than a local or a stored property"))
    }
    if let m = l.as(MemberAccessExprSyntax.self), let base = m.base {
      let (pre, b) = expr(base, expect: nil)
      if let bt = typeOf(base), case .n(let bn, _) = bt, let t = ty(named: bn, from: selfTy), isComputed(t, m.declName.baseName.text) { return (pre, no(p, "\(m.trimmedDescription): a computed property set")) }
      return (pre, X("get", p, [("x", b), ("f", .s(m.declName.baseName.text)), ("text", .s(short(m.trimmedDescription)))]))
    }
    if let sc = l.as(SubscriptCallExprSyntax.self), sc.arguments.count == 1, sc.arguments.first!.label == nil {
      let (pre, b) = expr(sc.calledExpression, expect: nil)
      let kt: TT? = { if case .dict(let k, _)? = typeOf(sc.calledExpression) { return k }; return nil }()
      let (kp, k) = expr(sc.arguments.first!.expression, expect: kt)
      return (pre + kp, X("idx", p, [("x", b), ("i", k), ("text", .s(short(l.trimmedDescription)))]))
    }
    return ([], no(p, "\(short(l.trimmedDescription)): an assignment the subset doesn't read"))
  }
  func assign(_ l: ExprSyntax, _ r: ExprSyntax, _ p: String) -> [J] {
    if l.is(DiscardAssignmentExprSyntax.self) { let (pre, x) = expr(r, expect: nil); return pre + [S("expr", p, [("x", x)])] }
    if let t = l.as(TupleExprSyntax.self), t.elements.count > 1 { return [sno(p, "a tuple assigned")] }
    let (tp, to) = target(l)
    if to["e"].str == "no" { return tp + [S("expr", p, [("x", to)])] }
    if to["e"].str == "idx" {
      if r.is(NilLiteralExprSyntax.self) { return tp + [S("del", p, [("x", to)])] }
      if case .opt? = typeOf(r) { return tp + [sno(p, "\(short(r.trimmedDescription)): an Optional set at a key (it sets or removes)")] }
    }
    let (rp, x) = expr(r, expect: typeOf(l))
    return rp + tp + [S("set", p, [("to", to), ("x", copied(x, r))])]
  }
  func compound(_ l: ExprSyntax, _ op: String, _ r: ExprSyntax, _ p: String, _ e: ExprSyntax) -> [J] {
    // d[k, default: v] op= y: the key's value (or v) op y, set at the key
    if let sc = l.as(SubscriptCallExprSyntax.self), sc.arguments.count == 2, sc.arguments.last!.label?.text == "default" {
      let (pre, d) = expr(sc.calledExpression, expect: nil)
      let (kp, k) = expr(sc.arguments.first!.expression, expect: nil)
      let (dp, dv) = expr(sc.arguments.last!.expression, expect: nil)
      let (rp, y) = expr(r, expect: nil)
      let cur = X("call", p, [("f", X("get", p, [("x", d), ("f", "get"), ("text", .s(short(sc.calledExpression.trimmedDescription)))])), ("args", [k, dv]), ("kw", []), ("text", .s(short(l.trimmedDescription)))])
      return pre + kp + dp + rp + [S("set", p, [("to", X("idx", p, [("x", d), ("i", k), ("text", .s(short(l.trimmedDescription)))])), ("x", arith(op, cur, y, p, e.trimmedDescription))])]
    }
    let (tp, to) = target(l)
    if to["e"].str == "no" { return tp + [S("expr", p, [("x", to)])] }
    let (rp, y) = expr(r, expect: typeOf(l))
    return rp + tp + [S("set", p, [("to", to), ("x", arith(op, to, y, p, e.trimmedDescription))])]
  }
  func arith(_ op: String, _ a: J, _ b: J, _ p: String, _ text: String) -> J {
    let wrap = op.hasPrefix("&")
    let o = wrap ? String(op.dropFirst()) : op
    return X("bin", p, [("op", .s(o)), ("x", a), ("y", b), ("ovf", .s(wrap ? "wrap" : "trap")), ("div", "trunc"), ("text", .s(short(text))), ("trap", .s("a crash: \(o == "/" || o == "%" ? "division by zero or overflow" : "arithmetic overflow")")), ("crash", wrap ? .null : true)])
  }
  // A condition list (`if c, let x = o, case .a = e`): each one's test, with the bindings it makes visible to the next.
  enum Cond { case test(J), bind(String, J, TT?), pat(J, [J]) }
  func conds(_ cl: ConditionElementListSyntax) -> ([J], [Cond]) {
    var pre: [J] = [], out: [Cond] = []
    for c in cl {
      let p = at(c)
      switch c.condition {
      case .expression(let e):
        let (ep, x) = expr(e, expect: .n("Bool", []))
        if !ep.isEmpty && !out.isEmpty { out.append(.test(no(p, "a condition with statements after a binding"))); continue }
        pre += ep; out.append(.test(x))
      case .optionalBinding(let ob):
        guard let id = ob.pattern.as(IdentifierPatternSyntax.self) else { out.append(.test(no(p, "an optional binding's pattern"))); continue }
        let n = id.identifier.text
        let src: ExprSyntax = ob.initializer?.value ?? ExprSyntax(DeclReferenceExprSyntax(baseName: .identifier(n)))
        let (ep, x) = ob.initializer == nil ? ([], local(n) != nil ? v(n, p) : expr(src, expect: nil).1) : expr(src, expect: nil)
        if !ep.isEmpty && !out.isEmpty { out.append(.test(no(p, "a binding with statements after another"))); continue }
        pre += ep
        var inner: TT? = nil
        if case .opt(let i)? = (ob.initializer == nil ? (local(n) ?? nil) : typeOf(src)) { inner = i }
        let t = temp()
        pre.append(S("set", p, [("to", v(t, p)), ("x", x)]))
        out.append(.bind(n, v(t, p), inner))
      case .matchingPattern(let mp):
        let (ep, x) = expr(mp.initializer.value, expect: nil)
        if !ep.isEmpty && !out.isEmpty { out.append(.test(no(p, "a pattern with statements after a binding"))); continue }
        pre += ep
        let t = temp()
        pre.append(S("set", p, [("to", v(t, p)), ("x", x)]))
        let (test, binds) = pattern(mp.pattern, v(t, p), typeOf(mp.initializer.value), p)
        out.append(.pat(test, binds))
      default: out.append(.test(no(p, "\(short(c.trimmedDescription)): an availability condition")))
      }
    }
    return (pre, out)
  }
  func nest(_ cs: [Cond], _ i: Int, _ then: () -> [J], _ els: [J], _ p: String) -> [J] {
    if i == cs.count { return then() }
    switch cs[i] {
    case .test(let c): return [S("if", p, [("c", c), ("then", .a(nest(cs, i + 1, then, els, p))), ("else", .a(els))])]
    case .bind(let n, let src, let t):
      bind(n, t)
      return [S("if", p, [("c", X("is", p, [("x", src), ("k", "some")])), ("then", .a([S("set", p, [("to", v(n, p)), ("x", X("unwrap", p, [("x", src), ("k", "some")]))])] + nest(cs, i + 1, then, els, p))), ("else", .a(els))])]
    case .pat(let test, let binds): return [S("if", p, [("c", test), ("then", .a(binds + nest(cs, i + 1, then, els, p))), ("else", .a(els))])]
    }
  }
  // An if (a statement, or a value set into `into`): its conditions nested, the else lowered once and shared.
  func ifStmt(_ i: IfExprSyntax, into: String?) -> [J] {
    let p = at(i)
    var els: [J] = []
    switch i.elseBody {
    case .ifExpr(let e)?: els = scoped { ifStmt(e, into: into) }
    case .codeBlock(let b)?: els = scoped { valued(b.statements, into) }
    case nil: els = []
    }
    return scoped {
      let (pre, cs) = conds(i.conditions)
      return pre + nest(cs, 0, { valued(i.body.statements, into) }, els, p)
    }
  }
  // A block whose last expression is the value (an if or switch used as an expression).
  func valued(_ items: CodeBlockItemListSyntax, _ into: String?) -> [J] {
    guard let into, let last = items.last, case .expr(let e) = last.item else { return block(items) }
    let rest = block(CodeBlockItemListSyntax(items.dropLast()))
    if let ie = e.as(IfExprSyntax.self) { return rest + ifStmt(ie, into: into) }
    if let se = e.as(SwitchExprSyntax.self) { return rest + switchStmt(se, into: into) }
    let (pre, x) = expr(e, expect: nil)
    return rest + pre + [S("set", at(e), [("to", v(into, at(e))), ("x", x)])]
  }
  func guardStmt(_ g: GuardStmtSyntax) -> [J] {
    let p = at(g)
    let els = scoped { block(g.body.statements) }
    let (pre, cs) = conds(g.conditions)
    var out = pre
    for c in cs {
      switch c {
      case .test(let x): out.append(S("if", p, [("c", x), ("then", []), ("else", .a(els))]))
      case .bind(let n, let src, let t):
        out.append(S("if", p, [("c", X("is", p, [("x", src), ("k", "none")])), ("then", .a(els)), ("else", [])]))
        bind(n, t)
        out.append(S("set", p, [("to", v(n, p)), ("x", X("unwrap", p, [("x", src), ("k", "some")]))]))
      case .pat(let test, let binds): out.append(S("if", p, [("c", test), ("then", []), ("else", .a(els))])); out += binds
      }
    }
    return out
  }
  // A switch: its cases a chain of ifs in order (the last a failure: Swift's switch is exhaustive, so it is unreachable
  // for the code's own values), inside a block a `break` leaves.
  func switchStmt(_ sw: SwitchExprSyntax, into: String?) -> [J] {
    let p = at(sw)
    let (pre, x) = expr(sw.subject, expect: nil)
    let st = typeOf(sw.subject)
    let t = temp()
    var out = pre + [S("set", p, [("to", v(t, p)), ("x", x)])]
    var chain: [J] = [S("fail", p, [("why", "a switch no case takes (unreachable for the code's own values)")])]
    for c in sw.cases.reversed() {
      guard case .switchCase(let sc) = c else { return out + [sno(at(c), "#if in a switch")] }
      let cp = at(sc)
      let r: [J] = scoped {
        switch sc.label {
        case .default: return valued(sc.statements, into)
        case .case(let lab):
          var tests: [J] = []
          var binds: [J] = []
          var guardX: J? = nil
          for item in lab.caseItems {
            let (tt, bs) = pattern(item.pattern, v(t, cp), st, cp)
            if !bs.isEmpty && lab.caseItems.count > 1 { return [sno(cp, "a case of several patterns that bind")] }
            binds += bs; tests.append(tt)
            if let w = item.whereClause {
              if lab.caseItems.count > 1 { return [sno(cp, "a where clause in a case of several patterns")] }
              let (wp, wx) = expr(w.condition, expect: .n("Bool", []))
              if !wp.isEmpty { return [sno(cp, "a where clause with statements")] }
              guardX = wx
            }
          }
          let body = valued(sc.statements, into)
          let test = tests.count == 1 ? tests[0] : X("or", cp, [("xs", .a(tests)), ("strict", true)])
          if let gx = guardX { return [S("if", cp, [("c", test), ("then", .a(binds + [S("if", cp, [("c", gx), ("then", .a(body)), ("else", .a(chain))])])), ("else", .a(chain))])] }
          if test["e"].str == "bool", case .b(true) = test["v"] { return binds + body }
          return [S("if", cp, [("c", test), ("then", .a(binds + body)), ("else", .a(chain))])]
        }
      }
      chain = r
    }
    out.append(S("switch", p, [("cases", [["default": true, "b": .a(chain), "p": .s(p)]])]))
    return out
  }
  // A pattern against a value: its test, and the bindings it makes (set where it holds).
  func pattern(_ pat: PatternSyntax, _ val: J, _ vt: TT?, _ p: String, binding: Bool = false) -> (J, [J]) {
    let yes = X("bool", p, [("v", true)])
    if pat.is(WildcardPatternSyntax.self) { return (yes, []) }
    if let vb = pat.as(ValueBindingPatternSyntax.self) { return pattern(vb.pattern, val, vt, p, binding: true) }
    if let id = pat.as(IdentifierPatternSyntax.self) { bind(id.identifier.text, vt); return (yes, [S("set", p, [("to", v(id.identifier.text, p)), ("x", val)])]) }
    if let ep = pat.as(ExpressionPatternSyntax.self) { return exprPattern(ep.expression, val, vt, p, binding: binding) }
    return (no(p, "\(short(pat.trimmedDescription)): a pattern outside the subset"), [])
  }
  func exprPattern(_ e: ExprSyntax, _ val: J, _ vt: TT?, _ p: String, binding: Bool) -> (J, [J]) {
    let yes = X("bool", p, [("v", true)])
    if e.is(DiscardAssignmentExprSyntax.self) { return (yes, []) }
    if let pe = e.as(PatternExprSyntax.self) { return pattern(pe.pattern, val, vt, p, binding: binding) }
    if binding, let r = e.as(DeclReferenceExprSyntax.self) { bind(r.baseName.text, vt); return (yes, [S("set", p, [("to", v(r.baseName.text, p)), ("x", val)])]) }
    if e.is(NilLiteralExprSyntax.self) { return (X("is", p, [("x", val), ("k", "none")]), []) }
    if let oc = e.as(OptionalChainingExprSyntax.self) {
      var inner: TT? = nil
      if case .opt(let i)? = vt { inner = i }
      let (t, b) = exprPattern(oc.expression, X("unwrap", p, [("x", val), ("k", "some")]), inner, p, binding: binding)
      return (X("and", p, [("xs", [X("is", p, [("x", val), ("k", "some")]), t]), ("strict", true)]), b)
    }
    // .some(p) / .none on an Optional
    if case .opt(let inner)? = vt {
      if let m = e.as(MemberAccessExprSyntax.self), m.base == nil, m.declName.baseName.text == "none" { return (X("is", p, [("x", val), ("k", "none")]), []) }
      if let c = e.as(FunctionCallExprSyntax.self), let m = c.calledExpression.as(MemberAccessExprSyntax.self), m.base == nil, m.declName.baseName.text == "some", c.arguments.count == 1 {
        let (t, b) = exprPattern(c.arguments.first!.expression, X("unwrap", p, [("x", val), ("k", "some")]), inner, p, binding: binding)
        return (X("and", p, [("xs", [X("is", p, [("x", val), ("k", "some")]), t]), ("strict", true)]), b)
      }
    }
    if let c = e.as(FunctionCallExprSyntax.self), c.calledExpression.as(MemberAccessExprSyntax.self) != nil { return (no(p, "\(short(e.trimmedDescription)): a case with associated values (an enum with data)"), []) }
    // a range: lo...hi, lo..<hi
    if let inf = e.as(InfixOperatorExprSyntax.self), let op = inf.operator.as(BinaryOperatorExprSyntax.self)?.operator.text, op == "..." || op == "..<" {
      let (_, lo) = expr(inf.leftOperand, expect: vt), (_, hi) = expr(inf.rightOperand, expect: vt)
      return (X("and", p, [("xs", [X("cmp", p, [("op", "<="), ("x", lo), ("y", val)]), X("cmp", p, [("op", .s(op == "..." ? "<=" : "<")), ("x", val), ("y", hi)])]), ("strict", true)]), [])
    }
    let (pre, x) = expr(e, expect: vt)
    if !pre.isEmpty { return (no(p, "\(short(e.trimmedDescription)): a pattern with statements"), []) }
    return (X("cmp", p, [("op", "=="), ("x", val), ("y", x), ("text", .s(short(e.trimmedDescription)))]), [])
  }

  // --- expressions: (statements before, the value) ------------------------------------------------------------------
  func expr(_ e: ExprSyntax, expect: TT?) -> ([J], J) {
    let p = at(e)
    let t = short(e.trimmedDescription)
    if let i = e.as(IntegerLiteralExprSyntax.self) {
      guard let n = intLit(i.literal.text) else { return ([], no(p, "\(t): an integer literal past Int")) }
      var x = X("int", p, [("v", .s(String(n)))])
      if case .n(let en, _)? = expect.map(resolve), INTS[en] != nil { x["ty"] = stype(.n(en, [])) }
      if case .opt(.n(let en, _))? = expect.map(resolve), INTS[en] != nil { x["ty"] = stype(.n(en, [])) }
      return ([], x)
    }
    if let b = e.as(BooleanLiteralExprSyntax.self) { return ([], X("bool", p, [("v", .b(b.literal.text == "true"))])) }
    if e.is(NilLiteralExprSyntax.self) { return ([], X("none", p)) }
    if e.is(FloatLiteralExprSyntax.self) { return ([], no(p, "\(t): a float literal")) }
    if let s = e.as(StringLiteralExprSyntax.self) { return stringLit(s, p, t) }
    if let tu = e.as(TupleExprSyntax.self) {
      if tu.elements.count == 1 { return expr(tu.elements.first!.expression, expect: expect) }
      var pre: [J] = [], xs: [J] = []
      for el in tu.elements { let (a, x) = expr(el.expression, expect: nil); pre += a; xs.append(x) }
      return (pre, X("tuple", p, [("xs", .a(xs))]))
    }
    if let r = e.as(DeclReferenceExprSyntax.self) { return ([], name(r.baseName.text, p, t, expect)) }
    if e.is(SuperExprSyntax.self) { return ([], no(p, "super")) }
    if let m = e.as(MemberAccessExprSyntax.self) { return member(m, p, t, expect) }
    if let c = e.as(FunctionCallExprSyntax.self) {
      if c.trailingClosure != nil || c.arguments.contains(where: { $0.expression.is(ClosureExprSyntax.self) }) { return ([], no(p, "\(t): a closure")) }
      var (pre, x) = call(c, p, t, expect)
      if x["e"].str == "call" { x["end"] = .s(end(c)) }
      return (pre, x)
    }
    if let sc = e.as(SubscriptCallExprSyntax.self) {
      let (pre, b) = expr(sc.calledExpression, expect: nil)
      let kt: TT? = { if case .dict(let k, _)? = typeOf(sc.calledExpression) { return k }; return nil }()
      let vt: TT? = { if case .dict(_, let v)? = typeOf(sc.calledExpression) { return v }; return nil }()
      if sc.arguments.count == 1, sc.arguments.first!.label == nil {
        let (kp, k) = expr(sc.arguments.first!.expression, expect: kt)
        return (pre + kp, X("call", p, [("f", X("get", p, [("x", b), ("f", "get"), ("text", .s(short(sc.calledExpression.trimmedDescription)))])), ("args", [k]), ("kw", []), ("text", .s(t))]))
      }
      if sc.arguments.count == 2, sc.arguments.last!.label?.text == "default" {
        let (kp, k) = expr(sc.arguments.first!.expression, expect: kt), (dp, d) = expr(sc.arguments.last!.expression, expect: vt)
        return (pre + kp + dp, X("call", p, [("f", X("get", p, [("x", b), ("f", "get"), ("text", .s(short(sc.calledExpression.trimmedDescription)))])), ("args", [k, d]), ("kw", []), ("text", .s(t))]))
      }
      return (pre, no(p, "\(t): a subscript outside the subset (a dictionary's [key] and [key, default:])"))
    }
    if let inf = e.as(InfixOperatorExprSyntax.self) { return infix(inf, p, t, expect) }
    if let pr = e.as(PrefixOperatorExprSyntax.self) {
      let op = pr.operator.text
      if op == "!" { let (pre, x) = expr(pr.expression, expect: .n("Bool", [])); return (pre, X("not", p, [("x", x), ("strict", true), ("text", .s(t))])) }
      if op == "-" {
        if let i = pr.expression.as(IntegerLiteralExprSyntax.self), let n = intLit(i.literal.text) { var x = X("int", p, [("v", .s(String(-n)))]); if case .n(let en, _)? = expect, INTS[en] != nil { x["ty"] = stype(.n(en, [])) }; return ([], x) }
        let (pre, x) = expr(pr.expression, expect: expect)
        return (pre, arith("-", X("int", p, [("v", "0")]), x, p, t))
      }
      if op == "+" { return expr(pr.expression, expect: expect) }
      return ([], no(p, "\(t): the operator \(op)"))
    }
    if let fu = e.as(ForceUnwrapExprSyntax.self) { let (pre, x) = expr(fu.expression, expect: expect.map { .opt($0) }); return (pre, X("expect", p, [("x", x), ("text", .s("\(t) (a crash: nil force-unwrapped)")), ("crash", true)])) }
    if let tr = e.as(TryExprSyntax.self) {
      if tr.questionOrExclamationMark?.text == "?" { return ([], no(p, "\(t): try? (an error made nil)")) }
      return expr(tr.expression, expect: expect)
    }
    if e.is(AwaitExprSyntax.self) { return ([], no(p, "\(t): an await (a suspension point, where other calls may interleave)")) }
    if let te = e.as(TernaryExprSyntax.self) {
      let (cp, c) = expr(te.condition, expect: .n("Bool", []))
      let (ap, a) = expr(te.thenExpression, expect: expect), (bp, b) = expr(te.elseExpression, expect: expect)
      if ap.isEmpty && bp.isEmpty { return (cp, X("ite", p, [("c", c), ("a", a), ("b", b), ("text", .s(t))])) }
      let r = temp()
      return (cp + [S("if", p, [("c", c), ("then", .a(ap + [S("set", p, [("to", v(r, p)), ("x", a)])])), ("else", .a(bp + [S("set", p, [("to", v(r, p)), ("x", b)])]))])], v(r, p))
    }
    if let ie = e.as(IfExprSyntax.self) { let r = temp(); return (ifStmt(ie, into: r), v(r, p)) }
    if let se = e.as(SwitchExprSyntax.self) { let r = temp(); return (switchStmt(se, into: r), v(r, p)) }
    if let d = e.as(DictionaryExprSyntax.self) {
      if case .colon = d.content { return ([], X("dict", p, [("keys", []), ("vals", []), ("text", .s(t))])) }
      return ([], no(p, "\(t): a dictionary literal with items"))
    }
    if e.is(ArrayExprSyntax.self) { return ([], no(p, "\(t): an array")) }
    if e.is(ClosureExprSyntax.self) { return ([], no(p, "\(t): a closure")) }
    if e.is(IsExprSyntax.self) || e.is(AsExprSyntax.self) { return ([], no(p, "\(t): a dynamic type test or cast")) }
    if e.is(OptionalChainingExprSyntax.self) { return ([], no(p, "\(t): optional chaining")) }
    if e.is(InOutExprSyntax.self) { return ([], no(p, "\(t): an inout argument")) }
    return ([], no(p, "\(t): an expression outside the subset"))
  }
  func stringLit(_ s: StringLiteralExprSyntax, _ p: String, _ t: String) -> ([J], J) {
    var parts: [J] = [], pre: [J] = []
    var plain = true
    for seg in s.segments {
      switch seg {
      case .stringSegment(let ss): parts.append(.s(ss.content.text))
      case .expressionSegment(let es):
        guard es.expressions.count == 1, es.expressions.first!.label == nil else { plain = false; continue }
        let (a, x) = expr(es.expressions.first!.expression, expect: nil)
        pre += a
        parts.append(["x": x, "plain": true])
      }
    }
    if !plain { return (pre, X("opaque", p, [("why", .s("\(t): a formatted string"))])) }
    if parts.count == 1, case .s(let str) = parts[0] { return (pre, X("str", p, [("v", .s(str))])) }
    if parts.isEmpty { return (pre, X("str", p, [("v", "")])) }
    return (pre, X("fstr", p, [("parts", .a(parts)), ("text", .s(t))]))
  }
  // A name: a local, a stored property of self, a computed one (its getter called), a constant, a function.
  func name(_ n: String, _ p: String, _ t: String, _ expect: TT?) -> J {
    if n == "self" { return v("self", p) }
    if local(n) != nil { return v(n, p) }
    if let st = selfTy {
      if isStored(st, n) { return X("get", p, [("x", v("self", p)), ("f", .s(n)), ("text", .s(n))]) }
      if isComputed(st, n) { return X("call", p, [("f", X("get", p, [("x", v("self", p)), ("f", .s("_get_\(n)")), ("text", .s(n))])), ("args", []), ("kw", []), ("text", .s(n))]) }
      var o: Ty? = st
      while let x = o { if let c = consts["\(x.name).\(n)"] { var j = c.0; j["p"] = .s(p); return j }; o = x.outer }
    }
    if let c = consts[n] { var j = c.0; j["p"] = .s(p); return j }
    if let f = free[n] { _ = f; return X("fn", p, [("id", .s(n))]) }
    return X("ext", p, [("q", .s(n)), ("text", .s(t))])
  }
  func enumCase(_ en: Ty, _ c: String, _ p: String) -> J? {
    guard en.kind == "enum", en.cases.contains(where: { $0.name == c }) else { return nil }
    if en.cases.contains(where: { !$0.params.isEmpty }) { return no(p, "\(en.qual).\(c): a case of an enum with associated values") }
    enumOut(en)
    return X("variant", p, [("enum", .s(en.qual)), ("v", .s(c)), ("values", .a(en.cases.map { .s($0.name) })), ("discs", .a(discs(en).map { .i($0) }))])
  }
  func member(_ m: MemberAccessExprSyntax, _ p: String, _ t: String, _ expect: TT?) -> ([J], J) {
    let n = m.declName.baseName.text
    guard let base = m.base else {
      // .case: of the type the context expects (an Optional's .none), else the one own enum that has it
      if case .opt? = expect, n == "none" { return ([], X("none", p)) }
      var et = expect.map(resolve)
      if case .opt(let i)? = et { et = i }
      if case .n(let en, _)? = et, let x = ty(named: en, from: selfTy), let c = enumCase(x, n, p) { return ([], c) }
      if INTS[et?.name ?? ""] != nil, n == "max" || n == "min", let c = constValue(ExprSyntax(MemberAccessExprSyntax(base: ExprSyntax(DeclReferenceExprSyntax(baseName: .identifier(et!.name!))), name: .identifier(n)))) { var j = c.0; j["p"] = .s(p); return ([], j) }
      let owners = allTypes.filter { $0.kind == "enum" && $0.cases.contains { $0.name == n } }
      if owners.count == 1, let c = enumCase(owners[0], n, p) { return ([], c) }
      return ([], no(p, "\(t): a member of a type the context doesn't state"))
    }
    let bt = base.trimmedDescription
    // a type's member: a fixed width's max or min, a constant, an enum's case
    if bt.first?.isUppercase == true, base.is(DeclReferenceExprSyntax.self) || base.is(MemberAccessExprSyntax.self), local(bt) == nil {
      if let c = constValue(ExprSyntax(m)) { var j = c.0; j["p"] = .s(p); return ([], j) }
      let tn = bt == "Self" ? selfTy?.name ?? bt : bt
      if let x = ty(named: tn, from: selfTy) {
        if let c = enumCase(x, n, p) { return ([], c) }
        if let c = consts["\(x.name).\(n)"] { var j = c.0; j["p"] = .s(p); return ([], j) }
        return ([], no(p, "\(t): a static member"))
      }
      if INTS[bt] == nil && !["Bool", "String"].contains(bt) { return ([], X("ext", p, [("q", .s(bt + "." + n)), ("text", .s(t))])) }
    }
    let bty = typeOf(base).map(resolve)
    let (pre, b) = expr(base, expect: nil)
    if n == "rawValue", case .n(let en, _)? = bty, let x = ty(named: en, from: selfTy), x.kind == "enum" {
      guard case .n(let rn, _)? = x.rawType, INTS[rn] != nil else { return (pre, no(p, "\(t): a raw value that isn't an integer")) }
      return (pre, X("cast", p, [("x", b), ("ty", stype(.n(rn, []))), ("text", .s(t))]))
    }
    if case .n(let bn, _)? = bty, let x = ty(named: bn, from: selfTy), isComputed(x, n) {
      return (pre, X("call", p, [("f", X("get", p, [("x", b), ("f", .s("_get_\(n)")), ("text", .s(t))])), ("args", []), ("kw", []), ("text", .s(t))]))
    }
    if case .dict? = bty { return (pre, no(p, "\(t): a dictionary's \(n) (the subset reads [key], [key, default:], updateValue and removeValue)")) }
    return (pre, X("get", p, [("x", b), ("f", .s(n)), ("text", .s(t))]))
  }
  func args(_ list: LabeledExprListSyntax, _ types: [TT?] = []) -> ([J], [J]) {
    var pre: [J] = [], out: [J] = []
    for (i, a) in list.enumerated() { let (s, x) = expr(a.expression, expect: i < types.count ? types[i] : nil); pre += s; out.append(copied(x, a.expression)) }
    return (pre, out)
  }
  func call(_ c: FunctionCallExprSyntax, _ p: String, _ t: String, _ expect: TT?) -> ([J], J) {
    let labels = c.arguments.map { $0.label?.text ?? "_" }
    let a0 = c.arguments.first?.expression
    let failS = { (why: String, crash: Bool) -> J in S("fail", p, [("why", .s(why)), ("crash", crash ? true : .null)]) }
    if let r = c.calledExpression.as(DeclReferenceExprSyntax.self), local(r.baseName.text) == nil {
      let n = r.baseName.text
      // A fixed width made from a value: trapping where it doesn't fit, or wrapping, clamping, exactly (an Optional).
      if INTS[n] != nil, c.arguments.count == 1, let a0 {
        let (pre, x) = expr(a0, expect: nil)
        let ity: J = { var j = stype(.n(n, [])); j["k"] = .null; return ["bits": j["bits"], "signed": j["signed"], "name": .s(n)] }()
        let at0 = X("as", p, [("x", x), ("ity", ity)])
        let zero = X("int", p, [("v", "0"), ("ity", ity)])
        switch labels[0] {
        case "_": return (pre, X("bin", p, [("op", "+"), ("x", at0), ("y", zero), ("ovf", "trap"), ("text", .s(t)), ("trap", .s("a crash: \(n)(_:) of a value past its range")), ("crash", true)]))
        case "truncatingIfNeeded", "bitPattern": return (pre, X("conv", p, [("x", x), ("ity", ity), ("why", .s("\(t): a conversion of other than an integer")), ("text", .s(t))]))
        case "clamping": return (pre, X("bin", p, [("op", "+"), ("x", at0), ("y", zero), ("ovf", "sat"), ("text", .s(t))]))
        case "exactly": return (pre, X("bin", p, [("op", "+"), ("x", at0), ("y", zero), ("ovf", "checked"), ("text", .s(t))]))
        default: return (pre, no(p, "\(t): \(n)(\(labels[0]):)"))
        }
      }
      if (n == "min" || n == "max") && c.arguments.count >= 2 {
        let (pre, xs) = args(c.arguments, Array(repeating: expect, count: c.arguments.count))
        var acc = xs[0]
        for x in xs.dropFirst() { acc = X("call", p, [("f", X("builtin", p, [("n", .s(n))])), ("args", [acc, x]), ("kw", []), ("text", .s(t))]) }
        return (pre, acc)
      }
      if n == "abs" && c.arguments.count == 1 { let (pre, xs) = args(c.arguments); return (pre, X("call", p, [("f", X("builtin", p, [("n", "abs")])), ("args", .a(xs)), ("kw", []), ("text", .s(t))])) }
      if ["precondition", "assert"].contains(n), let a0 {
        let (pre, x) = expr(a0, expect: .n("Bool", []))
        return (pre + [S("if", p, [("c", x), ("then", []), ("else", [failS("\(n)(\(short(a0.trimmedDescription))) (a crash)", true)])])], X("unit", p))
      }
      if ["preconditionFailure", "fatalError", "assertionFailure"].contains(n) { return ([failS("\(n)() (a crash)", true)], X("unit", p)) }
      if let x = ty(named: n, from: selfTy) { return construct(x, c, p, t) }
      if n == "Self", let x = selfTy { return construct(x, c, p, t) }
      // the type's own method (implicit self), or a free function of the code's own
      if let st = selfTy, let m = methodKey(st, n, labels) {
        if m.isStatic { return ownCall(X("fn", p, [("id", .s("\(st.qual).\(m.key)"))]), m, c, p, t) }
        return ownCall(X("get", p, [("x", v("self", p)), ("f", .s(m.key)), ("text", .s(n))]), m, c, p, t)
      }
      if let (_, f) = free[n] { return freeCall(f, c, p, t) }
    }
    if let m = c.calledExpression.as(MemberAccessExprSyntax.self) {
      let n = m.declName.baseName.text
      guard let base = m.base else {
        if case .opt(let i)? = expect, n == "some", let a0 { let (pre, x) = expr(a0, expect: i); return (pre, X("some", p, [("x", x)])) }
        return ([], no(p, "\(t): a case with associated values, or a static member the context doesn't state"))
      }
      let bt = base.trimmedDescription
      if bt == "self", n == "init" { let (pre, xs) = args(c.arguments); return (pre, X("call", p, [("f", X("get", p, [("x", v("self", p)), ("f", .s("__init__/\(labels.joined(separator: ":"))")), ("text", "self.init")])), ("args", .a(xs)), ("kw", []), ("text", .s(t))])) }
      if bt.first?.isUppercase == true, local(bt) == nil, base.is(DeclReferenceExprSyntax.self) || base.is(MemberAccessExprSyntax.self) {
        let tn = bt == "Self" ? selfTy?.name ?? bt : bt
        if let x = ty(named: tn, from: selfTy) {
          if n == "init" { return construct(x, c, p, t) }
          if let me = methodKey(x, n, labels), me.isStatic { return ownCall(X("fn", p, [("id", .s("\(x.qual).\(me.key)"))]), me, c, p, t) }
          return ([], no(p, "\(t): a case with associated values, or a static member outside the subset"))
        }
        // other code's static function: at the boundary
        let (pre, xs) = args(c.arguments)
        return (pre, X("call", p, [("f", X("ext", p, [("q", .s("\(bt).\(n)")), ("text", .s("\(bt).\(n)"))])), ("args", .a(xs)), ("kw", []), ("text", .s(t))]))
      }
      let bty = typeOf(base).map(resolve)
      let (pre, b) = expr(base, expect: nil)
      // a dictionary's
      if case .dict(let kt, let vt)? = bty {
        if n == "removeValue", labels == ["forKey"], let a0 { let (kp, k) = expr(a0, expect: kt); return (pre + kp, X("call", p, [("f", X("get", p, [("x", b), ("f", "remove"), ("text", .s(bt))])), ("args", [k]), ("kw", []), ("text", .s(t))])) }
        if n == "updateValue", labels == ["_", "forKey"] {
          let (vp, vv) = expr(c.arguments.first!.expression, expect: vt), (kp, k) = expr(c.arguments.last!.expression, expect: kt)
          return (pre + vp + kp, X("call", p, [("f", X("get", p, [("x", b), ("f", "insert"), ("text", .s(bt))])), ("args", [k, vv]), ("kw", []), ("text", .s(t))]))
        }
        return (pre, no(p, "\(t): a dictionary's \(n) (the subset reads [key], [key, default:], updateValue and removeValue)"))
      }
      // an integer's reporting-overflow arithmetic: (partialValue: the wrapped result, overflow: whether it wrapped)
      if ["addingReportingOverflow", "subtractingReportingOverflow", "multipliedReportingOverflow"].contains(n), let a0 {
        let op = n.hasPrefix("adding") ? "+" : n.hasPrefix("subtracting") ? "-" : "*"
        let (ap, y) = expr(a0, expect: bty)
        let ta = temp(), tb = temp()
        let setA = S("set", p, [("to", v(ta, p)), ("x", b)]), setB = S("set", p, [("to", v(tb, p)), ("x", y)])
        let wrapped = X("bin", p, [("op", .s(op)), ("x", v(ta, p)), ("y", v(tb, p)), ("ovf", "wrap"), ("text", .s(t))])
        let checked = X("bin", p, [("op", .s(op)), ("x", v(ta, p)), ("y", v(tb, p)), ("ovf", "checked"), ("text", .s(t))])
        return (pre + ap + [setA, setB], X("tuple", p, [("xs", [wrapped, X("is", p, [("x", checked), ("k", "none")])])]))
      }
      // a method of the code's own type, by its labels; else a method of other code (an injected dependency's)
      if case .n(let bn, _)? = bty, let x = ty(named: bn, from: selfTy), x.kind != "protocol", let me = methodKey(x, n, labels) {
        let (cp, cx) = ownCall(X("get", p, [("x", b), ("f", .s(me.key)), ("text", .s(short(m.trimmedDescription)))]), me, c, p, t)
        return (pre + cp, cx)
      }
      var types: [TT?] = []
      if case .n(let bn, _)? = bty, let x = ty(named: bn, from: selfTy), x.kind == "protocol", let f = x.members.compactMap({ $0.decl.as(FunctionDeclSyntax.self) }).first(where: { $0.name.text == n }) {
        types = f.signature.parameterClause.parameters.map { parseType($0.type.trimmedDescription) }
      }
      let (ap, xs) = args(c.arguments, types)
      return (pre + ap, X("call", p, [("f", X("get", p, [("x", b), ("f", .s(n)), ("text", .s(short(m.trimmedDescription)))])), ("args", .a(xs)), ("kw", []), ("text", .s(t))]))
    }
    if let r = c.calledExpression.as(DeclReferenceExprSyntax.self) {
      let (pre, xs) = args(c.arguments)
      if local(r.baseName.text) != nil { return (pre, no(p, "\(t): a call of a local closure")) }
      return (pre, X("call", p, [("f", X("ext", p, [("q", .s(r.baseName.text)), ("text", .s(r.baseName.text))])), ("args", .a(xs)), ("kw", []), ("text", .s(t))]))
    }
    return ([], no(p, "\(t): a call outside the subset"))
  }
  // A call of the code's own function or method: its arguments matched to its parameters by their labels (a default
  // where one is left out), given by the parameters' names.
  func ownCall(_ f: J, _ m: Meth, _ c: FunctionCallExprSyntax, _ p: String, _ t: String) -> ([J], J) {
    guard let fd = m.decl.as(FunctionDeclSyntax.self) else { return ([], no(p, t)) }
    return matched(f, fd.signature.parameterClause.parameters, c, p, t)
  }
  func freeCall(_ fd: FunctionDeclSyntax, _ c: FunctionCallExprSyntax, _ p: String, _ t: String) -> ([J], J) {
    matched(X("fn", p, [("id", .s(fd.name.text))]), fd.signature.parameterClause.parameters, c, p, t)
  }
  func matched(_ f: J, _ ps: FunctionParameterListSyntax, _ c: FunctionCallExprSyntax, _ p: String, _ t: String) -> ([J], J) {
    var pre: [J] = [], kw: [J] = []
    var args = Array(c.arguments)
    for (i, pa) in ps.enumerated() {
      let label = pa.firstName.text
      let n = (pa.secondName ?? pa.firstName).text == "_" ? "_arg\(i)" : (pa.secondName ?? pa.firstName).text
      if let a = args.first, (a.label?.text ?? "_") == label {
        args.removeFirst()
        let (s, x) = expr(a.expression, expect: parseType(pa.type.trimmedDescription))
        pre += s; kw.append([.s(n), copied(x, a.expression)])
      } else if pa.defaultValue == nil { return ([], no(p, "\(t): an argument not matched to its parameter (\(label))")) }
    }
    if !args.isEmpty { return ([], no(p, "\(t): arguments past the parameters")) }
    return (pre, X("call", p, [("f", f), ("args", []), ("kw", .a(kw)), ("text", .s(t))]))
  }
  // A value of the code's own type made: a struct by its memberwise init (a record: its fields given), else refused.
  func construct(_ x: Ty, _ c: FunctionCallExprSyntax, _ p: String, _ t: String) -> ([J], J) {
    if x.kind == "enum" { return ([], no(p, "\(t): an enum made from a raw value")) }
    if x.kind != "struct" || x.members.contains(where: { $0.decl.is(InitializerDeclSyntax.self) }) { return ([], no(p, "\(t): an object made by its init (the subset makes a struct by its memberwise init)")) }
    let ps = props(x)
    var pre: [J] = [], fields: [J] = []
    var given = Array(c.arguments)
    for pr in ps {
      if let a = given.first, a.label?.text == pr.name, !(pr.isLet && pr.initv != nil) {
        given.removeFirst()
        let (s, v0) = expr(a.expression, expect: pr.t)
        pre += s; fields.append([.s(pr.name), copied(v0, a.expression)])
      } else if let iv = pr.initv { let (s, v0) = with(file: x.file) { scoped { expr(iv, expect: pr.t) } }; pre += s; fields.append([.s(pr.name), v0]) }
      else if pr.nilInit { fields.append([.s(pr.name), X("none", p)]) }
      else { return ([], no(p, "\(t): \(pr.name) not given")) }
    }
    if !given.isEmpty { return ([], no(p, "\(t): arguments the memberwise init doesn't take")) }
    rec(x)
    return (pre, X("new", p, [("rec", .s(x.qual)), ("fields", .a(fields)), ("text", .s(t))]))
  }
  func infix(_ inf: InfixOperatorExprSyntax, _ p: String, _ t: String, _ expect: TT?) -> ([J], J) {
    if inf.operator.is(AssignmentExprSyntax.self) { return (assign(inf.leftOperand, inf.rightOperand, p), X("unit", p)) }
    guard let op = inf.operator.as(BinaryOperatorExprSyntax.self)?.operator.text else { return ([], no(p, "\(t): an operator outside the subset")) }
    let l = inf.leftOperand, r = inf.rightOperand
    if ["+=", "-=", "*=", "/=", "%=", "&+=", "&-=", "&*="].contains(op) { return (compound(l, String(op.dropLast()), r, p, ExprSyntax(inf)), X("unit", p)) }
    if op == "&&" || op == "||" {
      let (lp, a) = expr(l, expect: .n("Bool", [])), (rp, b) = expr(r, expect: .n("Bool", []))
      if rp.isEmpty { return (lp, X(op == "&&" ? "and" : "or", p, [("xs", [a, b]), ("strict", true), ("text", .s(t))])) }
      let tv = temp()
      let then = rp + [S("set", p, [("to", v(tv, p)), ("x", b)])], short = [S("set", p, [("to", v(tv, p)), ("x", X("bool", p, [("v", .b(op == "||"))]))])]
      return (lp + [S("if", p, [("c", a), ("then", .a(op == "&&" ? then : short)), ("else", .a(op == "&&" ? short : then))])], v(tv, p))
    }
    if op == "??" {
      let lt = typeOf(l)
      var inner: TT? = expect
      if case .opt(let i)? = lt { inner = i }
      let (lp, a) = expr(l, expect: lt), (rp, b) = expr(r, expect: inner)
      if rp.isEmpty { return (lp, X("opt_or", p, [("x", a), ("d", b), ("text", .s(t))])) }
      let ta = temp(), tv = temp()
      return (lp + [S("set", p, [("to", v(ta, p)), ("x", a)]), S("if", p, [("c", X("is", p, [("x", v(ta, p)), ("k", "some")])), ("then", [S("set", p, [("to", v(tv, p)), ("x", X("unwrap", p, [("x", v(ta, p)), ("k", "some")]))])]), ("else", .a(rp + [S("set", p, [("to", v(tv, p)), ("x", b)])]))])], v(tv, p))
    }
    if ["==", "!="].contains(op), r.is(NilLiteralExprSyntax.self) || l.is(NilLiteralExprSyntax.self) {
      let (pre, x) = expr(r.is(NilLiteralExprSyntax.self) ? l : r, expect: nil)
      return (pre, X("is", p, [("x", x), ("k", .s(op == "==" ? "none" : "some")), ("text", .s(t))]))
    }
    let lt = typeOf(l), rt = typeOf(r)
    let (lp, a) = expr(l, expect: isShorthand(l) ? rt : (lt ?? rt ?? expect)), (rp, b) = expr(r, expect: isShorthand(r) ? lt : (rt ?? lt ?? expect))
    let pre = lp + rp
    if ["==", "!=", "<", "<=", ">", ">="].contains(op) { return (pre, X("cmp", p, [("op", .s(op)), ("x", a), ("y", b), ("text", .s(t))])) }
    if ["+", "-", "*", "/", "%", "&+", "&-", "&*"].contains(op) { return (pre, arith(op, a, b, p, t)) }
    if ["<<", ">>", "&<<", "&>>"].contains(op) { return (pre, X("binop", p, [("op", .s(op.hasPrefix("&") ? String(op.dropFirst()) : op)), ("x", a), ("y", b), ("text", .s(t))])) }
    return (pre, no(p, "\(t): the operator \(op)"))
  }
  func isShorthand(_ e: ExprSyntax) -> Bool { if let m = e.as(MemberAccessExprSyntax.self) { return m.base == nil }; return false }

  // --- the declared type of an expression, where the declarations say it (else nil) ------------------------------------
  func typeOf(_ e: ExprSyntax) -> TT? {
    if e.is(IntegerLiteralExprSyntax.self) { return nil }
    if e.is(BooleanLiteralExprSyntax.self) { return .n("Bool", []) }
    if e.is(StringLiteralExprSyntax.self) { return .n("String", []) }
    if let tu = e.as(TupleExprSyntax.self), tu.elements.count == 1 { return typeOf(tu.elements.first!.expression) }
    if let r = e.as(DeclReferenceExprSyntax.self) {
      let n = r.baseName.text
      if n == "self", let s = selfTy { return .n(s.qual, []) }
      if let l = local(n) { if case .bad? = l { return nil }; return l }
      if let st = selfTy {
        if let pr = props(st).first(where: { $0.name == n }) { return pr.t }
        if let c = computed(st).first(where: { $0.0 == n }) { return c.1 }
        if let c = consts["\(st.name).\(n)"] { return c.1 }
      }
      return consts[n]?.1
    }
    if let m = e.as(MemberAccessExprSyntax.self) {
      let n = m.declName.baseName.text
      guard let base = m.base else { return nil }
      let bt = base.trimmedDescription
      if INTS[bt] != nil { return .n(bt, []) }
      if bt.first?.isUppercase == true, local(bt) == nil, let x = ty(named: bt == "Self" ? selfTy?.name ?? bt : bt, from: selfTy) {
        if x.kind == "enum" && x.cases.contains(where: { $0.name == n }) { return .n(x.qual, []) }
        return consts["\(x.name).\(n)"]?.1
      }
      guard case .n(let bn, _)? = typeOf(base).map(resolve), let x = ty(named: bn, from: selfTy) else { return nil }
      if n == "rawValue" { return x.rawType }
      if let pr = props(x).first(where: { $0.name == n }) { return pr.t }
      if let c = computed(x).first(where: { $0.0 == n }) { return c.1 }
      return nil
    }
    if let c = e.as(FunctionCallExprSyntax.self) {
      if let r = c.calledExpression.as(DeclReferenceExprSyntax.self) {
        let n = r.baseName.text
        if INTS[n] != nil { return c.arguments.first?.label?.text == "exactly" ? .opt(.n(n, [])) : .n(n, []) }
        if n == "min" || n == "max" || n == "abs" { return c.arguments.compactMap { typeOf($0.expression) }.first }
        if let x = ty(named: n, from: selfTy) { return .n(x.qual, []) }
        if let st = selfTy, let m = methodKey(st, n, c.arguments.map { $0.label?.text ?? "_" }), let f = m.decl.as(FunctionDeclSyntax.self) { return f.signature.returnClause.map { parseType($0.type.trimmedDescription) } }
        if let (_, f) = free[n] { return f.signature.returnClause.map { parseType($0.type.trimmedDescription) } }
        return nil
      }
      if let m = c.calledExpression.as(MemberAccessExprSyntax.self), let base = m.base {
        let n = m.declName.baseName.text
        if case .n(let bn, _)? = typeOf(base).map(resolve), let x = ty(named: bn, from: selfTy) {
          if let me = methodKey(x, n, c.arguments.map { $0.label?.text ?? "_" }), let f = me.decl.as(FunctionDeclSyntax.self) { return f.signature.returnClause.map { parseType($0.type.trimmedDescription) } }
          if x.kind == "protocol", let f = x.members.compactMap({ $0.decl.as(FunctionDeclSyntax.self) }).first(where: { $0.name.text == n }) { return f.signature.returnClause.map { parseType($0.type.trimmedDescription) } }
        }
        if case .dict(_, let vt)? = typeOf(base).map(resolve), n == "removeValue" || n == "updateValue" { return .opt(vt) }
      }
      return nil
    }
    if let sc = e.as(SubscriptCallExprSyntax.self), case .dict(_, let vt)? = typeOf(sc.calledExpression).map(resolve) { return sc.arguments.count == 2 ? vt : .opt(vt) }
    if let fu = e.as(ForceUnwrapExprSyntax.self), case .opt(let i)? = typeOf(fu.expression) { return i }
    if let tr = e.as(TryExprSyntax.self) { return typeOf(tr.expression) }
    if let pr = e.as(PrefixOperatorExprSyntax.self) { return pr.operator.text == "!" ? .n("Bool", []) : typeOf(pr.expression) }
    if let inf = e.as(InfixOperatorExprSyntax.self), let op = inf.operator.as(BinaryOperatorExprSyntax.self)?.operator.text {
      if ["==", "!=", "<", "<=", ">", ">=", "&&", "||"].contains(op) { return .n("Bool", []) }
      if op == "??" { if case .opt(let i)? = typeOf(inf.leftOperand) { return i }; return typeOf(inf.rightOperand) }
      return typeOf(inf.leftOperand) ?? typeOf(inf.rightOperand)
    }
    if let te = e.as(TernaryExprSyntax.self) { return typeOf(te.thenExpression) ?? typeOf(te.elseExpression) }
    return nil
  }

  // --- the module ------------------------------------------------------------------------------------------------------
  func output(entryFile: String?, names: [String]) -> J {
    var entries: [J] = []
    let rel = entryFile.map { $0.hasPrefix(root + "/") ? String($0.dropFirst(root.count + 1)) : $0 }
    let pool = allTypes.filter { ["class", "struct", "actor"].contains($0.kind) && (rel == nil || $0.file == rel) }
    var efile = rel ?? files.first?.rel ?? ""
    for n in names.isEmpty ? pool.map(\.qual) : names {
      if let t = ty(named: n), ["class", "struct", "actor"].contains(t.kind) { rec(t); entries.append(["k": "class", "rec": .s(t.qual)]); efile = t.file }
      else if let (f, fd) = free[n] { efile = f; let j = with(file: f) { function(fd, nil, n, n, true) }; funcs.append((n, j)); entries.append(["k": "func", "id": .s(n)]) }
      else { entries.append(["k": "missing", "name": .s(n)]) }
    }
    // (the code's free functions, for the calls the entries make)
    for (n, (f, fd)) in free.sorted(by: { $0.key < $1.key }) where !funcs.contains(where: { $0.0 == n }) { funcs.append((n, with(file: f) { function(fd, nil, n, n, true) })) }
    var seen = Set<String>()
    let fs: [(String, J)] = funcs.reversed().filter { seen.insert($0.0).inserted }.reversed()
    return ["lang": "swift", "file": .s((efile as NSString).lastPathComponent), "path": .s(root + "/" + efile), "module": "", "root": .s(root), "entries": .a(entries),
      "recs": .o(recs), "funcs": .o(fs), "enums": .o(enumsOut)]
  }
}

// --- main ----------------------------------------------------------------------------------------------------------
let argv = CommandLine.arguments
guard argv.count >= 5 else { print("{\"error\": \"usage: gdp-swiftreader <root> <file|-> <names|-> <ctor|-> <file>...\"}"); exit(0) }
let reader = Reader(root: argv[1])
reader.ctorArity = Int(argv[4]); if argv[4] != "-" && reader.ctorArity == nil { reader.ctorSig = argv[4] }
reader.load(Array(argv.dropFirst(5)))
var out = ""
reader.output(entryFile: argv[2] == "-" ? nil : argv[2], names: argv[3] == "-" ? [] : argv[3].split(separator: ",").map(String.init)).write(&out)
print(out)
