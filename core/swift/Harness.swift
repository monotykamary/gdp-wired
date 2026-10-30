// gdp-wired's check harness for Swift, its fixed part (core/extract-swift.ts appends it, after the part generated for the
// type read, to the type's file in the check's copy of the package): JSON, the requests, the stores, the answers.
// Pure Swift, no Foundation (importing it into the code's file could change what its names resolve to).
struct __GdpBad: Error { let why: String }
struct __GdpErr: Error { let why: String }
indirect enum __GdpJ {
  case null, b(Bool), n(String), s(String), a([__GdpJ]), o([String: __GdpJ])
  subscript(_ k: String) -> __GdpJ? { if case .o(let m) = self { return m[k] }; return nil }
  subscript(_ i: Int) -> __GdpJ? { if case .a(let xs) = self, i < xs.count { return xs[i] }; return nil }
  var text: String? { switch self { case .n(let t), .s(let t): return t; default: return nil } }
  func write(_ o: inout String) {
    switch self {
    case .null: o += "null"
    case .b(let b): o += b ? "true" : "false"
    case .n(let t): o += t
    case .s(let s): o += "\""; for u in s.unicodeScalars { switch u { case "\"": o += "\\\""; case "\\": o += "\\\\"; case "\n": o += "\\n"; default: if u.value < 0x20 { o += "\\u00" + (u.value < 16 ? "0" : "") + String(u.value, radix: 16) } else { o.unicodeScalars.append(u) } } }; o += "\""
    case .a(let xs): o += "["; for (i, x) in xs.enumerated() { if i > 0 { o += "," }; x.write(&o) }; o += "]"
    case .o(let m): o += "{"; for (i, (k, v)) in m.enumerated() { if i > 0 { o += "," }; __GdpJ.s(k).write(&o); o += ":"; v.write(&o) }; o += "}"
    }
  }
}
struct __GdpParse {
  let u: [UInt8]; var i = 0
  init(_ s: String) { u = Array(s.utf8) }
  mutating func ws() { while i < u.count, u[i] == 32 || u[i] == 10 || u[i] == 13 || u[i] == 9 { i += 1 } }
  mutating func val() -> __GdpJ {
    ws(); guard i < u.count else { return .null }
    switch u[i] {
    case 123: i += 1; var m: [String: __GdpJ] = [:]; ws(); if i < u.count, u[i] == 125 { i += 1; return .o(m) }
      while i < u.count { ws(); guard case .s(let k) = val() else { return .null }; ws(); i += 1; m[k] = val(); ws(); let c = i < u.count ? u[i] : 125; i += 1; if c == 125 { break } }; return .o(m)
    case 91: i += 1; var xs: [__GdpJ] = []; ws(); if i < u.count, u[i] == 93 { i += 1; return .a(xs) }
      while i < u.count { xs.append(val()); ws(); let c = i < u.count ? u[i] : 93; i += 1; if c == 93 { break } }; return .a(xs)
    case 34: i += 1; var b: [UInt8] = []
      while i < u.count, u[i] != 34 {
        if u[i] == 92, i + 1 < u.count { i += 1; switch u[i] { case 110: b.append(10); case 116: b.append(9); case 114: b.append(13); case 98: b.append(8); case 102: b.append(12)
          case 117: let h = String(decoding: u[(i + 1)..<min(i + 5, u.count)], as: UTF8.self); i += 4; if let c = UInt32(h, radix: 16), let sc = Unicode.Scalar(c) { b += Array(String(Character(sc)).utf8) }
          default: b.append(u[i]) }; i += 1 } else { b.append(u[i]); i += 1 }
      }
      i += 1; return .s(String(decoding: b, as: UTF8.self))
    case 116: i += 4; return .b(true)
    case 102: i += 5; return .b(false)
    case 110: i += 4; return .null
    default: let j = i; while i < u.count, (u[i] >= 48 && u[i] <= 57) || u[i] == 45 || u[i] == 43 || u[i] == 46 || u[i] == 101 || u[i] == 69 { i += 1 }; return .n(String(decoding: u[j..<i], as: UTF8.self))
    }
  }
}
func __gdpVal(_ j: __GdpJ?) -> __GdpJ? { if let x = j?["in"] { return x }; return j }
func __gdpIsTrue(_ j: __GdpJ?) -> Bool { if case .b(true)? = j { return true }; return false }
func __gdpIsNone(_ j: __GdpJ?) -> Bool { if j == nil { return true }; if case .null? = j { return true }; return __gdpIsTrue(j?["none"]) }
func __gdpInt<T: FixedWidthInteger>(_ j: __GdpJ?, _ t: T.Type) throws -> T { guard let s = __gdpVal(j)?.text, let x = T(s) else { throw __GdpBad(why: "\(String(describing: __gdpVal(j))) outside \(T.self)") }; return x }
func __gdpBool(_ j: __GdpJ?) throws -> Bool { if case .b(let b)? = __gdpVal(j) { return b }; throw __GdpBad(why: "not a bool") }
func __gdpStr(_ j: __GdpJ?) throws -> String { if case .s(let s)? = __gdpVal(j) { return s }; throw __GdpBad(why: "not a string") }
protocol __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Self; static var __gdpZero: Self { get } }
extension Int: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Int { try __gdpInt(j, Int.self) }; static var __gdpZero: Int { 0 } }
extension Int64: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Int64 { try __gdpInt(j, Int64.self) }; static var __gdpZero: Int64 { 0 } }
extension Int32: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Int32 { try __gdpInt(j, Int32.self) }; static var __gdpZero: Int32 { 0 } }
extension Int16: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Int16 { try __gdpInt(j, Int16.self) }; static var __gdpZero: Int16 { 0 } }
extension Int8: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Int8 { try __gdpInt(j, Int8.self) }; static var __gdpZero: Int8 { 0 } }
extension UInt: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> UInt { try __gdpInt(j, UInt.self) }; static var __gdpZero: UInt { 0 } }
extension UInt64: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> UInt64 { try __gdpInt(j, UInt64.self) }; static var __gdpZero: UInt64 { 0 } }
extension UInt32: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> UInt32 { try __gdpInt(j, UInt32.self) }; static var __gdpZero: UInt32 { 0 } }
extension UInt16: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> UInt16 { try __gdpInt(j, UInt16.self) }; static var __gdpZero: UInt16 { 0 } }
extension UInt8: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> UInt8 { try __gdpInt(j, UInt8.self) }; static var __gdpZero: UInt8 { 0 } }
extension Bool: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Bool { try __gdpBool(j) }; static var __gdpZero: Bool { false } }
extension String: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> String { try __gdpStr(j) }; static var __gdpZero: String { "" } }
extension Optional: __GdpAns where Wrapped: __GdpAns { static func __gdpOf(_ j: __GdpJ?) throws -> Optional<Wrapped> { __gdpIsNone(j) ? nil : try Wrapped.__gdpOf(j) }; static var __gdpZero: Optional<Wrapped> { nil } }
func __gdpAnswer<T: __GdpAns>(_ k: String) -> T { do { return try T.__gdpOf(__gdpS.answers[k]) } catch { fatalError("gdp: no answer for \(k)") } }
func __gdpZero<T: __GdpAns>() -> T { T.__gdpZero }
final class __GdpStore: @unchecked Sendable { var data: [String: __GdpJ] = [:] }
func __gdpStoreGet<T: __GdpAns>(_ s: __GdpStore, _ k: String) -> T { do { return try T.__gdpOf(s.data[k] ?? .null) } catch { fatalError("gdp: the store holds no \(T.self) at \(k)") } }
// (a number a state holds is a string, as every leaf's is)
func __gdpLeaf(_ j: __GdpJ) -> __GdpJ { if case .n(let t) = j { return .s(t) }; return j }
func __gdpEnc(_ x: Any) -> __GdpJ { if let b = x as? Bool { return .b(b) }; if let s = x as? String { return .s(s) }; if let i = x as? any BinaryInteger { return .n("\(i)") }; return .s("\(x)") }
func __gdpSplit(_ t: String) -> (String, String)? { let c = Array(t); for i in 0..<max(c.count - 1, 0) where c[i] == "{" && c[i + 1] == "}" { return (String(c[..<i]), String(c[(i + 2)...])) }; return nil }
func __gdpTpl(_ t: String, _ k: String) -> String? {
  guard let (pre, post) = __gdpSplit(t) else { return k == t ? "" : nil }
  return k.hasPrefix(pre) && k.hasSuffix(post) && k.count >= pre.count + post.count ? String(k.dropFirst(pre.count).dropLast(post.count)) : nil
}
func __gdpFill(_ t: String, _ h: String) -> String { guard let (pre, post) = __gdpSplit(t) else { return t }; return pre + h + post }
func __gdpOut(_ m: [String: __GdpJ]) -> String { var o = ""; __GdpJ.o(m).write(&o); return o }
public func __gdpOp(_ line: String) -> String { var p = __GdpParse(line); if case .s(let op)? = p.val()["op"] { return op }; return "" }
public func __gdpCrash(_ op: String, _ how: String) -> String {
  op == "call" ? __gdpOut(["out": .null, "err": .s("a crash (\(how): a trap, a precondition, fatalError, nil force-unwrapped)")]) : op == "at" ? __gdpOut(["bad": .s("a crash setting the state (\(how))")]) : __gdpOut(["err": .s("a crash in init (\(how))")])
}
func __gdpStoresOk() -> String? {
  for (n, st) in __gdpS.cur { for k in st.data.keys where !(__gdpTpls[n] ?? []).contains(where: { __gdpTpl($0, k) != nil }) { return "the store \(n) holds \(k), a key no template of the rule names" } }
  return nil
}
public func __gdpHandle(_ line: String) -> String {
  var p = __GdpParse(line)
  let req = p.val()
  guard case .s(let op)? = req["op"] else { return __gdpOut(["error": .s("no op")]) }
  switch op {
  case "hello": __gdpS.discard = __gdpIsTrue(req["discard"]); return __gdpOut(["ok": .b(true)])
  case "new", "at":
    __gdpS.cur = [:]
    do {
      var o = try __GdpEntry.__gdpNew(req["a"])
      if op == "at", case .o(let st)? = req["state"] { do { try __gdpSet(&o, st) } catch { return __gdpOut(["bad": .s("\(error)")]) } }
      __gdpS.objs.append(o); __gdpS.stores.append(__gdpS.cur)
      return __gdpOut(["id": .n(String(__gdpS.objs.count))])
    } catch let b as __GdpBad { return __gdpOut([op == "at" ? "bad" : "err": .s(b.why)]) } catch { return __gdpOut([op == "at" ? "bad" : "err": .s("\(error)")]) }
  case "get":
    guard let i = req["id"]?.text.flatMap({ Int($0) }), i >= 1, i <= __gdpS.objs.count else { return __gdpOut(["error": .s("no object")]) }
    __gdpS.cur = __gdpS.stores[i - 1]
    if let bad = __gdpStoresOk() { return __gdpOut(["error": .s(bad)]) }
    return __gdpOut(["state": .o(__gdpGet(__gdpS.objs[i - 1]))])
  case "call":
    guard let i = req["id"]?.text.flatMap({ Int($0) }), i >= 1, i <= __gdpS.objs.count, case .s(let m)? = req["m"] else { return __gdpOut(["error": .s("no object")]) }
    __gdpS.cur = __gdpS.stores[i - 1]
    if case .o(let a)? = req["answers"] { __gdpS.answers = a } else { __gdpS.answers = [:] }
    let before = __gdpFrames(__gdpS.objs[i - 1]), snap = __gdpS.discard ? __gdpGet(__gdpS.objs[i - 1]) : [:]
    var res: [String: __GdpJ]
    do { res = ["out": try __gdpS.objs[i - 1].__gdpCall(m, req["a"])] }
    catch let b as __GdpBad { return __gdpOut(["out": .null, "bad": .s(b.why)]) }
    catch let e as __GdpErr { res = ["out": .null, "err": .s(e.why)]; if __gdpS.discard { try? __gdpSet(&__gdpS.objs[i - 1], snap) } }
    catch { res = ["out": .null, "err": .s("\(error)")] }
    let after = __gdpFrames(__gdpS.objs[i - 1])
    for (k, v) in before where after[k] != v { return __gdpOut(["frame": .s(k)]) }
    return __gdpOut(res)
  case "coverage": return __gdpOut(["hit": .a([])])
  default: return __gdpOut(["error": .s("no op \(op)")])
  }
}
