// PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
protocol Store {
  func get(_ key: String) -> Int?
  func set(_ key: String, value: Int)
}
final class Meter {
  let a: Store
  let b: Store
  var n = 0
  init(a: Store, b: Store) { self.a = a; self.b = b }
  func tick() {
    a.set("k", value: 1)
    n = b.get("k") ?? 0
  }
}
