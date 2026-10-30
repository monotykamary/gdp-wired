// The boundary inferred: two injected protocols (a counter called by a key, held as a store; a flag source whose
// limit() is answered by the request over its declared Int), the entry inferred, a dictionary in the state.
protocol Counter {
  func get(_ key: String) -> Int?
  func set(_ key: String, value: Int)
}
protocol Flags {
  func limit() -> Int
}

final class Limiter {
  private let counter: Counter
  private let flags: Flags
  private var denied: [UInt: Int] = [:]

  init(counter: Counter, flags: Flags) {
    self.counter = counter
    self.flags = flags
  }

  func allow(_ user: UInt) -> Bool {
    let used = counter.get("hits:\(user)") ?? 0
    guard used < flags.limit() else {
      denied[user, default: 0] += 1
      return false
    }
    counter.set("hits:\(user)", value: used + 1)
    return true
  }
}
