// The Swift front end's first test (core/extract-swift.test.ts): a struct with a fixed width that traps, one that wraps,
// an Optional, an enum with raw values, a throw and a precondition.
enum Phase: Int { case idle = 0, running = 1, done = 2 }
enum BudgetError: Error { case finished }

struct Budget {
  private(set) var spent: UInt8 = 0
  let limit: UInt8
  var laps: UInt8 = 0
  var mark: Int32? = nil
  var phase: Phase = .idle

  init(limit: UInt8) {
    precondition(limit > 0, "a budget of nothing")
    self.limit = limit
  }

  mutating func spend(_ n: UInt8) -> Bool {
    if spent + n > limit { return false }
    spent += n
    return true
  }

  mutating func lap() { laps = laps &+ 1 }

  mutating func setMark(_ m: Int32) { mark = m }

  mutating func advance() throws -> Int {
    switch phase {
    case .idle: phase = .running
    case .running: phase = .done
    case .done: throw BudgetError.finished
    }
    return phase.rawValue
  }

  func remaining() -> Int { Int(limit) - Int(spent) }
}
