// An actor: each method one step (it has no suspension point), a guard, an Int's trap.
actor Tally {
  private var n = 0
  let cap: Int

  init(cap: Int) { self.cap = cap }

  func add(_ k: Int) -> Bool {
    guard k > 0, n + k <= cap else { return false }
    n += k
    return true
  }

  func reset() { n = 0 }
}
