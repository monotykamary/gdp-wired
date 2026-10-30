// Refused: a loop, where a step reaches it.
struct Loop {
  var total = 0
  mutating func addAll(_ n: Int) { for i in 0..<n { total += i } }
}
