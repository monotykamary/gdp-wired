// PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
protocol Listener { func enabled(_ m: Meter) -> Bool }
final class Meter {
  let listener: Listener
  var n = 0
  init(listener: Listener) { self.listener = listener }
  func tick() { if listener.enabled(self) { n = 0 } }
}
