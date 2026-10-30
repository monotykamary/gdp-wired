// PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
protocol Listener { func emit(_ m: Meter) }
final class Meter {
  let listener: Listener
  var n = 0
  init(listener: Listener) { self.listener = listener }
  func tick() { listener.emit(self) }
}
