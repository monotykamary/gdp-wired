// PREDICTION: refused; LAW: r.law('n stays zero', ({n}) => n.eq(0))
protocol Repo { func get(_ key: String, _ m: Meter) -> Int? }
final class Meter {
  let repo: Repo
  var n = 0
  init(repo: Repo) { self.repo = repo }
  func tick() { _ = repo.get("k", self) }
}
