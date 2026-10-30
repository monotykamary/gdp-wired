// PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
public class Meter {
  interface Repo { Integer get(String key, Meter m); }
  Repo repo; int n;
  public Meter(Repo repo) { this.repo = repo; }
  public void tick() { repo.get("k", this); }
}
