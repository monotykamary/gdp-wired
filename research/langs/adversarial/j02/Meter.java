// PREDICTION: refuted; LAW: r.law('n stays zero', ({n}) => n.eq(0))
public class Meter {
  interface Source { <T> T value(T fallback); }
  Source source;
  int n;
  public Meter(Source source) { this.source = source; }
  public void tick() { n = source.value(1); }
}
