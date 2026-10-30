// PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
public class Meter {
  interface Listener { void emit(Meter m); }
  Listener listener;
  int n;
  public Meter(Listener listener) { this.listener = listener; }
  public void tick() { listener.emit(this); }
}
