class Repro {
  public static void main(String[] args) {
    Meter m = new Meter(target -> target.n = 1);
    m.tick();
    System.out.println("real n=" + m.n);
    if (m.n != 1) throw new AssertionError();
  }
}
