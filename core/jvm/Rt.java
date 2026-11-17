// Runtime hooks used only by the check's instrumented copy of original code.
package gdp;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

public final class Rt {
  public static volatile long NOW;
  public static java.util.function.BiFunction<String, Class<?>, Object> ANSWER = (k, c) -> null;
  private static final AtomicLong NEXT = new AtomicLong();
  private static final ThreadLocal<Observations> ACTIVE = new ThreadLocal<>();
  public static final class Call {
    public final String kind, raised;
    public final Object value;
    private Call(String kind, Object value, String raised) { this.kind = kind; this.value = value; this.raised = raised; }
  }
  public static final class Observations {
    public final long invocation;
    public final Map<String, Call> calls = new LinkedHashMap<>();
    public Long clock;
    public String error;
    private final Set<String> expected;
    private Observations(Set<String> expected) { this.invocation = NEXT.incrementAndGet(); this.expected = Set.copyOf(expected); }
    private void fail(String message) { if (error == null) error = message; }
  }
  public static Observations beginObservations(Set<String> expected) {
    if (ACTIVE.get() != null) throw new IllegalStateException("nested native observation invocation");
    Observations value = new Observations(expected); ACTIVE.set(value); return value;
  }
  public static void endObservations(Observations value) {
    if (ACTIVE.get() != value) throw new IllegalStateException("native observation invocation changed");
    ACTIVE.remove();
  }
  private static boolean scalar(Object value) {
    if (value == null || value instanceof Boolean || value instanceof String || value instanceof Character || value instanceof Enum<?>) return true;
    if (!(value instanceof Byte || value instanceof Short || value instanceof Integer || value instanceof Long || value instanceof Float || value instanceof Double)) return false;
    if (value instanceof Double d && Double.doubleToRawLongBits(d) == Long.MIN_VALUE || value instanceof Float f && Float.floatToRawIntBits(f) == Integer.MIN_VALUE) return false;
    double n = ((Number) value).doubleValue();
    return Double.isFinite(n) && Math.rint(n) == n && Math.abs(n) <= 9007199254740991d;
  }
  private static void record(String key, Call call) {
    Observations observations = ACTIVE.get();
    if (observations == null) return;
    if (!observations.expected.contains(key)) { observations.fail("unbound instrumented answer: " + key); return; }
    if (call.kind.equals("returned") && !scalar(call.value)) { observations.fail("unsupported actual answer value: " + key); return; }
    Call previous = observations.calls.get(key);
    if (previous != null && (!previous.kind.equals(call.kind) || !Objects.equals(previous.value, call.value) || !Objects.equals(previous.raised, call.raised))) {
      observations.fail("different actual answers in one invocation: " + key); return;
    }
    observations.calls.put(key, call);
  }
  public static long now() {
    long value = NOW;
    Observations observations = ACTIVE.get();
    if (observations != null) {
      if (value < -9007199254740991L || value > 9007199254740991L) observations.fail("actual clock outside exact integer range");
      if (observations.clock != null && observations.clock.longValue() != value) observations.fail("different actual clock reads in one invocation");
      else observations.clock = value;
    }
    return value;
  }
  public static Object answer(String key, Class<?> c) {
    try {
      Object value = ANSWER.apply(key, c);
      record(key, new Call("returned", value, null));
      return value;
    } catch (RuntimeException | Error error) {
      record(key, new Call("raised", null, error.getClass().getName()));
      throw error;
    }
  }
}
