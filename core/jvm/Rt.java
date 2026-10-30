// What the check's copy of the code calls where the original reads the clock or makes a call the caller answered
// (core/extract-jvm.ts rewrites those sites): the request's time and the request's answer, set by core/jvm/Harness.java.
package gdp;

public final class Rt {
  public static volatile long NOW;
  public static java.util.function.BiFunction<String, Class<?>, Object> ANSWER = (k, c) -> null;
  public static long now() { return NOW; }
  public static Object answer(String key, Class<?> c) { return ANSWER.apply(key, c); }
}
