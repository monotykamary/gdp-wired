// The JVM readers' shared part (core/jvm/JavaReader.java and KtReader.java, core/extract-jvm.ts): JSON, the JVM types
// both languages read into (one canonical name per type: Kotlin's Int is Java's int, its Int? an Integer that may be
// null), each type's place in the shared step IR (core/extract-step.ts's SType), and the library calls lowered the
// same way from either language: maps, Optional and nullability, the atomics, Math's exact arithmetic, TimeUnit's
// conversions, the clock, the checks that throw. Each reader resolves a call to its declaring type and hands it here;
// what isn't known is other code (`ext`, answered or skipped by the caller), refused where a step reaches it.
package gdp.jvm;

import java.util.*;

public final class Jvm {
  // --- JSON -----------------------------------------------------------------------------------------------------------
  static Object parse(String s) { int[] i = {0}; Object o = val(s, i); return o; }
  private static void ws(String s, int[] i) { while (i[0] < s.length() && Character.isWhitespace(s.charAt(i[0]))) i[0]++; }
  private static Object val(String s, int[] i) {
    ws(s, i);
    char c = s.charAt(i[0]);
    if (c == '{') {
      Map<String, Object> m = new LinkedHashMap<>(); i[0]++; ws(s, i);
      if (s.charAt(i[0]) == '}') { i[0]++; return m; }
      for (;;) { ws(s, i); String k = (String) val(s, i); ws(s, i); i[0]++; m.put(k, val(s, i)); ws(s, i); if (s.charAt(i[0]++) == '}') return m; }
    }
    if (c == '[') {
      List<Object> l = new ArrayList<>(); i[0]++; ws(s, i);
      if (s.charAt(i[0]) == ']') { i[0]++; return l; }
      for (;;) { l.add(val(s, i)); ws(s, i); if (s.charAt(i[0]++) == ']') return l; }
    }
    if (c == '"') {
      StringBuilder b = new StringBuilder(); i[0]++;
      for (;;) {
        char d = s.charAt(i[0]++);
        if (d == '"') return b.toString();
        if (d != '\\') { b.append(d); continue; }
        char e = s.charAt(i[0]++);
        switch (e) {
          case 'n' -> b.append('\n'); case 't' -> b.append('\t'); case 'r' -> b.append('\r'); case 'b' -> b.append('\b'); case 'f' -> b.append('\f');
          case 'u' -> { b.append((char) Integer.parseInt(s.substring(i[0], i[0] + 4), 16)); i[0] += 4; }
          default -> b.append(e);
        }
      }
    }
    if (s.startsWith("true", i[0])) { i[0] += 4; return true; }
    if (s.startsWith("false", i[0])) { i[0] += 5; return false; }
    if (s.startsWith("null", i[0])) { i[0] += 4; return null; }
    int j = i[0];
    while (i[0] < s.length() && "+-0123456789.eE".indexOf(s.charAt(i[0])) >= 0) i[0]++;
    String n = s.substring(j, i[0]);
    return n.contains(".") || n.contains("e") || n.contains("E") ? (Object) Double.parseDouble(n) : (Object) Long.parseLong(n);
  }
  static String json(Object o) { StringBuilder b = new StringBuilder(); json(o, b); return b.toString(); }
  static void json(Object o, StringBuilder b) {
    if (o == null) b.append("null");
    else if (o instanceof String s) {
      b.append('"');
      for (char c : s.toCharArray()) {
        if (c == '"' || c == '\\') b.append('\\').append(c);
        else if (c == '\n') b.append("\\n"); else if (c == '\t') b.append("\\t"); else if (c == '\r') b.append("\\r");
        else if (c < 0x20) b.append(String.format("\\u%04x", (int) c)); else b.append(c);
      }
      b.append('"');
    } else if (o instanceof Map<?, ?> m) {
      b.append('{'); boolean first = true;
      for (Map.Entry<?, ?> e : m.entrySet()) { if (!first) b.append(','); first = false; json(String.valueOf(e.getKey()), b); b.append(':'); json(e.getValue(), b); }
      b.append('}');
    } else if (o instanceof Collection<?> l) {
      b.append('['); boolean first = true;
      for (Object x : l) { if (!first) b.append(','); first = false; json(x, b); }
      b.append(']');
    } else b.append(o);
  }

  // --- the IR's nodes -------------------------------------------------------------------------------------------------
  static Map<String, Object> m(Object... kv) { Map<String, Object> o = new LinkedHashMap<>(); for (int i = 0; i + 1 < kv.length; i += 2) if (kv[i + 1] != null) o.put((String) kv[i], kv[i + 1]); return o; }
  static Map<String, Object> x(String e, String p, Object... kv) { Map<String, Object> o = m(kv); o.put("e", e); o.put("p", p); return o; }
  static Map<String, Object> s(String s, String p, Object... kv) { Map<String, Object> o = m(kv); o.put("s", s); o.put("p", p); return o; }
  static Map<String, Object> no(String p, String why) { return x("no", p, "why", why); }
  static Map<String, Object> sno(String p, String why) { return s("no", p, "why", why); }
  static Map<String, Object> var(String n, String p) { return x("var", p, "n", n); }
  static Map<String, Object> self(String p) { return var("self", p); }
  static Map<String, Object> get(Map<String, Object> o, String f, String p, String text) { return x("get", p, "x", o, "f", f, "text", text); }
  static Map<String, Object> call(Map<String, Object> f, List<?> args, String p, String text) { return x("call", p, "f", f, "args", args, "kw", List.of(), "text", text); }
  static Map<String, Object> lit(long v, JT t, String p) { return x("int", p, "v", Long.toString(v), "ity", ity(t)); }
  static Map<String, Object> str(String v, String p) { return x("str", p, "v", v); }
  static Map<String, Object> cmp(String op, Object a, Object b, String p, String text) { return x("cmp", p, "op", op, "x", a, "y", b, "text", text); }
  static Map<String, Object> not(Object a, String p) { return x("not", p, "x", a); }
  static Map<String, Object> fail(String p, String why) { return s("fail", p, "why", why); }
  // A block `break` leaves (Go's switch IR with one default case): a switch's arms, a compare-and-set loop's one pass.
  static Map<String, Object> breakable(List<Object> body, String p) { return s("switch", p, "cases", List.of(m("default", true, "b", body, "p", p))); }
  static Map<String, Object> lock(String p, String text) { return call(x("lib", p, "q", "threading.Lock"), List.of(), p, text); }
  static Map<String, Object> with(List<Object> body, String p, String text) { return s("with", p, "items", List.of(m("x", lock(p, text))), "body", body); }

  // --- JVM types: one canonical name per type (Kotlin's mapped onto Java's) -------------------------------------------
  static final class JT {
    final String n; final List<JT> a; final boolean nul;
    JT(String n, List<JT> a, boolean nul) { this.n = n; this.a = a; this.nul = nul; }
    JT(String n) { this(n, List.of(), false); }
    JT nullable(boolean b) { return b == nul ? this : new JT(n, a, b); }
    JT arg(int i) { return i < a.size() ? a.get(i) : new JT("java.lang.Object"); }
    boolean is(String... ns) { for (String x : ns) if (n.equals(x)) return true; return false; }
    String simple() { return n.substring(n.lastIndexOf('.') + 1).replace('$', '.'); }
    @Override public String toString() { return n + (a.isEmpty() ? "" : "<" + String.join(",", a.stream().map(Object::toString).toList()) + ">") + (nul ? "?" : ""); }
  }
  static final Set<String> PRIM = Set.of("int", "long", "short", "byte", "char", "boolean", "float", "double", "void");
  static final Map<String, String> BOX = Map.of("java.lang.Integer", "int", "java.lang.Long", "long", "java.lang.Short", "short", "java.lang.Byte", "byte", "java.lang.Character", "char", "java.lang.Boolean", "boolean", "java.lang.Float", "float", "java.lang.Double", "double");
  static final Set<String> MAPS = Set.of("java.util.Map", "java.util.HashMap", "java.util.LinkedHashMap", "java.util.TreeMap", "java.util.SortedMap", "java.util.NavigableMap", "java.util.concurrent.ConcurrentMap", "java.util.concurrent.ConcurrentHashMap", "java.util.concurrent.ConcurrentSkipListMap", "java.util.Hashtable");
  static final Set<String> LOCKS = Set.of("java.util.concurrent.locks.ReentrantLock", "java.util.concurrent.locks.Lock", "java.util.concurrent.locks.ReentrantReadWriteLock", "java.util.concurrent.locks.ReadWriteLock", "java.util.concurrent.locks.StampedLock", "kotlinx.coroutines.sync.Mutex");
  static final List<String> UNITS = List.of("NANOSECONDS", "MICROSECONDS", "MILLISECONDS", "SECONDS", "MINUTES", "HOURS", "DAYS");
  static final long[] NANOS = {1L, 1_000L, 1_000_000L, 1_000_000_000L, 60_000_000_000L, 3_600_000_000_000L, 86_400_000_000_000L};
  static String prim(JT t) { return PRIM.contains(t.n) ? t.n : BOX.get(t.n); }
  static boolean num(JT t) { String q = prim(t); return q != null && !q.equals("boolean") && !q.equals("void"); }
  static boolean integral(JT t) { String q = prim(t); return q != null && Set.of("int", "long", "short", "byte", "char").contains(q); }
  static boolean floating(JT t) { String q = prim(t); return "float".equals(q) || "double".equals(q); }
  static boolean map(JT t) { return MAPS.contains(t.n); }
  static boolean atomic(JT t) { return t.n.startsWith("java.util.concurrent.atomic.Atomic") || t.n.startsWith("kotlinx.atomicfu.Atomic"); }
  // The type an atomic holds.
  static JT held(JT t) {
    return switch (t.simple()) { case "AtomicInteger", "AtomicInt" -> new JT("int"); case "AtomicLong" -> new JT("long"); case "AtomicBoolean" -> new JT("boolean"); default -> t.arg(0); };
  }
  // An integer type's width, sign and name (the executor's IntTy); Kotlin's names where the reader is Kotlin's.
  static boolean kotlin = false;
  static Map<String, Object> ity(JT t) {
    String q = t == null ? null : prim(t);
    if (q == null) return null;
    return switch (q) {
      case "int" -> m("bits", 32, "signed", true, "name", kotlin ? "Int" : "int");
      case "long" -> m("bits", 64, "signed", true, "name", kotlin ? "Long" : "long");
      case "short" -> m("bits", 16, "signed", true, "name", kotlin ? "Short" : "short");
      case "byte" -> m("bits", 8, "signed", true, "name", kotlin ? "Byte" : "byte");
      case "char" -> m("bits", 16, "signed", false, "name", kotlin ? "Char" : "char");
      default -> null;
    };
  }
  // Binary numeric promotion: the type two operands are computed at.
  static JT promote(JT a, JT b) {
    if (floating(a) || floating(b)) return new JT("double");
    if ("long".equals(prim(a)) || "long".equals(prim(b))) return new JT("long");
    return new JT("int");
  }

  // An argument's type: a float's whole values are exact below 2^24 (a double's below 2^53, the rule's own bound), so a
  // float argument is one of those (the harness refuses to give one past them, as the rule does).
  static Map<String, Object> pstype(JT t, Env env) {
    if (t != null && "float".equals(prim(t))) { Map<String, Object> f = m("k", "int", "bits", 25, "signed", true); return t.nul ? m("k", "opt", "of", f) : f; }
    return stype(t, env);
  }
  // What a reader knows of the code's own types.
  interface Env { List<String> enumValues(String fq); String rec(String fq); }
  static Map<String, Object> stype(JT t, Env env) {
    if (t == null) return m("k", "opaque", "why", "a value of no type the reader resolved");
    if (t.nul && !t.is("java.util.Optional")) return m("k", "opt", "of", stype(t.nullable(false), env));
    String q = prim(t);
    if (q != null) {
      Map<String, Object> it = ity(t);
      if (it != null) return m("k", "int", "bits", it.get("bits"), "signed", it.get("signed"));
      return q.equals("boolean") ? m("k", "bool") : q.equals("void") ? m("k", "none") : m("k", "float");
    }
    if (t.is("java.lang.String", "java.lang.CharSequence")) return m("k", "str");
    if (t.is("java.util.Optional")) return m("k", "opt", "of", stype(t.arg(0), env));
    if (t.is("java.util.OptionalInt")) return m("k", "opt", "of", stype(new JT("int"), env));
    if (t.is("java.util.OptionalLong")) return m("k", "opt", "of", stype(new JT("long"), env));
    if (t.is("java.util.concurrent.TimeUnit")) return m("k", "choice", "values", UNITS, "enum", t.n);
    List<String> ev = env.enumValues(t.n);
    if (ev != null) return m("k", "choice", "values", ev, "enum", t.n);
    if (map(t)) return m("k", "map", "key", stype(t.arg(0), env), "val", stype(t.arg(1), env));
    if (atomic(t)) { Map<String, Object> h = new LinkedHashMap<>(stype(held(t), env)); h.put("atomic", t.simple()); return h; }
    if (LOCKS.contains(t.n)) return m("k", "lock");
    String r = env.rec(t.n);
    if (r != null) return m("k", "rec", "name", r);
    if (t.n.startsWith("java.util.") && (t.n.endsWith("List") || t.n.endsWith("Set") || t.n.endsWith("Queue") || t.n.endsWith("Deque") || t.n.equals("java.util.Collection"))) return m("k", "opaque", "why", "a " + t.simple() + " (collections but maps are outside the subset)");
    return m("k", "opaque", "why", "a " + t.simple() + " (a type of other code)");
  }

  // --- the library, lowered (a call the reader resolved to its declaring type) -----------------------------------------
  // A call: its declaring type and name, the receiver (null for a static one) with its type, the arguments with theirs,
  // the result's type, where it is and its text, and whether its value is used (a statement's isn't). The reader gives
  // a `pure` test (an argument read twice must read the same: no call in it).
  record Call(String owner, String name, Map<String, Object> recv, JT recvT, List<Map<String, Object>> args, List<JT> argT, JT out, String p, String text, boolean stmt, boolean pure) {}
  // Lowered: an expression (`x`), or statements (`ss`) for a call used as one; null where it isn't the library's.
  record Low(Map<String, Object> x, List<Object> ss) {}
  static Low ex(Map<String, Object> x) { return new Low(x, null); }
  static Low st(Object... ss) { return new Low(null, List.of(ss)); }

  // An operand at a type (Java's binary promotion made explicit: the executor computes at its operands' type).
  static Map<String, Object> at(Map<String, Object> v, JT from, JT to) {
    Map<String, Object> it = ity(to);
    if (it == null || (from != null && Objects.equals(prim(from), prim(to)))) return v;
    if ("int".equals(v.get("e"))) { Map<String, Object> c = new LinkedHashMap<>(v); c.put("ity", it); return c; }
    return x("as", (String) v.get("p"), "x", v, "ity", it);
  }
  static Map<String, Object> arith(String op, Map<String, Object> a, JT ta, Map<String, Object> b, JT tb, JT out, String ovf, String p, String text) {
    if (floating(out)) return x("bin", p, "op", op.equals("/") ? "//" : op, "x", a, "y", b, "text", text, "float", true);
    return x("bin", p, "op", op, "x", at(a, ta, out), "y", at(b, tb, out), "ovf", ovf, "text", text);
  }
  static Low lib(Call c) {
    String o = c.owner, n = c.name, p = c.p, t = c.text;
    List<Map<String, Object>> a = c.args;
    int na = a.size();
    JT a0 = na > 0 ? c.argT.get(0) : null;
    // Math: min and max at the result's type, abs wrapped as Java's (abs of MIN_VALUE is MIN_VALUE), exact arithmetic
    // trapping (an ArithmeticException), floorDiv and floorMod by a constant.
    if (o.equals("java.lang.Math") || o.equals("java.lang.StrictMath") || o.equals("kotlin.math.MathKt")) {
      switch (n) {
        case "min", "max", "minOf", "maxOf": if (na == 2) return ex(x("minmax", p, "op", n.startsWith("min") ? "min" : "max", "xs", List.of(at(a.get(0), a0, c.out), at(a.get(1), c.argT.get(1), c.out)), "ity", ity(c.out), "why", t + ": min or max of no integer type", "text", t)); break;
        case "abs": if (na == 1 && ity(c.out) != null) { Map<String, Object> v = at(a.get(0), a0, c.out); return ex(x("ite", p, "c", cmp("<", v, lit(0, c.out, p), p, t), "a", x("unop", p, "op", "-", "x", v), "b", v)); } break;
        case "addExact", "subtractExact", "multiplyExact": if (na == 2) return ex(arith(n.startsWith("add") ? "+" : n.startsWith("sub") ? "-" : "*", a.get(0), a0, a.get(1), c.argT.get(1), c.out, "trap", p, t)); break;
        case "incrementExact", "decrementExact": if (na == 1) return ex(arith(n.startsWith("inc") ? "+" : "-", a.get(0), a0, lit(1, c.out, p), c.out, c.out, "trap", p, t)); break;
        case "negateExact": if (na == 1) return ex(arith("-", lit(0, c.out, p), c.out, a.get(0), a0, c.out, "trap", p, t)); break;
        case "toIntExact": if (na == 1) return ex(arith("+", x("as", p, "x", a.get(0), "ity", ity(new JT("int"))), c.out, lit(0, c.out, p), c.out, c.out, "trap", p, t)); break;
        case "floorDiv", "floorMod": if (na == 2) return ex(x("as", p, "x", x("bin", p, "op", n.equals("floorDiv") ? "//" : "%", "x", a.get(0), "y", a.get(1), "text", t), "ity", ity(c.out))); break;
        case "clamp": if (na == 3) return ex(x("minmax", p, "op", "max", "xs", List.of(at(a.get(1), c.argT.get(1), c.out), x("minmax", p, "op", "min", "xs", List.of(at(a.get(0), a0, c.out), at(a.get(2), c.argT.get(2), c.out)), "ity", ity(c.out))), "ity", ity(c.out), "text", t)); break;
      }
      return null;
    }
    // Boxing and unboxing are the value; Objects.equals is ==.
    if ((BOX.containsKey(o) || o.equals("java.lang.Number")) && (n.endsWith("Value") && na == 0 && c.recv != null)) return ex(at(c.recv, c.recvT, c.out));
    if (BOX.containsKey(o) && n.equals("valueOf") && na == 1 && !"java.lang.String".equals(a0.n)) return ex(at(a.get(0), a0, c.out));
    if ((o.equals("java.util.Objects") && n.equals("equals") && na == 2)) return ex(cmp("==", a.get(0), a.get(1), p, t));
    if (o.equals("java.lang.String") && c.recv != null) {
      if (n.equals("equals") && na == 1) return ex(cmp("==", c.recv, a.get(0), p, t));
      if (n.equals("isEmpty") && na == 0) return ex(cmp("==", c.recv, str("", p), p, t));
    }
    if (o.equals("java.lang.Enum") && n.equals("ordinal") && na == 0) return ex(x("cast", p, "x", c.recv, "ty", m("k", "int", "bits", 32, "signed", true), "text", t));
    // Checks that throw: Objects.requireNonNull, Guava's Preconditions, Kotlin's check, require, error and their NotNull.
    if (o.equals("java.util.Objects") && n.equals("requireNonNull") && na >= 1) return ex(x("expect", p, "x", a.get(0), "text", t + " (a NullPointerException)"));
    if (o.equals("com.google.common.base.Preconditions") && (n.equals("checkArgument") || n.equals("checkState")) && na >= 1 && c.stmt)
      return st(s("if", p, "c", not(a.get(0), p), "then", List.of(fail(p, t + " (an Illegal" + (n.equals("checkState") ? "State" : "Argument") + "Exception)")), "else", List.of()));
    if (o.equals("com.google.common.base.Preconditions") && n.equals("checkNotNull") && na >= 1) return ex(x("expect", p, "x", a.get(0), "text", t + " (a NullPointerException)"));
    if (o.startsWith("kotlin.") && (n.equals("check") || n.equals("require")) && na >= 1 && c.stmt)
      return st(s("if", p, "c", not(a.get(0), p), "then", List.of(fail(p, t + " failed (an Illegal" + (n.equals("check") ? "State" : "Argument") + "Exception)")), "else", List.of()));
    if (o.startsWith("kotlin.") && (n.equals("checkNotNull") || n.equals("requireNotNull")) && na >= 1) return ex(x("expect", p, "x", a.get(0), "text", t + " (an Illegal" + (n.equals("checkNotNull") ? "State" : "Argument") + "Exception)"));
    if (o.startsWith("kotlin.") && n.equals("error") && na == 1 && c.stmt) return st(fail(p, t + " (an IllegalStateException)"));
    // The clock: the request's time (the harness's, through the check's rewrite of the call).
    if ((o.equals("java.lang.System") && (n.equals("currentTimeMillis") || n.equals("nanoTime"))) || (o.equals("java.time.Clock") && n.equals("millis")) || (o.equals("java.time.InstantSource") && n.equals("millis"))
        || (o.startsWith("kotlin.system.") && (n.equals("getTimeMillis") || n.equals("currentTimeMillis"))))
      return ex(x("clock", p, "text", t));
    // TimeUnit's conversions: the unit's factor, truncated (Java's toX truncates toward zero; its saturation at
    // Long's range is past the rule's ±2^53).
    if (o.equals("java.util.concurrent.TimeUnit") && c.recv != null && n.startsWith("to") && na == 1 && !n.equals("toChronoUnit") && c.pure) {
      int to = switch (n) { case "toNanos" -> 0; case "toMicros" -> 1; case "toMillis" -> 2; case "toSeconds" -> 3; case "toMinutes" -> 4; case "toHours" -> 5; case "toDays" -> 6; default -> -1; };
      if (to < 0) return null;
      JT lt = new JT("long");
      Map<String, Object> d = at(a.get(0), a0, lt), acc = null;
      for (int u = UNITS.size() - 1; u >= 0; u--) {
        Map<String, Object> v = u == to ? d : u > to ? x("bin", p, "op", "*", "x", d, "y", lit(NANOS[u] / NANOS[to], lt, p), "ovf", "sat", "text", t) : x("bin", p, "op", "/", "x", d, "y", lit(NANOS[to] / NANOS[u], lt, p), "ovf", "wrap", "text", t);
        acc = acc == null ? v : x("ite", p, "c", cmp("==", c.recv, str(UNITS.get(u), p), p, t), "a", v, "b", acc);
      }
      return ex(acc);
    }
    // Optional: empty is None, of is Some, isPresent and isEmpty test it, get and orElseThrow unwrap it (a failure where
    // it is empty: NoSuchElementException), orElse gives a default.
    if (o.equals("java.util.Optional") || o.equals("java.util.OptionalInt") || o.equals("java.util.OptionalLong")) {
      switch (n) {
        case "empty": return ex(x("none", p));
        case "of": return ex(x("some", p, "x", a.get(0)));
        case "ofNullable": return ex(a.get(0));
        case "isPresent": return ex(x("is", p, "x", c.recv, "k", "some", "text", t));
        case "isEmpty": return ex(x("is", p, "x", c.recv, "k", "none", "text", t));
        case "get", "getAsInt", "getAsLong", "orElseThrow": if (na == 0) return ex(x("expect", p, "x", c.recv, "text", t + " (a NoSuchElementException)")); break;
        case "orElse": return ex(x("opt_or", p, "x", c.recv, "d", a.get(0)));
      }
      return null;
    }
    // Maps: get (None where the key isn't held), getOrDefault, containsKey, put and remove (their old values), a put
    // as a statement one key written.
    if (MAPS.contains(o) || o.equals("kotlin.collections.MapsKt") || o.startsWith("kotlin.collections.Map") || o.startsWith("kotlin.collections.MutableMap")) {
      Map<String, Object> mm = c.recv != null ? c.recv : na > 0 ? a.get(0) : null;
      List<Map<String, Object>> rest = c.recv != null ? a : a.subList(1, na);
      if (mm == null) return null;
      Map<String, Object> getf = get(mm, "get", p, t);
      switch (n) {
        case "get": if (rest.size() == 1) return ex(call(getf, rest, p, t)); break;
        case "getOrDefault": if (rest.size() == 2) return ex(call(getf, rest, p, t)); break;
        case "containsKey": if (rest.size() == 1) return ex(cmp("in", rest.get(0), mm, p, t)); break;
        case "getValue": if (rest.size() == 1) return ex(x("idx", p, "x", mm, "i", rest.get(0), "text", t + " (a NoSuchElementException where the key isn't held)")); break;
        case "put", "set": if (rest.size() == 2) return c.stmt ? st(s("set", p, "to", x("idx", p, "x", mm, "i", rest.get(0), "text", t), "x", rest.get(1))) : ex(call(get(mm, "insert", p, t), rest, p, t)); break;
        case "remove": if (rest.size() == 1) return ex(call(get(mm, "remove", p, t), rest, p, t)); break;
      }
      return ex(no(p, t + ": " + n + " of a map (the subset reads get, getOrDefault, containsKey, put and remove)"));
    }
    // The atomics: a read, a write, a read-modify-write (each the field it is: one request one step).
    if (atomic(c.recvT) && c.recv != null) {
      Map<String, Object> pl = c.recv;
      JT h = held(c.recvT);
      Map<String, Object> one = lit(1, h, p);
      switch (n) {
        case "get", "getPlain", "getAcquire", "getOpaque", "intValue", "longValue", "getValue": if (na == 0) return ex(pl); break;
        case "set", "lazySet", "setPlain", "setRelease", "setOpaque", "setValue": if (na == 1) return c.stmt ? st(s("set", p, "to", pl, "x", at(a.get(0), a0, h))) : ex(x("rmw", p, "op", "store", "place", pl, "args", List.of(a.get(0)), "text", t)); break;
        case "getAndSet": if (na == 1) return ex(x("rmw", p, "op", "swap", "place", pl, "args", List.of(at(a.get(0), a0, h)), "text", t)); break;
        case "getAndIncrement", "getAndDecrement": if (na == 0) return ex(x("rmw", p, "op", n.endsWith("Increment") ? "fetch_add" : "fetch_sub", "place", pl, "args", List.of(one), "text", t)); break;
        case "incrementAndGet", "decrementAndGet": if (na == 0) return ex(arith(n.startsWith("inc") ? "+" : "-", x("rmw", p, "op", n.startsWith("inc") ? "fetch_add" : "fetch_sub", "place", pl, "args", List.of(one), "text", t), h, one, h, h, "wrap", p, t)); break;
        case "getAndAdd": if (na == 1) return ex(x("rmw", p, "op", "fetch_add", "place", pl, "args", List.of(at(a.get(0), a0, h)), "text", t)); break;
        case "addAndGet": if (na == 1 && c.pure) return ex(arith("+", x("rmw", p, "op", "fetch_add", "place", pl, "args", List.of(at(a.get(0), a0, h)), "text", t), h, a.get(0), a0, h, "wrap", p, t)); break;
        case "compareAndSet", "weakCompareAndSet", "weakCompareAndSetPlain", "weakCompareAndSetVolatile", "compareAndExchange":
          if (na == 2) { Map<String, Object> r = x("rmw", p, "op", "compare_exchange", "place", pl, "args", List.of(at(a.get(0), a0, h), at(a.get(1), c.argT.get(1), h)), "text", t); return ex(n.equals("compareAndExchange") ? x("unwrap", p, "x", r, "k", "ok") : x("is", p, "x", r, "k", "ok", "text", t)); }
          break;
      }
      return ex(no(p, t + ": " + c.recvT.simple() + "." + n + " (the subset reads get, set, getAndSet, the increments and adds, compareAndSet)"));
    }
    return null;
  }

  // --- what the caller's boundary inference reads ----------------------------------------------------------------------
  // A declaration's annotations (DI ones among them) and its `// gdp:` tags, as the reader saw them.
  static final Set<String> DI = Set.of("Autowired", "Inject", "Resource", "Value", "Qualifier", "Named", "Lazy", "MockBean", "Bean", "Component", "Service", "Repository", "Configuration");
  static Map<String, Object> anno(String name, String fq, String text) { return m("name", name, "fq", fq, "text", text, "di", DI.contains(name) ? true : null); }
  // `// gdp: ...` comments of a file, by the line they are on (a tag names the declaration or call on its line, or on
  // the next line that has code).
  static TreeMap<Integer, String> tags(String src) {
    TreeMap<Integer, String> out = new TreeMap<>();
    String[] lines = src.split("\n", -1);
    for (int i = 0; i < lines.length; i++) {
      int k = lines[i].indexOf("gdp:");
      if (k < 0) continue;
      String before = lines[i].substring(0, k).trim();
      if (!(before.endsWith("//") || before.endsWith("/*") || before.endsWith("*"))) continue;
      String t = lines[i].substring(k + 4).replace("*/", "").trim();
      int at = i + 1;
      String code = lines[i].substring(0, lines[i].indexOf(before.endsWith("//") ? "//" : before.endsWith("/*") ? "/*" : "*")).trim();
      if (code.isEmpty()) { int j = i + 1; while (j < lines.length && (lines[j].trim().isEmpty() || lines[j].trim().startsWith("//") || lines[j].trim().startsWith("@"))) j++; at = j + 1; }
      out.merge(at, t, (x, y) -> x + "; " + y);
    }
    return out;
  }
}
