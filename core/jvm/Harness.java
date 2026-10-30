// The JVM side of the extractor's check (core/extract-step.ts's checkStep), for Java and Kotlin alike: the class
// loaded as compiled from the code (or as the project ships it), its object made, set to a state, called with the
// rule's requests and read back by reflection, one JSON line a request over two named pipes. The clock and an answered
// call are the request's (the check's copy of the code reads them through gdp.Rt). Atomics, Optional and Kotlin's
// nullable types are read and set through what they hold; a map's cells through the map the object already has.
//
//   java -cp <tools>:<the code's classes> gdp.jvm.Harness <in-fifo> <out-fifo>
package gdp.jvm;

import java.io.*;
import java.lang.reflect.*;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.atomic.*;
import static gdp.jvm.Jvm.*;

public final class Harness {
  static Map<?, ?> S;
  static Class<?> cls;
  static ClassLoader loader;
  static final Map<Long, Object> OBJS = new HashMap<>();
  static Map<?, ?> CUR = Map.of();

  public static void main(String[] argv) throws Exception {
    BufferedReader in = new BufferedReader(new InputStreamReader(new FileInputStream(argv[0]), StandardCharsets.UTF_8));
    Writer out = new OutputStreamWriter(new FileOutputStream(argv[1]), StandardCharsets.UTF_8);
    gdp.Rt.ANSWER = (k, c) -> { Object a = CUR.get(k); return a == null || ((Map<?, ?>) a).containsKey("none") ? null : conv(((Map<?, ?>) a).get("in"), c, null); };
    for (String line; (line = in.readLine()) != null; ) {
      Map<?, ?> req = (Map<?, ?>) parse(line);
      Object res;
      try { res = handle(req); } catch (Throwable e) { res = m("error", cut(e.toString(), 500)); }
      out.write(json(res)); out.write('\n'); out.flush();
    }
  }
  static String cut(String s, int n) { return s.length() <= n ? s : s.substring(0, n); }
  static String err(Throwable e) { Throwable c = e instanceof InvocationTargetException i && i.getCause() != null ? i.getCause() : e; return cut(c.getClass().getSimpleName() + ": " + c.getMessage(), 300); }
  static long now(Map<?, ?> req) { Object n = req.get("now"); return n == null ? 0 : ((Number) n).longValue(); }

  static Object handle(Map<?, ?> req) throws Exception {
    String op = (String) req.get("op");
    if (op.equals("new") || op.equals("at")) gdp.Rt.NOW = now(req);
    switch (op) {
      case "hello": {
        S = req;
        List<File> cp = new ArrayList<>();
        for (Object f : (List<?>) req.get("cp")) cp.add(new File((String) f));
        URL[] urls = new URL[cp.size()];
        for (int i = 0; i < urls.length; i++) urls[i] = cp.get(i).toURI().toURL();
        loader = new URLClassLoader(urls, Harness.class.getClassLoader());
        cls = Class.forName((String) req.get("jcls"), false, loader);
        return m("ok", true);
      }
      case "new": try { return m("id", make((List<?>) req.get("a"))); } catch (Throwable e) { return m("err", err(e)); }
      case "at":
        try { long i = make((List<?>) req.get("a")); setState(OBJS.get(i), (Map<?, ?>) req.get("state")); return m("id", i); }
        catch (Throwable e) { return m("bad", err(e)); }
      case "get": return m("state", stateOf(OBJS.get(((Number) req.get("id")).longValue())));
      case "call": return call(req);
      case "coverage": return m("hit", List.of());
      default: return m("error", "no op " + op);
    }
  }

  // --- classes and members --------------------------------------------------------------------------------------------
  static Class<?> type(String n) throws ClassNotFoundException {
    return switch (n) { case "int" -> int.class; case "long" -> long.class; case "short" -> short.class; case "byte" -> byte.class; case "char" -> char.class; case "boolean" -> boolean.class; case "float" -> float.class; case "double" -> double.class; default -> Class.forName(n, false, loader); };
  }
  static Class<?>[] types(List<?> ns) throws ClassNotFoundException { Class<?>[] out = new Class<?>[ns.size()]; for (int i = 0; i < out.length; i++) out[i] = type((String) ns.get(i)); return out; }
  static Field field(Class<?> c, String n) throws NoSuchFieldException {
    for (Class<?> k = c; k != null; k = k.getSuperclass()) try { Field f = k.getDeclaredField(n); f.setAccessible(true); return f; } catch (NoSuchFieldException e) { /* the superclass's */ }
    throw new NoSuchFieldException(n);
  }
  // A method by its JVM name (Kotlin's internal ones are name$module) and parameter types, in the class or a superclass.
  static Method method(Map<?, ?> sig) throws Exception {
    String n = (String) sig.get("name");
    Class<?>[] ps = types((List<?>) sig.get("params"));
    for (Class<?> k = cls; k != null; k = k.getSuperclass())
      for (Method m : k.getDeclaredMethods()) if ((m.getName().equals(n) || m.getName().startsWith(n + "$")) && !m.isSynthetic() && Arrays.equals(m.getParameterTypes(), ps)) { m.setAccessible(true); return m; }
    throw new NoSuchMethodException(n + Arrays.toString(ps));
  }

  // --- values ---------------------------------------------------------------------------------------------------------
  static Object conv(Object v, Class<?> c, Type g) {
    if (c == Optional.class) return v == null ? Optional.empty() : Optional.of(conv(v, g instanceof ParameterizedType pt ? raw(pt.getActualTypeArguments()[0]) : Object.class, null));
    if (v == null) return c.isPrimitive() ? conv(0L, c, null) : null;
    if (c == int.class || c == Integer.class) return (int) fit(v, Integer.MIN_VALUE, Integer.MAX_VALUE);
    if (c == long.class || c == Long.class) return num(v).longValue();
    if (c == short.class || c == Short.class) return (short) fit(v, Short.MIN_VALUE, Short.MAX_VALUE);
    if (c == byte.class || c == Byte.class) return (byte) fit(v, Byte.MIN_VALUE, Byte.MAX_VALUE);
    if (c == char.class || c == Character.class) return (char) fit(v, 0, 65535);
    if (c == double.class || c == Double.class) { double d = num(v).doubleValue(); if (Math.abs(d) > 9.007199254740992E15) throw new IllegalArgumentException("a double past 2^53 (the subset's floats are whole and exact)"); return d; }
    if (c == float.class || c == Float.class) { double d = num(v).doubleValue(); if (d < -16777216 || d > 16777215) throw new IllegalArgumentException("a float outside [-2^24, 2^24) (the subset's floats are whole and exact)"); return (float) d; }
    if (c == boolean.class || c == Boolean.class) return v;
    if (c.isEnum()) return enumOf(c, (String) v);
    if (c == String.class || c == CharSequence.class) return String.valueOf(v);
    if (c == Object.class) return v;
    throw new IllegalArgumentException("a " + c.getSimpleName() + " from " + v);
  }
  // An integer within its type (one outside it isn't given: the rule refuses it too).
  static long fit(Object v, long lo, long hi) { long n = num(v).longValue(); if (n < lo || n > hi) throw new IllegalArgumentException(n + " is outside the type's range"); return n; }
  @SuppressWarnings({"unchecked", "rawtypes"}) static Object enumOf(Class<?> c, String n) { return Enum.valueOf((Class) c, n); }
  static Number num(Object v) { return v instanceof Number n ? n : v instanceof String s ? (Number) Long.parseLong(s) : (Number) 0L; }
  static Class<?> raw(Type t) { return t instanceof Class<?> c ? c : t instanceof ParameterizedType p ? raw(p.getRawType()) : Object.class; }
  // An argument from its spec: an input, None, an inert value (an interface's proxy that does nothing), a record.
  static Object build(Object spec0, Class<?> c, Type g) throws Exception {
    Map<?, ?> spec = (Map<?, ?>) spec0;
    if (spec.containsKey("in")) return conv(spec.get("in"), c, g);
    if (spec.containsKey("none")) return c == Optional.class ? Optional.empty() : c.isPrimitive() ? conv(0L, c, null) : null;
    if (spec.containsKey("inert")) return inert(c);
    if (spec.containsKey("rec")) return record(c, (Map<?, ?>) spec.get("f"));
    throw new IllegalArgumentException("an argument spec " + json(spec));
  }
  static Object inert(Class<?> c) {
    if (c.isPrimitive()) return conv(0L, c, null);
    if (!c.isInterface()) return null;
    return Proxy.newProxyInstance(loader, new Class<?>[]{c}, (o, m, a) -> m.getName().equals("toString") ? "inert" : m.getName().equals("hashCode") ? 0 : m.getName().equals("equals") ? o == a[0] : m.getReturnType().isPrimitive() && m.getReturnType() != void.class ? conv(0L, m.getReturnType(), null) : null);
  }
  // A record of the code's own: a Java record by its canonical constructor, another class made without one and its
  // fields set (every other field its zero).
  static Object record(Class<?> c, Map<?, ?> f) throws Exception {
    if (c.isRecord()) {
      RecordComponent[] rc = c.getRecordComponents();
      Object[] args = new Object[rc.length];
      Class<?>[] ts = new Class<?>[rc.length];
      for (int i = 0; i < rc.length; i++) { ts[i] = rc[i].getType(); Object s = f.get(rc[i].getName()); args[i] = s == null ? conv(null, ts[i], null) : s instanceof Map<?, ?> ? build(s, ts[i], rc[i].getGenericType()) : conv(s, ts[i], rc[i].getGenericType()); }
      Constructor<?> k = c.getDeclaredConstructor(ts); k.setAccessible(true); return k.newInstance(args);
    }
    Field uf = Class.forName("sun.misc.Unsafe").getDeclaredField("theUnsafe"); uf.setAccessible(true);
    Object u = uf.get(null);
    Object o = u.getClass().getMethod("allocateInstance", Class.class).invoke(u, c);
    for (Map.Entry<?, ?> e : f.entrySet()) { Field fd = field(c, (String) e.getKey()); fd.set(o, e.getValue() instanceof Map<?, ?> ? build(e.getValue(), fd.getType(), fd.getGenericType()) : conv(e.getValue(), fd.getType(), fd.getGenericType())); }
    return o;
  }
  // A value as the check reads it: a number as its decimal text, a string or an enum's name, a boolean, null.
  static String enc(Object v) {
    if (v instanceof Double || v instanceof Float) { double d = ((Number) v).doubleValue(); return d == Math.floor(d) && Math.abs(d) < 9.2e18 ? Long.toString((long) d) : "f:" + d; }
    if (v instanceof Number n) return Long.toString(n.longValue());
    if (v instanceof Character ch) return Integer.toString(ch);
    return "?:" + (v == null ? "null" : v.getClass().getSimpleName());
  }
  static Object tag(Object v) {
    if (v instanceof Optional<?> o) return o.isPresent() ? tag(o.get()) : null;
    if (v == null || v instanceof Boolean) return v;
    if (v instanceof Number || v instanceof Character) return m("n", enc(v));
    if (v instanceof String s) return m("s", s);
    if (v instanceof Enum<?> e) return m("s", e.name());
    return m("o", v.getClass().getSimpleName());
  }

  // --- the state ------------------------------------------------------------------------------------------------------
  // A leaf's holder (the object whose field it is) and its field.
  static Object holder(Object o, List<?> path) throws Exception { for (int i = 0; i < path.size() - 1; i++) o = field(o.getClass(), (String) path.get(i)).get(o); return o; }
  // What a field holds: an atomic's value, an Optional's (null where empty).
  static Object read(Object h, String f) throws Exception {
    Object v = field(h.getClass(), f).get(h);
    if (v instanceof AtomicInteger a) return a.get();
    if (v instanceof AtomicLong a) return a.get();
    if (v instanceof AtomicBoolean a) return a.get();
    if (v instanceof AtomicReference<?> a) return a.get();
    if (v instanceof Optional<?> o) return o.orElse(null);
    return v;
  }
  @SuppressWarnings("unchecked") static void write(Object h, String f, Object v, Map<?, ?> leaf) throws Exception {
    Field fd = field(h.getClass(), f);
    Object cur = fd.get(h);
    Type g = fd.getGenericType();
    if (cur instanceof AtomicInteger a) { a.set((int) fit(v, Integer.MIN_VALUE, Integer.MAX_VALUE)); return; }
    if (cur instanceof AtomicLong a) { a.set(num(v).longValue()); return; }
    if (cur instanceof AtomicBoolean a) { a.set((Boolean) v); return; }
    if (cur instanceof AtomicReference<?> a) { ((AtomicReference<Object>) a).set(v == null ? null : conv(v, g instanceof ParameterizedType pt ? raw(pt.getActualTypeArguments()[0]) : Object.class, null)); return; }
    fd.set(h, conv(v, fd.getType(), g));
  }
  static Map<String, Object> stateOf(Object obj) throws Exception {
    Map<String, Object> s = new LinkedHashMap<>();
    for (Object l0 : (List<?>) S.get("leaves")) {
      Map<?, ?> l = (Map<?, ?>) l0;
      String k = (String) l.get("kind");
      if (k.equals("frame")) continue;
      List<?> path = (List<?>) l.get("path");
      Object h = holder(obj, path), v = read(h, (String) path.get(path.size() - 1));
      switch (k) {
        case "none" -> s.put((String) l.get("name"), v == null);
        case "num" -> s.put((String) l.get("name"), v == null ? "0" : enc(v));
        case "str", "choice" -> s.put((String) l.get("name"), v == null ? "" : v instanceof Enum<?> e ? e.name() : v.toString());
        case "bool" -> s.put((String) l.get("name"), v == null ? false : v);
        case "map" -> {
          Map<String, Object> cells = new LinkedHashMap<>();
          List<?> fs = (List<?>) l.get("fields");
          for (Map.Entry<?, ?> e : ((Map<?, ?>) v).entrySet()) {
            Object x = e.getValue();
            Map<String, Object> c = new LinkedHashMap<>();
            if (fs == null) c.put("value", x instanceof Boolean ? x : enc(x));
            else for (Object f0 : fs) { String f = (String) ((Map<?, ?>) f0).get("name"); Object y = read(x, f); c.put(f, y instanceof Boolean ? y : y instanceof Enum<?> en ? en.name() : enc(y)); }
            cells.put(e.getKey() instanceof Enum<?> en ? en.name() : String.valueOf(e.getKey()), c);
          }
          s.put((String) l.get("name"), cells);
        }
        default -> { }
      }
    }
    return s;
  }
  @SuppressWarnings("unchecked") static void setState(Object obj, Map<?, ?> st) throws Exception {
    List<?> leaves = (List<?>) S.get("leaves");
    for (Object l0 : leaves) {
      Map<?, ?> l = (Map<?, ?>) l0;
      String k = (String) l.get("kind");
      if (k.equals("frame") || k.equals("none")) continue;
      List<?> path = (List<?>) l.get("path");
      Object h = holder(obj, path), v = st.get(l.get("name"));
      String f = (String) path.get(path.size() - 1);
      if (k.equals("map")) {
        Field fd = field(h.getClass(), f);
        Map<Object, Object> mp = (Map<Object, Object>) fd.get(h);
        Type[] ka = fd.getGenericType() instanceof ParameterizedType pt ? pt.getActualTypeArguments() : new Type[]{Object.class, Object.class};
        mp.clear();
        List<?> fs = (List<?>) l.get("fields");
        for (Map.Entry<?, ?> e : ((Map<?, ?>) v).entrySet()) {
          Object key = conv("num".equals(l.get("key")) ? (Object) Long.parseLong((String) e.getKey()) : e.getKey(), raw(ka[0]), null);
          Map<?, ?> c = (Map<?, ?>) e.getValue();
          mp.put(key, fs == null ? conv(c.get("value"), raw(ka[1]), null) : record(raw(ka[1]), c));
        }
        continue;
      }
      write(h, f, v, l);
    }
    for (Object l0 : leaves) {
      Map<?, ?> l = (Map<?, ?>) l0;
      if (!"none".equals(l.get("kind")) || !Boolean.TRUE.equals(st.get(l.get("name")))) continue;
      List<?> path = (List<?>) l.get("path");
      Object h = holder(obj, path);
      String f = (String) path.get(path.size() - 1);
      Field fd = field(h.getClass(), f);
      if (fd.get(h) instanceof AtomicReference<?> a) ((AtomicReference<Object>) a).set(null);
      else fd.set(h, fd.getType() == Optional.class ? Optional.empty() : null);
    }
  }
  // The fields the rule leaves out, as they are (each must be as it was after a call).
  static Map<String, String> frames(Object obj) {
    Map<String, String> out = new LinkedHashMap<>();
    for (Object l0 : (List<?>) S.get("leaves")) {
      Map<?, ?> l = (Map<?, ?>) l0;
      if (!"frame".equals(l.get("kind")) || l.get("cls") != null) continue;
      List<?> path = (List<?>) l.get("path");
      try {
        Object h = holder(obj, path), v = field(h.getClass(), (String) path.get(path.size() - 1)).get(h);
        String txt = v == null ? "null" : v.getClass().isArray() ? Arrays.deepToString(new Object[]{v}) : v instanceof Collection<?> || v instanceof Map<?, ?> || v instanceof Number || v instanceof String || v instanceof Boolean ? v.toString() : v.getClass().getName();
        out.put(String.join(".", path.stream().map(String::valueOf).toList()), System.identityHashCode(v) + ":" + txt);
      } catch (Exception e) { /* unread */ }
    }
    return out;
  }

  // --- requests -------------------------------------------------------------------------------------------------------
  static long make(List<?> args) throws Exception {
    Map<?, ?> ctor = (Map<?, ?>) S.get("jctor");
    Class<?>[] ts = types((List<?>) ctor.get("params"));
    Constructor<?> k = cls.getDeclaredConstructor(ts);
    k.setAccessible(true);
    Type[] gs = k.getGenericParameterTypes();
    Object[] a = new Object[ts.length];
    for (int i = 0; i < ts.length; i++) a[i] = i < args.size() ? build(((List<?>) args.get(i)).get(1), ts[i], i < gs.length ? gs[i] : ts[i]) : inert(ts[i]);
    Object o = k.newInstance(a);
    long id = OBJS.size() + 1;
    OBJS.put(id, o);
    return id;
  }
  static Object call(Map<?, ?> req) throws Exception {
    long id = ((Number) req.get("id")).longValue();
    Object obj = OBJS.get(id);
    gdp.Rt.NOW = now(req);
    CUR = req.get("answers") == null ? Map.of() : (Map<?, ?>) req.get("answers");
    String key = (String) req.get("m");
    Map<?, ?> sig = (Map<?, ?>) ((Map<?, ?>) S.get("methods")).get(key);
    Method m = method(sig);
    Class<?>[] ts = m.getParameterTypes();
    Type[] gs = m.getGenericParameterTypes();
    List<?> specs = (List<?>) req.get("a");
    Object[] a = new Object[ts.length];
    try { for (int i = 0; i < ts.length; i++) a[i] = i < specs.size() ? build(((List<?>) specs.get(i)).get(1), ts[i], gs[i]) : inert(ts[i]); }
    catch (Exception e) { return m("bad", err(e)); }
    Map<String, String> before = frames(obj);
    Map<String, Object> snap = Boolean.TRUE.equals(S.get("discard")) ? stateOf(obj) : null;
    Object out = null;
    String err = null;
    try { out = m.invoke(Modifier.isStatic(m.getModifiers()) ? null : obj, a); } catch (InvocationTargetException e) { err = err(e); }
    if (err != null && snap != null) setState(obj, snap);
    // A method returning the object's next value (an immutable class's step): the object is that value.
    if (err == null && ((List<?>) S.get("reducers")).contains(key) && cls.isInstance(out)) { OBJS.put(id, out); obj = out; out = null; }
    Map<String, String> after = frames(obj);
    for (Map.Entry<String, String> e : before.entrySet()) if (!e.getValue().equals(after.get(e.getKey())) && !((List<?>) S.get("reducers")).contains(key)) return m("frame", e.getKey());
    Map<String, Object> res = m("out", tag(out));
    if (err != null) res.put("err", err);
    return res;
  }
}
