// The extractor's Kotlin reader (core/extract-jvm.ts): a class read through the Kotlin compiler's own parser (its PSI,
// from the kotlin-compiler.jar of the kotlinc installed) and lowered into the shared step IR through the JVM layer the
// Java reader uses (core/jvm/Jvm.java: one type per JVM type, the library's calls lowered alike). The PSI is syntax:
// the types are the code's own declarations (Kotlin states a property's and a parameter's), a local's from its
// initializer, an expression's from its parts. Kotlin's semantics as the IR's operations: Int and Long wrap, a nullable
// type is an option (?:, !!, ?.let, smart casts), when is a chain of ifs, if and when as values are pushed into their
// branches where they return, the standard library's scope functions (let, also, run, apply, takeIf, takeUnless) are
// inlined, check/require/error throw, @Synchronized, synchronized and withLock make the step atomic, a data class's
// copy is an update and a method of an immutable class returning its next value is a step to it.
//
//   java -cp <tools>:<kotlin-compiler.jar>:<kotlin-stdlib.jar> gdp.jvm.KtReader '{"root": <dir>, "file": <file>, "names": ["Class"]}'
package gdp.jvm;

import com.intellij.openapi.util.Disposer;
import com.intellij.psi.PsiElement;
import com.intellij.psi.tree.IElementType;
import java.io.File;
import java.nio.file.*;
import java.util.*;
import org.jetbrains.kotlin.KtNodeTypes;
import org.jetbrains.kotlin.cli.jvm.compiler.*;
import org.jetbrains.kotlin.config.*;
import org.jetbrains.kotlin.lexer.KtTokens;
import org.jetbrains.kotlin.psi.*;
import static gdp.jvm.Jvm.*;

public final class KtReader implements Jvm.Env {
  record X(Map<String, Object> ir, JT t) {}
  // A lowering's context: the statements an expression needs before it (a scope function's), the locals' types, the
  // names the lambda's `it` and `this` stand for.
  static final class Ctx {
    final List<Object> pre; final Map<String, JT> locals; final int cond; final boolean init;
    Ctx(List<Object> pre, Map<String, JT> locals, int cond, boolean init) { this.pre = pre; this.locals = locals; this.cond = cond; this.init = init; }
    Ctx under() { return new Ctx(pre, locals, cond + 1, init); }
    Ctx fresh() { return new Ctx(new ArrayList<>(), locals, cond, init); }
    Ctx scope() { return new Ctx(pre, new HashMap<>(locals), cond, init); }
  }
  KtFile file; String src, base, pkg;
  int[] lines;
  final Map<String, KtClassOrObject> classes = new LinkedHashMap<>();
  final Map<String, String> imports = new HashMap<>();
  final List<String> stars = new ArrayList<>(List.of("kotlin.", "kotlin.collections.", "kotlin.comparisons.", "kotlin.ranges.", "kotlin.text.", "java.lang.", "kotlin.jvm."));
  final Map<String, Object> recs = new LinkedHashMap<>(), funcs = new LinkedHashMap<>(), jvm = new LinkedHashMap<>();
  final List<Object> rewrites = new ArrayList<>();
  final List<String> reducers = new ArrayList<>();
  KtClassOrObject self;
  String selfName;
  TreeMap<Integer, String> tags;
  int tmp = 0;

  public static void main(String[] argv) throws Exception {
    Map<?, ?> req = (Map<?, ?>) parse(argv[0]);
    Jvm.kotlin = true;
    System.out.println(json(new KtReader().read(req)));
  }
  static KtPsiFactory factory() throws Exception {
    CompilerConfiguration cfg = new CompilerConfiguration();
    cfg.put(CommonConfigurationKeys.MESSAGE_COLLECTOR_KEY, org.jetbrains.kotlin.cli.common.messages.MessageCollector.Companion.getNONE());
    // (Kotlin 2.2 and later want an extension storage registered; earlier ones have no such key)
    try {
      Class<?> k = Class.forName("org.jetbrains.kotlin.cli.FrontendConfigurationKeysKt"), st = Class.forName("org.jetbrains.kotlin.compiler.plugin.CompilerPluginRegistrar$ExtensionStorage");
      k.getMethod("setExtensionsStorage", CompilerConfiguration.class, st).invoke(null, cfg, st.getConstructor().newInstance());
    } catch (ClassNotFoundException | NoSuchMethodException e) { /* an older compiler */ }
    KotlinCoreEnvironment env = KotlinCoreEnvironment.createForProduction(Disposer.newDisposable(), cfg, EnvironmentConfigFiles.JVM_CONFIG_FILES);
    return new KtPsiFactory(env.getProject(), false);
  }

  Map<String, Object> read(Map<?, ?> req) throws Exception {
    String path = (String) req.get("file"), root = (String) req.get("root");
    src = Files.readString(Path.of(path));
    base = new File(path).getName();
    KtPsiFactory f = factory();
    file = f.createFile(base, src);
    pkg = file.getPackageFqName().asString();
    List<Integer> ls = new ArrayList<>(List.of(0));
    for (int i = 0; i < src.length(); i++) if (src.charAt(i) == '\n') ls.add(i + 1);
    lines = ls.stream().mapToInt(Integer::intValue).toArray();
    tags = tags(src);
    for (KtImportDirective im : file.getImportDirectives()) {
      if (im.getImportedFqName() == null) continue;
      String q = im.getImportedFqName().asString();
      if (im.isAllUnder()) stars.add(q + ".");
      else imports.put(im.getAliasName() != null ? im.getAliasName() : q.substring(q.lastIndexOf('.') + 1), q);
    }
    index(file.getDeclarations(), pkg.isEmpty() ? "" : pkg + ".", "");
    // (the other files of the file's directory: their classes and enums, by name)
    File[] sibs = new File(path).getAbsoluteFile().getParentFile().listFiles((d, n) -> n.endsWith(".kt") && !n.equals(base));
    for (File s : sibs == null ? new File[0] : sibs) { try { KtFile o = f.createFile(s.getName(), Files.readString(s.toPath())); String op = o.getPackageFqName().asString(); index(o.getDeclarations(), op.isEmpty() ? "" : op + ".", ""); } catch (Exception e) { /* unread */ } }
    Map<String, Object> out = m("lang", "kotlin", "file", base, "path", new File(path).getAbsolutePath(), "module", pkg, "root", new File(root).getAbsolutePath());
    List<Object> entries = new ArrayList<>();
    for (Object n : (List<?>) req.get("names")) {
      String key = null;
      for (String k : classes.keySet()) { String dotted = k.replace('$', '.'); if (dotted.equals(n) || dotted.endsWith("." + n)) { key = k; break; } }
      entries.add(key == null ? m("k", "missing", "name", n) : m("k", "class", "rec", entry(key)));
    }
    out.put("entries", entries); out.put("recs", recs); out.put("funcs", funcs);
    Map<Object, Object> once = new LinkedHashMap<>();
    for (Object r : rewrites) once.putIfAbsent(((Map<?, ?>) r).get("span"), r);
    jvm.put("rewrites", new ArrayList<>(once.values())); jvm.put("reducers", reducers);
    out.put("jvm", jvm);
    return out;
  }
  void index(List<KtDeclaration> ds, String prefix, String outer) {
    for (KtDeclaration d : ds) if (d instanceof KtClassOrObject c && c.getName() != null) {
      String bin = prefix + outer + c.getName();
      classes.putIfAbsent(bin, c);
      if (c.getBody() != null) index(c.getBody().getDeclarations(), prefix, outer + c.getName() + "$");
    }
  }
  String binOf(KtClassOrObject c) { for (Map.Entry<String, KtClassOrObject> e : classes.entrySet()) if (e.getValue() == c) return e.getKey(); return c.getName(); }

  // --- positions ---------------------------------------------------------------------------------------------------------
  int line(int off) { int i = Arrays.binarySearch(lines, off); return i >= 0 ? i + 1 : -i - 1; }
  String where(PsiElement e) { int o = e.getTextRange().getStartOffset(), l = line(o); return base + ":" + l + ":" + (o - lines[l - 1] + 1); }
  String zero() { return base + ":0:0"; }
  static String text(PsiElement e) { String x = e.getText().replaceAll("\\s+", " "); return x.length() <= 60 ? x : x.substring(0, 57) + "..."; }
  List<Object> span(PsiElement e) { return List.of(e.getTextRange().getStartOffset(), e.getTextRange().getEndOffset()); }
  String tag(PsiElement e) { int l0 = line(e.getTextRange().getStartOffset()), l1 = line(e.getTextRange().getEndOffset()); var h = tags.subMap(l0, true, Math.max(l0, Math.min(l1, l0 + 1)), true); return h.isEmpty() ? null : String.join("; ", h.values()); }

  // --- types ---------------------------------------------------------------------------------------------------------
  static final Map<String, String> BUILTIN = Map.ofEntries(Map.entry("Int", "int"), Map.entry("Long", "long"), Map.entry("Short", "short"), Map.entry("Byte", "byte"), Map.entry("Char", "char"), Map.entry("Boolean", "boolean"), Map.entry("Float", "float"), Map.entry("Double", "double"),
    Map.entry("String", "java.lang.String"), Map.entry("CharSequence", "java.lang.CharSequence"), Map.entry("Any", "java.lang.Object"), Map.entry("Unit", "void"), Map.entry("Nothing", "void"), Map.entry("Number", "java.lang.Number"),
    Map.entry("Map", "java.util.Map"), Map.entry("MutableMap", "java.util.Map"), Map.entry("HashMap", "java.util.HashMap"), Map.entry("LinkedHashMap", "java.util.LinkedHashMap"), Map.entry("List", "java.util.List"), Map.entry("MutableList", "java.util.List"),
    Map.entry("ArrayList", "java.util.ArrayList"), Map.entry("Set", "java.util.Set"), Map.entry("MutableSet", "java.util.Set"), Map.entry("HashSet", "java.util.HashSet"), Map.entry("Collection", "java.util.Collection"));
  static final Map<String, String> UNBOX = Map.of("int", "java.lang.Integer", "long", "java.lang.Long", "short", "java.lang.Short", "byte", "java.lang.Byte", "char", "java.lang.Character", "boolean", "java.lang.Boolean", "float", "java.lang.Float", "double", "java.lang.Double");
  // A name of a type as the file sees it: Kotlin's built-ins, the file's classes, its imports, the default imports.
  String resolve(String n) {
    if (BUILTIN.containsKey(n)) return BUILTIN.get(n);
    String first = n.contains(".") ? n.substring(0, n.indexOf('.')) : n, rest = n.contains(".") ? n.substring(n.indexOf('.')) : "";
    for (String k : classes.keySet()) { String d = k.replace('$', '.'); if (d.equals(n) || d.endsWith("." + n)) return k; }
    if (imports.containsKey(first)) return bin(imports.get(first) + rest);
    if (n.contains(".") && load(n) != null) return load(n).getName();
    for (String s : stars) { Class<?> c = load(s + n); if (c != null) return c.getName(); }
    return pkg.isEmpty() ? n : pkg + "." + n;
  }
  String bin(String q) { Class<?> c = load(q); return c != null ? c.getName() : q; }
  static Class<?> load(String q) {
    for (String t = q; ; ) {
      try { return Class.forName(t, false, KtReader.class.getClassLoader()); } catch (ClassNotFoundException | NoClassDefFoundError e) { /* an outer class's nested one? */ }
      int i = t.lastIndexOf('.');
      if (i < 0) return null;
      t = t.substring(0, i) + "$" + t.substring(i + 1);
    }
  }
  JT type(KtTypeReference tr) { return tr == null ? null : type(tr.getTypeElement()); }
  JT type(KtTypeElement te) {
    if (te instanceof KtNullableType nt) { JT in = type(nt.getInnerType()); if (in == null) return null; String b = UNBOX.get(in.n); return new JT(b != null ? b : in.n, in.a, true); }
    if (te instanceof KtFunctionType ft) return new JT("kotlin.jvm.functions.Function" + ft.getParameters().size());
    if (te instanceof KtUserType ut) {
      List<String> parts = new ArrayList<>();
      for (KtUserType u = ut; u != null; u = u.getQualifier()) parts.add(0, u.getReferencedName());
      List<JT> as = new ArrayList<>();
      for (KtTypeProjection p : ut.getTypeArguments()) { JT a = type(p.getTypeReference()); as.add(a == null ? new JT("java.lang.Object") : a.nul ? a : boxed(a)); }
      return new JT(resolve(String.join(".", parts)), as, false);
    }
    return null;
  }
  static JT boxed(JT t) { String b = UNBOX.get(t.n); return b == null ? t : new JT(b, t.a, t.nul); }
  // A JVM parameter's erased type, as the harness looks the method up.
  static String erased(JT t) { if (t == null) return "java.lang.Object"; if (t.nul) return UNBOX.getOrDefault(t.n, t.n); return t.n.equals("void") ? "java.lang.Object" : t.n; }
  @Override public List<String> enumValues(String fq) {
    KtClassOrObject c = classes.get(fq);
    if (c instanceof KtClass k && k.isEnum()) { List<String> out = new ArrayList<>(); for (KtDeclaration d : k.getBody().getDeclarations()) if (d instanceof KtEnumEntry e) out.add(e.getName()); return out; }
    Class<?> j = c == null ? load(fq) : null;
    if (j != null && j.isEnum()) { List<String> out = new ArrayList<>(); for (Object o : j.getEnumConstants()) out.add(((Enum<?>) o).name()); return out; }
    return null;
  }
  @Override public String rec(String fq) {
    KtClassOrObject c = classes.get(fq);
    if (!(c instanceof KtClass k) || k.isEnum() || k.isInterface() || k.isSealed()) return null;
    if (recs.containsKey(fq) || fq.equals(selfName)) return fq;
    List<Object> fields = new ArrayList<>();
    for (KtParameter p : k.getPrimaryConstructorParameters()) if (p.hasValOrVar()) fields.add(m("name", p.getName(), "t", stype(type(p.getTypeReference()), this)));
    recs.put(fq, m("name", fq, "short", k.getName(), "fields", fields, "methods", m(), "kinds", k.isData() || fields.size() == k.getPrimaryConstructorParameters().size() ? List.of("dataclass") : List.of("value"), "own", true, "module", pkg, "p", where(k), "jvm", m("data", k.isData() ? true : null)));
    return fq;
  }
  List<Object> annos(KtModifierListOwner o) {
    List<Object> out = new ArrayList<>();
    for (KtAnnotationEntry a : o.getAnnotationEntries()) { String n = a.getShortName() == null ? a.getText() : a.getShortName().asString(); out.add(anno(n, resolve(n), a.getText())); }
    return out;
  }
  static boolean has(KtModifierListOwner o, String n) { for (KtAnnotationEntry a : o.getAnnotationEntries()) if (a.getShortName() != null && a.getShortName().asString().equals(n)) return true; return false; }

  // --- the class ---------------------------------------------------------------------------------------------------------
  // Its supertypes of this file (a sealed or abstract parent's members), from the root down.
  List<KtClassOrObject> chain(KtClassOrObject c) {
    List<KtClassOrObject> out = new ArrayList<>();
    for (KtClassOrObject k = c; k != null; ) {
      out.add(0, k);
      KtClassOrObject next = null;
      for (KtSuperTypeListEntry e : k.getSuperTypeListEntries()) { JT t = type(e.getTypeReference()); if (t != null && classes.get(t.n) instanceof KtClass sc && !sc.isInterface()) next = sc; }
      k = next;
    }
    return out;
  }
  boolean computed(KtProperty p) { return p.getInitializer() == null && p.getGetter() != null && p.getGetter().hasBody() && !p.getGetter().getText().contains("field"); }
  String entry(String name) {
    KtClassOrObject c = classes.get(name);
    self = c; selfName = name;
    Map<String, Object> methods = new LinkedHashMap<>(), sigs = new LinkedHashMap<>();
    List<Object> fields = new ArrayList<>(), jfields = new ArrayList<>(), kinds = new ArrayList<>();
    if (c instanceof KtClass k && !k.getTypeParameters().isEmpty()) kinds.add("generic:" + k.getTypeParameters().size());
    if (c instanceof KtClass k && k.isInner()) return refused(c, name, "an inner class (it holds its outer object; the subset reads a top-level or nested class)");
    List<KtClassOrObject> ch = chain(c);
    boolean immutable = true;
    for (KtClassOrObject k : ch) {
      if (k instanceof KtClass kc) for (KtParameter p : kc.getPrimaryConstructorParameters()) if (p.hasValOrVar()) {
        immutable &= !p.isMutable();
        JT t = type(p.getTypeReference());
        fields.add(m("name", p.getName(), "t", stype(t, this)));
        jfields.add(m("name", p.getName(), "jt", String.valueOf(t), "annos", annos(p), "tag", tag(p)));
      }
      for (KtDeclaration d : body(k)) if (d instanceof KtProperty p && !computed(p) && !p.hasModifier(KtTokens.CONST_KEYWORD)) {
        immutable &= !p.isVar();
        JT t = type(p.getTypeReference());
        if (t == null && p.getInitializer() != null) t = ex(p.getInitializer(), new Ctx(new ArrayList<>(), new HashMap<>(), 0, true)).t();
        fields.add(m("name", p.getName(), "t", stype(t, this)));
        jfields.add(m("name", p.getName(), "jt", String.valueOf(t), "annos", annos(p), "tag", tag(p)));
      }
    }
    // methods: the subclass's own first (an override hides its parent's)
    Set<String> seen = new HashSet<>();
    for (int i = ch.size() - 1; i >= 0; i--) {
      KtClassOrObject k = ch.get(i);
      for (KtDeclaration d : body(k)) {
        if (d instanceof KtNamedFunction fn && fn.hasBody()) {
          String key = key(k, fn);
          if (!seen.add(key)) continue;
          String id = binOf(k) + "#" + fn.getName() + "/" + fn.getValueParameters().size();
          JT rt = type(fn.getTypeReference());
          boolean reducer = immutable && rt != null && (rt.n.equals(name) || chain(c).stream().anyMatch(s -> binOf(s).equals(rt.n)));
          methods.put(key, id);
          funcs.put(id, func(fn, id, reducer, fields));
          if (reducer) reducers.add(key);
          sigs.put(key, m("name", fn.getName(), "params", fn.getValueParameters().stream().map(p -> erased(type(p.getTypeReference()))).toList(), "decl", binOf(k)));
        } else if (d instanceof KtProperty p && computed(p)) {
          if (!seen.add(p.getName())) continue;
          String id = binOf(k) + "#get:" + p.getName();
          methods.put(p.getName(), id);
          funcs.put(id, getter(p, id));
          JT t = type(p.getTypeReference());
          sigs.put(p.getName(), m("name", (p.getName().startsWith("is") && t != null && t.is("boolean") ? p.getName() : "get" + Character.toUpperCase(p.getName().charAt(0)) + p.getName().substring(1)), "params", List.of(), "decl", binOf(k)));
        }
      }
    }
    // the constructor: the primary one, the parents' property initializers before the class's own
    methods.put("__init__", name + "#<init>");
    funcs.put(name + "#<init>", ctor(c, ch));
    List<Object> ps = c instanceof KtClass k ? k.getPrimaryConstructorParameters().stream().map(p -> (Object) erased(type(p.getTypeReference()))).toList() : List.of();
    Map<String, Object> jctor = m("params", ps, "names", c instanceof KtClass k ? k.getPrimaryConstructorParameters().stream().map(KtParameter::getName).toList() : List.of(),
      "jts", c instanceof KtClass k ? k.getPrimaryConstructorParameters().stream().map(p -> String.valueOf(type(p.getTypeReference()))).toList() : List.of(),
      "paramAnnos", c instanceof KtClass k ? k.getPrimaryConstructorParameters().stream().map(this::annos).toList() : List.of(),
      "annos", c instanceof KtClass k && k.getPrimaryConstructor() != null ? annos(k.getPrimaryConstructor()) : List.of());
    recs.put(name, m("name", name, "short", c.getName(), "fields", fields, "methods", methods, "kinds", kinds, "own", true, "module", pkg, "p", where(c), "jvm", m("fields", jfields, "annos", annos(c), "ctor", jctor, "immutable", immutable ? true : null)));
    jvm.put("cls", name); jvm.put("ctor", ps); jvm.put("methods", sigs);
    return name;
  }
  static List<KtDeclaration> body(KtClassOrObject k) { return k.getBody() == null ? List.of() : k.getBody().getDeclarations(); }
  String key(KtClassOrObject k, KtNamedFunction fn) {
    long same = body(k).stream().filter(d -> d instanceof KtNamedFunction f && Objects.equals(f.getName(), fn.getName())).count();
    String n = same > 1 ? fn.getName() + "/" + fn.getValueParameters().size() : fn.getName();
    return fn.hasModifier(KtTokens.PRIVATE_KEYWORD) || Set.of("equals", "hashCode", "toString").contains(fn.getName()) ? "_" + n : n;
  }
  String refused(KtClassOrObject c, String name, String why) {
    funcs.put(name + "#<init>", m("id", name + "#<init>", "name", "__init__", "p", where(c), "span", List.of(base, 0, 0), "params", List.of(m("name", "self", "t", m("k", "any"), "self", true)), "ret", m("k", "none"), "body", List.of(sno(where(c), why)), "decorators", List.of()));
    recs.put(name, m("name", name, "short", c.getName(), "fields", List.of(), "methods", m("__init__", name + "#<init>"), "kinds", List.of(), "own", true, "module", pkg, "p", where(c)));
    return name;
  }
  Map<String, Object> fn(String id, String name, PsiElement at, List<Object> params, JT ret, List<Object> body, KtModifierListOwner o) {
    List<Object> ps = new ArrayList<>(List.of(m("name", "self", "t", m("k", "any"), "self", true)));
    ps.addAll(params);
    return m("id", id, "name", name, "cls", selfName, "p", where(at), "span", List.of(base, line(at.getTextRange().getStartOffset()), line(at.getTextRange().getEndOffset())), "params", ps, "ret", stype(ret, this), "body", body, "decorators", List.of(),
      "annos", o == null ? null : annos(o), "tag", tag(at), "jt", String.valueOf(ret));
  }
  Map<String, Object> func(KtNamedFunction f, String id, boolean reducer, List<Object> fields) {
    Ctx c = new Ctx(new ArrayList<>(), new HashMap<>(), 0, false);
    List<Object> params = new ArrayList<>();
    for (KtParameter p : f.getValueParameters()) {
      JT t = type(p.getTypeReference());
      c.locals.put(p.getName(), t);
      params.add(m("name", p.getName(), "t", pstype(t, this), "jt", String.valueOf(t), "annos", annos(p), "dflt", p.getDefaultValue() == null ? null : ex(p.getDefaultValue(), c.fresh(), t).ir()));
    }
    // (no declared type: Unit for a block body, the expression's for an expression body)
    JT ret = f.getTypeReference() != null ? type(f.getTypeReference()) : f.hasBlockBody() ? new JT("void") : ex(f.getBodyExpression(), new Ctx(new ArrayList<>(), new HashMap<>(c.locals), 0, false)).t();
    List<Object> body = new ArrayList<>();
    String p = where(f);
    if (f.getTypeParameters().size() > 0) body.add(sno(p, f.getName() + ": a generic function"));
    else if (f.getReceiverTypeReference() != null) body.add(sno(p, f.getName() + ": an extension function"));
    else if (f.hasBlockBody()) body.addAll(block(f.getBodyBlockExpression().getStatements(), c, ret));
    else body.addAll(tail(f.getBodyExpression(), c, ret));
    if (reducer) body = next(body, fields);
    if (has(f, "Synchronized")) body = new ArrayList<>(List.of(with(body, p, "@Synchronized " + f.getName())));
    Map<String, Object> out = fn(id, f.getName(), f, params, reducer ? null : ret, body, f);
    if (reducer) out.put("ret", m("k", "none"));
    if (f.hasModifier(KtTokens.SUSPEND_KEYWORD)) out.put("async", null);
    return out;
  }
  // A method returning the object's next value (an immutable class's step): each return writes the fields from it.
  List<Object> next(List<Object> body, List<Object> fields) {
    List<Object> out = new ArrayList<>();
    for (Object s0 : body) {
      @SuppressWarnings("unchecked") Map<String, Object> s = new LinkedHashMap<>((Map<String, Object>) s0);
      String k = (String) s.get("s"), p = (String) s.get("p");
      if ("ret".equals(k) && s.get("x") != null) {
        String v = "$next" + (tmp++);
        out.add(s("set", p, "to", var(v, p), "x", s.get("x")));
        for (Object f0 : fields) { String f = (String) ((Map<?, ?>) f0).get("name"); out.add(s("set", zero(), "to", get(self(p), f, p, "this." + f), "x", get(var(v, p), f, p, v + "." + f))); }
        out.add(s("ret", p));
        continue;
      }
      for (String b : List.of("then", "else", "body")) if (s.get(b) instanceof List<?> l) s.put(b, next(new ArrayList<>(l), fields));
      if (s.get("cases") instanceof List<?> cs) { List<Object> nc = new ArrayList<>(); for (Object c0 : cs) { Map<String, Object> c = new LinkedHashMap<>((Map<String, Object>) c0); c.put("b", next(new ArrayList<>((List<?>) c.get("b")), fields)); nc.add(c); } s.put("cases", nc); }
      out.add(s);
    }
    return out;
  }
  Map<String, Object> getter(KtProperty p, String id) {
    Ctx c = new Ctx(new ArrayList<>(), new HashMap<>(), 0, false);
    JT t = type(p.getTypeReference());
    KtPropertyAccessor g = p.getGetter();
    List<Object> body = g.hasBlockBody() ? block(((KtBlockExpression) g.getBodyExpression()).getStatements(), c, t) : tail(g.getBodyExpression(), c, t);
    if (has(g, "Synchronized") || has(p, "Synchronized")) body = new ArrayList<>(List.of(with(body, where(p), "@Synchronized get")));
    return fn(id, p.getName(), p, List.of(), t, body, p);
  }
  Map<String, Object> ctor(KtClassOrObject c, List<KtClassOrObject> ch) {
    Ctx cx = new Ctx(new ArrayList<>(), new HashMap<>(), 0, true);
    List<Object> params = new ArrayList<>(), body = new ArrayList<>();
    String p = where(c), z = zero();
    if (c instanceof KtClass k) for (KtParameter pa : k.getPrimaryConstructorParameters()) {
      JT t = type(pa.getTypeReference());
      cx.locals.put(pa.getName(), t);
      params.add(m("name", pa.getName(), "t", pstype(t, this), "jt", String.valueOf(t), "annos", annos(pa), "dflt", pa.getDefaultValue() == null ? null : ex(pa.getDefaultValue(), cx.fresh(), t).ir()));
      if (pa.hasValOrVar()) body.add(s("set", where(pa), "to", get(self(z), pa.getName(), z, "this." + pa.getName()), "x", var(pa.getName(), where(pa)), "t", stype(t, this)));
    }
    for (KtClassOrObject k : ch) for (KtDeclaration d : body(k)) {
      if (d instanceof KtProperty pr && !computed(pr) && !pr.hasModifier(KtTokens.CONST_KEYWORD)) {
        JT t = type(pr.getTypeReference());
        if (pr.getInitializer() == null) { body.add(s("set", z, "to", get(self(z), pr.getName(), z, "this." + pr.getName()), "x", x("none", z), "t", stype(t, this))); continue; }
        Ctx sc = cx.fresh();
        X v = ex(pr.getInitializer(), sc, t);
        if (t == null) t = v.t();
        body.addAll(sc.pre);
        body.add(s("set", where(pr), "to", get(self(z), pr.getName(), z, "this." + pr.getName()), "x", at(v.ir(), v.t(), t), "t", stype(t, this)));
      } else if (d instanceof KtAnonymousInitializer ai && ai.getBody() instanceof KtBlockExpression b) body.addAll(block(b.getStatements(), cx, null));
    }
    return m("id", binOf(c) + "#<init>", "name", "__init__", "cls", selfName, "p", p, "span", List.of(base, 0, 0), "params", prepend(m("name", "self", "t", m("k", "any"), "self", true), params), "ret", m("k", "none"), "body", body, "decorators", List.of());
  }
  static List<Object> prepend(Object a, List<Object> xs) { List<Object> out = new ArrayList<>(); out.add(a); out.addAll(xs); return out; }

  // --- statements ------------------------------------------------------------------------------------------------------
  List<Object> block(List<KtExpression> ss, Ctx c0, JT ret) {
    List<Object> out = new ArrayList<>();
    Ctx c = c0.scope();
    for (KtExpression s : ss) out.addAll(stmt(s, c, ret));
    return out;
  }
  // A statement, with what its expression needed before it.
  List<Object> stmt(KtExpression e, Ctx c0, JT ret) {
    Ctx c = new Ctx(new ArrayList<>(), c0.locals, 0, c0.init);
    List<Object> s = stmt1(e, c, ret);
    List<Object> out = new ArrayList<>(c.pre);
    out.addAll(s);
    return out;
  }
  List<Object> stmt1(KtExpression e, Ctx c, JT ret) {
    String p = where(e);
    if (e instanceof KtProperty v) {
      JT t = type(v.getTypeReference());
      X x = v.getInitializer() == null ? new X(x("none", p), t) : ex(v.getInitializer(), c, t);
      if (t == null) t = x.t();
      c.locals.put(v.getName(), t);
      return List.of(s("set", p, "to", var(v.getName(), p), "x", at(x.ir(), x.t(), t), "t", stype(t, this)));
    }
    if (e instanceof KtReturnExpression r) return r.getReturnedExpression() == null ? List.of(s("ret", p)) : tail(r.getReturnedExpression(), c, ret);
    if (e instanceof KtThrowExpression) return List.of(fail(p, text(e)));
    if (e instanceof KtIfExpression i) {
      X cond = ex(i.getCondition(), c);
      return List.of(s("if", p, "c", cond.ir(), "then", branch(i.getThen(), c, ret), "else", i.getElse() == null ? List.of() : branch(i.getElse(), c, ret)));
    }
    if (e instanceof KtWhenExpression w) return when(w, c, ret, false);
    if (e instanceof KtBlockExpression b) return block(b.getStatements(), c, ret);
    if (e instanceof KtWhileExpression w) return once(w.getCondition(), w.getBody(), c, ret, p);
    if (e instanceof KtDoWhileExpression w) return once(w.getCondition(), w.getBody(), c, ret, p);
    if (e instanceof KtForExpression) return List.of(sno(p, "a loop over a collection"));
    if (e instanceof KtBreakExpression b) return b.getLabelName() == null ? List.of(s("break", p)) : List.of(sno(p, "a labeled break"));
    if (e instanceof KtContinueExpression) return List.of(sno(p, "continue (a loop's next pass: the subset reads a compare-and-set loop's first)"));
    if (e instanceof KtTryExpression) return List.of(sno(p, "try (an exception caught: the subset reads an exception only as the step's failure)"));
    if (e instanceof KtBinaryExpression b) {
      IElementType op = b.getOperationToken();
      if (op == KtTokens.EQ) return assign(b.getLeft(), b.getRight(), c, p);
      String aop = op == KtTokens.PLUSEQ ? "+" : op == KtTokens.MINUSEQ ? "-" : op == KtTokens.MULTEQ ? "*" : op == KtTokens.DIVEQ ? "/" : op == KtTokens.PERCEQ ? "%" : null;
      if (aop != null) {
        X l = ex(b.getLeft(), c), r = ex(b.getRight(), c);
        Map<String, Object> to = place(b.getLeft(), c);
        if (to == null) return List.of(sno(p, text(b.getLeft()) + ": an assignment the subset doesn't read"));
        if (l.t() != null && l.t().is("java.lang.String")) return List.of(s("set", p, "to", to, "x", x("bin", p, "op", "+", "x", l.ir(), "y", r.ir(), "text", text(e))));
        if (l.t() != null && map(l.t())) return List.of(sno(p, text(e) + ": a map's plus (the subset writes one key a step)"));
        return List.of(s("set", p, "to", to, "x", arith(aop, l.ir(), l.t(), r.ir(), r.t(), l.t(), "wrap", p, text(e))));
      }
    }
    if (e instanceof KtUnaryExpression u && (u.getOperationToken() == KtTokens.PLUSPLUS || u.getOperationToken() == KtTokens.MINUSMINUS) && !(e instanceof KtPrefixExpression pe && pe.getOperationToken() == KtTokens.EXCL)) {
      X v = ex(u.getBaseExpression(), c);
      Map<String, Object> to = place(u.getBaseExpression(), c);
      if (to == null) return List.of(sno(p, text(e) + ": an assignment the subset doesn't read"));
      return List.of(s("set", p, "to", to, "x", arith(u.getOperationToken() == KtTokens.PLUSPLUS ? "+" : "-", v.ir(), v.t(), lit(1, v.t(), p), v.t(), v.t(), "wrap", p, text(e))));
    }
    // a call as a statement (a map's put, an atomic's set, a check, synchronized and withLock, a scope function)
    X x = exStmt(e, c, ret);
    if (x == null) return List.of();
    if ("$stmts".equals(x.ir().get("e"))) { @SuppressWarnings("unchecked") List<Object> ss = (List<Object>) x.ir().get("ss"); return ss; }
    return List.of(s("expr", p, "x", x.ir()));
  }
  List<Object> branch(KtExpression e, Ctx c, JT ret) { Ctx b = c.scope(); return e instanceof KtBlockExpression bl ? block(bl.getStatements(), b, ret) : stmt(e, b, ret); }
  // A return of an if or a when: the return pushed into its branches (each its own value, as statements).
  List<Object> tail(KtExpression e, Ctx c, JT ret) {
    String p = where(e);
    if (e instanceof KtParenthesizedExpression pe) return tail(pe.getExpression(), c, ret);
    if (e instanceof KtIfExpression i && i.getElse() != null) {
      X cond = ex(i.getCondition(), c);
      return List.of(s("if", p, "c", cond.ir(), "then", tailBranch(i.getThen(), c, ret), "else", tailBranch(i.getElse(), c, ret)));
    }
    if (e instanceof KtWhenExpression w) return when(w, c, ret, true);
    if (e instanceof KtBlockExpression b) {
      List<KtExpression> ss = b.getStatements();
      Ctx sc = c.scope();
      List<Object> out = new ArrayList<>();
      for (int i = 0; i < ss.size() - 1; i++) out.addAll(stmt(ss.get(i), sc, ret));
      if (!ss.isEmpty()) out.addAll(tail(ss.get(ss.size() - 1), sc, ret));
      return out;
    }
    if (e instanceof KtThrowExpression || e instanceof KtReturnExpression) return stmt1(e, c, ret);
    X x = ex(e, c, ret);
    return List.of(s("ret", p, "x", at(x.ir(), x.t(), ret)));
  }
  List<Object> tailBranch(KtExpression e, Ctx c, JT ret) { Ctx b = new Ctx(new ArrayList<>(), new HashMap<>(c.locals), 0, c.init); List<Object> t = tail(e, b, ret); List<Object> out = new ArrayList<>(b.pre); out.addAll(t); return out; }
  // when: a chain of ifs on == (a subject's value bound once), `is` a type test the reader decides where it can, `in`
  // a range's bounds.
  List<Object> when(KtWhenExpression w, Ctx c, JT ret, boolean asTail) {
    String p = where(w);
    List<Object> out = new ArrayList<>();
    X subj = null;
    String sv = null;
    if (w.getSubjectExpression() != null) {
      subj = ex(w.getSubjectExpression(), c);
      sv = "$when" + (tmp++);
      if (w.getSubjectVariable() != null) c.locals.put(w.getSubjectVariable().getName(), subj.t());
      out.add(s("set", p, "to", var(w.getSubjectVariable() != null ? w.getSubjectVariable().getName() : sv, p), "x", subj.ir()));
      if (w.getSubjectVariable() != null) sv = w.getSubjectVariable().getName();
    }
    List<Object> acc = List.of();
    List<KtWhenEntry> es = w.getEntries();
    boolean exhaustive = es.stream().anyMatch(KtWhenEntry::isElse);
    if (asTail && !exhaustive) acc = List.of(sno(p, "a when with no else as a value"));
    for (int i = es.size() - 1; i >= 0; i--) {
      KtWhenEntry en = es.get(i);
      List<Object> arm = asTail ? tailBranch(en.getExpression(), c, ret) : branch(en.getExpression(), c, ret);
      if (en.isElse()) { acc = arm; continue; }
      List<Object> conds = new ArrayList<>();
      for (KtWhenCondition wc : en.getConditions()) conds.add(cond(wc, sv, subj == null ? null : subj.t(), c, where(wc)));
      acc = List.of(s("if", zero(), "c", conds.size() == 1 ? conds.get(0) : x("or", where(en), "xs", conds), "then", arm, "else", acc));
    }
    out.addAll(acc);
    return out;
  }
  Object cond(KtWhenCondition wc, String sv, JT st, Ctx c, String p) {
    if (wc instanceof KtWhenConditionWithExpression we) {
      if (sv == null) return ex(we.getExpression(), c).ir();
      X v = ex(we.getExpression(), c, st);
      return cmp("==", var(sv, p), v.ir(), p, text(wc));
    }
    if (wc instanceof KtWhenConditionIsPattern ip) {
      JT t = type(ip.getTypeReference());
      Boolean is = isType(sv == null ? null : st, t);
      if (is == null) return no(p, text(wc) + ": a type test the reader can't decide");
      return x("bool", p, "v", ip.isNegated() != is);
    }
    if (wc instanceof KtWhenConditionInRange ir && ir.getRangeExpression() instanceof KtBinaryExpression r && r.getOperationToken() == KtTokens.RANGE && sv != null) {
      X lo = ex(r.getLeft(), c), hi = ex(r.getRight(), c);
      Object in = x("and", p, "xs", List.of(cmp("<=", lo.ir(), var(sv, p), p, text(wc)), cmp("<=", var(sv, p), hi.ir(), p, text(wc))));
      return ir.isNegated() ? not(in, p) : in;
    }
    return no(p, text(wc) + ": a when condition outside the subset");
  }
  // Whether a value of type a is a t: decided where a is the class read or one of its parents.
  Boolean isType(JT a, JT t) {
    if (a == null || t == null) return null;
    if (a.n.equals(t.n)) return true;
    KtClassOrObject ac = classes.get(a.n);
    if (ac == null) return null;
    if (chain(ac).stream().anyMatch(k -> binOf(k).equals(t.n))) return true;
    if (classes.containsKey(t.n) && a.n.equals(selfName)) return false;
    return null;
  }
  // while (true) / do ... while (true): a compare-and-set retry loop, read as its first pass.
  List<Object> once(KtExpression cond, KtExpression body, Ctx c, JT ret, String p) {
    if (!(cond instanceof KtConstantExpression k && k.getText().equals("true"))) return List.of(sno(p, "a loop"));
    List<Object> b = new ArrayList<>(branch(body, c, ret));
    b.add(sno(p, "the loop goes around again (the subset reads a retry loop's first pass: a compare-and-set that succeeds when calls don't interleave)"));
    return List.of(breakable(b, p));
  }
  List<Object> assign(KtExpression l, KtExpression r, Ctx c, String p) {
    if (l instanceof KtArrayAccessExpression aa && aa.getIndexExpressions().size() == 1) {
      X m = ex(aa.getArrayExpression(), c), k = ex(aa.getIndexExpressions().get(0), c), v = ex(r, c, m.t() == null ? null : m.t().arg(1));
      if (m.t() == null || !map(m.t())) return List.of(sno(p, text(l) + ": an item of other than a map"));
      return List.of(s("set", p, "to", x("idx", p, "x", m.ir(), "i", at(k.ir(), k.t(), m.t().arg(0)), "text", text(l)), "x", v.ir()));
    }
    Map<String, Object> to = place(l, c);
    if (to == null) return List.of(sno(p, text(l) + ": an assignment the subset doesn't read"));
    X tl = ex(l, c.fresh()), v = ex(r, c, tl.t());
    return List.of(s("set", p, "to", to, "x", at(v.ir(), v.t(), tl.t())));
  }
  Map<String, Object> place(KtExpression l, Ctx c) {
    String p = where(l);
    if (l instanceof KtNameReferenceExpression n) {
      String id = n.getReferencedName();
      if (c.locals.containsKey(id)) return var(id, p);
      if (field(id) != null) return get(self(p), id, p, id);
      return null;
    }
    if (l instanceof KtDotQualifiedExpression d && d.getSelectorExpression() instanceof KtNameReferenceExpression n) {
      X o = ex(d.getReceiverExpression(), c);
      return get(o.ir(), n.getReferencedName(), p, text(l));
    }
    return null;
  }
  // A field of the class read (a property with a backing field, a val/var constructor parameter), or its type.
  JT field(String name) {
    for (KtClassOrObject k : chain(self)) {
      if (k instanceof KtClass kc) for (KtParameter p : kc.getPrimaryConstructorParameters()) if (p.hasValOrVar() && name.equals(p.getName())) return orObject(type(p.getTypeReference()));
      for (KtDeclaration d : body(k)) if (d instanceof KtProperty pr && name.equals(pr.getName()) && !computed(pr) && !pr.hasModifier(KtTokens.CONST_KEYWORD)) {
        JT t = type(pr.getTypeReference());
        return t != null ? t : pr.getInitializer() != null ? orObject(ex(pr.getInitializer(), new Ctx(new ArrayList<>(), new HashMap<>(), 0, true)).t()) : new JT("java.lang.Object");
      }
    }
    return null;
  }
  static JT orObject(JT t) { return t == null ? new JT("java.lang.Object") : t; }
  KtProperty computedProp(String name) { for (KtClassOrObject k : chain(self)) for (KtDeclaration d : body(k)) if (d instanceof KtProperty pr && name.equals(pr.getName()) && computed(pr)) return pr; return null; }
  KtProperty constant(String name) {
    for (KtDeclaration d : file.getDeclarations()) if (d instanceof KtProperty pr && name.equals(pr.getName()) && pr.hasModifier(KtTokens.CONST_KEYWORD)) return pr;
    for (KtClassOrObject k : chain(self)) for (KtObjectDeclaration o : k instanceof KtClass kc ? kc.getCompanionObjects() : List.<KtObjectDeclaration>of()) for (KtDeclaration d : body(o)) if (d instanceof KtProperty pr && name.equals(pr.getName()) && (pr.hasModifier(KtTokens.CONST_KEYWORD) || !pr.isVar())) return pr;
    for (KtClassOrObject k : chain(self)) for (KtDeclaration d : body(k)) if (d instanceof KtProperty pr && name.equals(pr.getName()) && pr.hasModifier(KtTokens.CONST_KEYWORD)) return pr;
    return null;
  }
  KtNamedFunction method(String name, int arity) {
    List<KtClassOrObject> ch = chain(self);
    for (int i = ch.size() - 1; i >= 0; i--) for (KtDeclaration d : body(ch.get(i))) if (d instanceof KtNamedFunction f && name.equals(f.getName()) && f.getValueParameters().size() >= arity) return f;
    return null;
  }
  KtClassOrObject ownerOf(KtNamedFunction f) { for (KtClassOrObject k : chain(self)) if (body(k).contains(f)) return k; return self; }

  // --- expressions -----------------------------------------------------------------------------------------------------
  X ex(KtExpression e, Ctx c) { return ex(e, c, null); }
  X no1(PsiElement e, String why) { return new X(no(where(e), text(e) + ": " + why), null); }
  // An expression where its value is wanted (`want`: the type it is given to, which an integer literal takes).
  X ex(KtExpression e, Ctx c, JT want) {
    String p = where(e), t = text(e);
    if (e instanceof KtParenthesizedExpression pe) return ex(pe.getExpression(), c, want);
    if (e instanceof KtAnnotatedExpression ae) return ex(ae.getBaseExpression(), c, want);
    if (e instanceof KtLabeledExpression le) return ex(le.getBaseExpression(), c, want);
    if (e instanceof KtConstantExpression k) {
      IElementType et = k.getNode().getElementType();
      String s = k.getText().replace("_", "");
      if (et == KtNodeTypes.BOOLEAN_CONSTANT) return new X(x("bool", p, "v", s.equals("true")), new JT("boolean"));
      if (et == KtNodeTypes.NULL) return new X(x("none", p), new JT("null"));
      if (et == KtNodeTypes.INTEGER_CONSTANT) {
        boolean lng = s.endsWith("L") || s.endsWith("l");
        String d = s.replaceAll("[lLuU]+$", "");
        long v = d.startsWith("0x") || d.startsWith("0X") ? Long.parseLong(d.substring(2), 16) : d.startsWith("0b") || d.startsWith("0B") ? Long.parseLong(d.substring(2), 2) : Long.parseLong(d);
        JT ty = lng || v > Integer.MAX_VALUE || v < Integer.MIN_VALUE ? new JT("long") : want != null && integral(want) ? new JT(prim(want)) : new JT("int");
        return new X(lit(v, ty, p), ty);
      }
      if (et == KtNodeTypes.FLOAT_CONSTANT) { double d = Double.parseDouble(s.replaceAll("[fF]$", "")); return d == Math.floor(d) && Math.abs(d) < 9.007199254740992E15 ? new X(x("int", p, "v", Long.toString((long) d), "float", true), new JT(s.endsWith("f") || s.endsWith("F") ? "float" : "double")) : no1(e, "a float that isn't whole (a binary fraction)"); }
      if (et == KtNodeTypes.CHARACTER_CONSTANT) return no1(e, "a character literal");
    }
    if (e instanceof KtStringTemplateExpression st) {
      if (!st.hasInterpolation()) { StringBuilder b = new StringBuilder(); for (KtStringTemplateEntry en : st.getEntries()) b.append(en instanceof KtEscapeStringTemplateEntry es ? es.getUnescapedValue() : en.getText()); return new X(str(b.toString(), p), new JT("java.lang.String")); }
      List<Object> parts = new ArrayList<>();
      for (KtStringTemplateEntry en : st.getEntries()) parts.add(en.getExpression() == null ? en.getText() : m("x", ex(en.getExpression(), c.under()).ir(), "plain", true));
      return new X(x("fstr", p, "parts", parts, "text", t), new JT("java.lang.String"));
    }
    if (e instanceof KtThisExpression) return new X(self(p), new JT(selfName));
    if (e instanceof KtNameReferenceExpression n) return name(n, c, p, t);
    if (e instanceof KtDotQualifiedExpression d) return dot(d, c, p, t, want, false);
    if (e instanceof KtSafeQualifiedExpression sq) return safe(sq, c, p, t);
    if (e instanceof KtCallExpression ce) return call(ce, null, null, c, p, t, want, false);
    if (e instanceof KtArrayAccessExpression aa && aa.getIndexExpressions().size() == 1) {
      X m = ex(aa.getArrayExpression(), c), k = ex(aa.getIndexExpressions().get(0), c);
      if (m.t() == null || !map(m.t())) return no1(e, "an item of other than a map");
      return new X(Jvm.call(get(m.ir(), "get", p, t), List.of(at(k.ir(), k.t(), m.t().arg(0))), p, t), m.t().arg(1).nullable(true));
    }
    if (e instanceof KtIfExpression i) {
      if (i.getElse() == null) return no1(e, "an if with no else as a value");
      X cond = ex(i.getCondition(), c);
      X a = value(i.getThen(), c.under(), want), b = value(i.getElse(), c.under(), want);
      JT ty = a.t() == null || a.t().is("null") ? (b.t() == null ? null : b.t().nullable(a.t() != null)) : b.t() != null && b.t().is("null") ? a.t().nullable(true) : a.t();
      if (num(a.t()) && num(b.t())) ty = promote(a.t(), b.t());
      return new X(x("ite", p, "c", cond.ir(), "a", at(a.ir(), a.t(), ty), "b", at(b.ir(), b.t(), ty)), ty);
    }
    if (e instanceof KtWhenExpression w) return no1(e, "a when as a value inside an expression (the subset reads one as a statement or a return)");
    if (e instanceof KtPrefixExpression pe) {
      IElementType op = pe.getOperationToken();
      X v = ex(pe.getBaseExpression(), c, want);
      if (op == KtTokens.EXCL) return new X(not(v.ir(), p), new JT("boolean"));
      if (op == KtTokens.MINUS) return floating(v.t()) ? new X(x("neg", p, "x", v.ir()), v.t()) : new X(x("unop", p, "op", "-", "x", at(v.ir(), v.t(), v.t()), "text", t), v.t());
      if (op == KtTokens.PLUS) return v;
      return no1(e, "an assignment inside an expression");
    }
    if (e instanceof KtPostfixExpression pe) {
      if (pe.getOperationToken() == KtTokens.EXCLEXCL) { X v = ex(pe.getBaseExpression(), c); return new X(x("expect", p, "x", v.ir(), "text", t + " (a NullPointerException)"), v.t() == null ? null : v.t().nullable(false)); }
      return no1(e, "an assignment inside an expression");
    }
    if (e instanceof KtBinaryExpressionWithTypeRHS as) {
      X v = ex(as.getLeft(), c);
      JT to = type(as.getRight());
      Boolean is = isType(v.t(), to);
      return Boolean.TRUE.equals(is) ? new X(v.ir(), to) : no1(e, "a cast the reader can't decide");
    }
    if (e instanceof KtIsExpression ie) {
      X v = ex(ie.getLeftHandSide(), c);
      Boolean is = isType(v.t(), type(ie.getTypeReference()));
      return is == null ? no1(e, "a type test the reader can't decide") : new X(x("bool", p, "v", ie.isNegated() != is), new JT("boolean"));
    }
    if (e instanceof KtBinaryExpression b) return binary(b, c, p, t, want);
    if (e instanceof KtLambdaExpression || e instanceof KtCallableReferenceExpression) return new X(x("opaque", p, "why", t + ": a lambda (a closure)"), new JT("kotlin.jvm.functions.Function0"));
    if (e instanceof KtObjectLiteralExpression) return no1(e, "an object expression");
    if (e instanceof KtThrowExpression || e instanceof KtReturnExpression || e instanceof KtBreakExpression || e instanceof KtContinueExpression) return no1(e, "a jump inside an expression");
    return no1(e, e.getClass().getSimpleName().replace("Kt", "") + " (outside the subset)");
  }
  // A branch's value: a block's last expression after its statements (which go before it).
  X value(KtExpression e, Ctx c, JT want) {
    if (e instanceof KtBlockExpression b) {
      List<KtExpression> ss = b.getStatements();
      if (ss.isEmpty()) return new X(x("none", where(e)), new JT("void"));
      if (ss.size() > 1) return no1(e, "a block of several statements as a value");
      return ex(ss.get(0), c, want);
    }
    return ex(e, c, want);
  }
  X binary(KtBinaryExpression b, Ctx c, String p, String t, JT want) {
    IElementType op = b.getOperationToken();
    if (op == KtTokens.ANDAND || op == KtTokens.OROR) { X l = ex(b.getLeft(), c), r = ex(b.getRight(), c.under()); return new X(x(op == KtTokens.ANDAND ? "and" : "or", p, "xs", List.of(l.ir(), r.ir())), new JT("boolean")); }
    if (op == KtTokens.ELVIS) {
      X l = ex(b.getLeft(), c);
      KtExpression r = b.getRight();
      if (r instanceof KtReturnExpression || r instanceof KtThrowExpression) {
        if (c.cond > 0) return no1(b, "?: return inside a condition");
        String v = "$elvis" + (tmp++);
        c.pre.add(s("set", p, "to", var(v, p), "x", l.ir()));
        c.locals.put(v, l.t());
        c.pre.add(s("if", p, "c", cmp("is", var(v, p), x("none", p), p, t), "then", stmt(r, c, null), "else", List.of()));
        return new X(var(v, p), l.t() == null ? null : l.t().nullable(false));
      }
      X rv = ex(r, c.under(), l.t() == null ? want : l.t().nullable(false));
      JT ty = l.t() == null ? rv.t() : l.t().nullable(rv.t() != null && rv.t().nul);
      return new X(x("opt_or", p, "x", l.ir(), "d", at(rv.ir(), rv.t(), ty == null ? null : ty.nullable(false))), ty);
    }
    if (op == KtTokens.IN_KEYWORD || op == KtTokens.NOT_IN) {
      X k = ex(b.getLeft(), c), m = ex(b.getRight(), c);
      if (b.getRight() instanceof KtBinaryExpression r && r.getOperationToken() == KtTokens.RANGE) {
        X lo = ex(r.getLeft(), c), hi = ex(r.getRight(), c);
        Object in = x("and", p, "xs", List.of(cmp("<=", lo.ir(), k.ir(), p, t), cmp("<=", k.ir(), hi.ir(), p, t)));
        return new X(op == KtTokens.IN_KEYWORD ? (Map<String, Object>) in : not(in, p), new JT("boolean"));
      }
      if (m.t() == null || !map(m.t())) return no1(b, "in of other than a map or a range");
      return new X(cmp(op == KtTokens.IN_KEYWORD ? "in" : "not in", at(k.ir(), k.t(), m.t().arg(0)), m.ir(), p, t), new JT("boolean"));
    }
    X l = ex(b.getLeft(), c), r = ex(b.getRight(), c, l.t());
    if (op == KtTokens.EQEQ || op == KtTokens.EXCLEQ || op == KtTokens.EQEQEQ || op == KtTokens.EXCLEQEQEQ) {
      boolean eq = op == KtTokens.EQEQ || op == KtTokens.EQEQEQ;
      if (r.t() != null && r.t().is("null")) return new X(cmp(eq ? "is" : "is not", l.ir(), r.ir(), p, t), new JT("boolean"));
      if (l.t() != null && l.t().is("null")) return new X(cmp(eq ? "is" : "is not", r.ir(), l.ir(), p, t), new JT("boolean"));
      Map<String, Object> a = l.ir(), bb = r.ir();
      if (num(l.t()) && num(r.t())) { JT w = promote(l.t(), r.t()); a = at(a, l.t(), w); bb = at(bb, r.t(), w); }
      return new X(cmp(eq ? "==" : "!=", a, bb, p, t), new JT("boolean"));
    }
    String rel = op == KtTokens.LT ? "<" : op == KtTokens.LTEQ ? "<=" : op == KtTokens.GT ? ">" : op == KtTokens.GTEQ ? ">=" : null;
    if (rel != null) return new X(cmp(rel, l.ir(), r.ir(), p, t), new JT("boolean"));
    String a = op == KtTokens.PLUS ? "+" : op == KtTokens.MINUS ? "-" : op == KtTokens.MUL ? "*" : op == KtTokens.DIV ? "/" : op == KtTokens.PERC ? "%" : null;
    if (a != null) {
      if (l.t() != null && l.t().is("java.lang.String")) return new X(x("bin", p, "op", "+", "x", l.ir(), "y", r.ir(), "text", t), l.t());
      if (!num(l.t()) || !num(r.t())) return no1(b, "an operator of other than numbers");
      JT ty = promote(l.t(), r.t());
      if (floating(ty) && (a.equals("/") || a.equals("%"))) return no1(b, "a float division (the subset reads whole numbers)");
      return new X(arith(a, l.ir(), l.t(), r.ir(), r.t(), ty, "wrap", p, t), ty);
    }
    if (op == KtTokens.IDENTIFIER) {
      String n = b.getOperationReference().getReferencedName();
      if ((n.equals("shl") || n.equals("shr")) && integral(l.t())) return new X(x("binop", p, "op", n.equals("shl") ? "<<" : ">>", "x", at(l.ir(), l.t(), l.t()), "y", r.ir(), "text", t), l.t());
      if ((n.equals("and") || n.equals("or")) && "boolean".equals(prim(l.t()))) return new X(x(n, p, "xs", List.of(l.ir(), r.ir())), new JT("boolean"));
      return no1(b, n + " (an infix function outside the subset)");
    }
    return no1(b, "an operator outside the subset");
  }
  X name(KtNameReferenceExpression n, Ctx c, String p, String t) {
    String id = n.getReferencedName();
    if (c.locals.containsKey(id)) return new X(var(id, p), c.locals.get(id));
    JT ft = field(id);
    if (ft != null) return new X(get(self(p), id, p, id), ft);
    KtProperty cp = computedProp(id);
    if (cp != null) return new X(Jvm.call(get(self(p), id, p, id), List.of(), p, t), type(cp.getTypeReference()));
    KtProperty k = constant(id);
    if (k != null && k.getInitializer() != null) return ex(k.getInitializer(), c.fresh(), type(k.getTypeReference()));
    return new X(no(p, t + ": a name the reader can't resolve (another file's, or other code's)"), null);
  }
  // A receiver's member: an enum's constant, a field of an object of the code's own, a computed property, a call.
  X dot(KtDotQualifiedExpression d, Ctx c, String p, String t, JT want, boolean stmt) {
    KtExpression r = d.getReceiverExpression(), sel = d.getSelectorExpression();
    // A qualified name: an enum's constant, a companion's constant, a JDK class's static call
    String qual = r.getText().replaceAll("\\s", "");
    if (sel instanceof KtNameReferenceExpression sn && qual.matches("[A-Z][\\w.]*") && !c.locals.containsKey(qual) && field(qual) == null) {
      String ty = resolve(qual);
      List<String> ev = enumValues(ty);
      if (ev != null && ev.contains(sn.getReferencedName())) return new X(str(sn.getReferencedName(), p), new JT(ty));
      String q = ty + "." + sn.getReferencedName();
      if (q.equals("java.lang.Integer.MAX_VALUE") || q.equals("int.MAX_VALUE")) return new X(lit(Integer.MAX_VALUE, new JT("int"), p), new JT("int"));
      if (q.equals("java.lang.Integer.MIN_VALUE") || q.equals("int.MIN_VALUE")) return new X(lit(Integer.MIN_VALUE, new JT("int"), p), new JT("int"));
      if (q.equals("long.MAX_VALUE") || q.equals("long.MIN_VALUE")) return no1(d, "Long's bound (past the rule's ±2^53)");
      return no1(d, "a static member of another class");
    }
    if (sel instanceof KtCallExpression ce && qual.matches("[A-Z][\\w.]*") && !c.locals.containsKey(qual) && field(qual) == null) return call(ce, null, new JT(resolve(qual)), c, p, t, want, stmt);
    X o = ex(r, c);
    if (sel instanceof KtCallExpression ce) return call(ce, o, null, c, p, t, want, stmt);
    if (!(sel instanceof KtNameReferenceExpression sn)) return no1(d, "a member outside the subset");
    String f = sn.getReferencedName();
    if (o.t() != null && atomic(o.t()) && f.equals("value")) return new X(o.ir(), held(o.t()));
    if (o.t() != null && map(o.t()) && f.equals("size")) return no1(d, "a map's size");
    if (o.t() != null && (o.t().n.equals(selfName) || chain(self).stream().anyMatch(k -> binOf(k).equals(o.t().n)))) {
      JT ft = field(f);
      if (ft != null) return new X(get(o.ir(), f, p, t), ft);
      KtProperty cp = computedProp(f);
      if (cp != null) return new X(Jvm.call(get(o.ir(), f, p, t), List.of(), p, t), type(cp.getTypeReference()));
    }
    if (o.t() != null && rec(o.t().n) != null && classes.get(o.t().n) instanceof KtClass kc) {
      for (KtParameter pa : kc.getPrimaryConstructorParameters()) if (f.equals(pa.getName())) return new X(get(o.ir(), f, p, t), type(pa.getTypeReference()));
    }
    return no1(d, "a property of other code (" + (o.t() == null ? "?" : o.t().simple()) + ")");
  }
  // x?.f and x?.let { }: the member where x isn't null, null where it is.
  X safe(KtSafeQualifiedExpression sq, Ctx c, String p, String t) {
    if (c.cond > 0) return no1(sq, "?. inside a condition");
    X o = ex(sq.getReceiverExpression(), c);
    String v = "$safe" + (tmp++);
    c.pre.add(s("set", p, "to", var(v, p), "x", o.ir()));
    c.locals.put(v, o.t() == null ? null : o.t().nullable(false));
    Ctx in = new Ctx(new ArrayList<>(), c.locals, 0, c.init);
    KtExpression sel = sq.getSelectorExpression();
    X inner = sel instanceof KtCallExpression ce ? call(ce, new X(var(v, p), o.t() == null ? null : o.t().nullable(false)), null, in, p, t, null, false) : no1(sq, "?. of a property");
    if (!in.pre.isEmpty()) {
      String r = "$safev" + (tmp++);
      List<Object> then = new ArrayList<>(in.pre);
      then.add(s("set", p, "to", var(r, p), "x", inner.ir()));
      c.pre.add(s("set", p, "to", var(r, p), "x", x("none", p)));
      c.pre.add(s("if", p, "c", cmp("is not", var(v, p), x("none", p), p, t), "then", then, "else", List.of()));
      return new X(var(r, p), inner.t() == null ? null : inner.t().nullable(true));
    }
    return new X(x("ite", p, "c", cmp("is not", var(v, p), x("none", p), p, t), "a", inner.ir(), "b", x("none", p)), inner.t() == null ? null : inner.t().nullable(true));
  }
  // An expression used as a statement: a call whose value no one reads (a scope function's body runs as statements).
  X exStmt(KtExpression e, Ctx c, JT ret) {
    if (e instanceof KtDotQualifiedExpression d) return dot(d, c, where(e), text(e), null, true);
    if (e instanceof KtCallExpression ce) return call(ce, null, null, c, where(e), text(e), null, true);
    if (e instanceof KtSafeQualifiedExpression sq && sq.getSelectorExpression() instanceof KtCallExpression ce && lambda(ce) != null) {
      String p = where(e);
      X o = ex(sq.getReceiverExpression(), c);
      String v = "$safe" + (tmp++);
      c.pre.add(s("set", p, "to", var(v, p), "x", o.ir()));
      Ctx in = new Ctx(new ArrayList<>(), new HashMap<>(c.locals), 0, c.init);
      in.locals.put(v, o.t() == null ? null : o.t().nullable(false));
      X body = call(ce, new X(var(v, p), o.t() == null ? null : o.t().nullable(false)), null, in, p, text(e), null, true);
      List<Object> then = new ArrayList<>(in.pre);
      if ("$stmts".equals(body.ir().get("e"))) then.addAll((List<?>) body.ir().get("ss")); else then.add(s("expr", p, "x", body.ir()));
      return new X(x("$stmts", p, "ss", List.of(s("if", p, "c", cmp("is not", var(v, p), x("none", p), p, text(e)), "then", then, "else", List.of()))), null);
    }
    return ex(e, c);
  }
  static KtLambdaExpression lambda(KtCallExpression ce) { return ce.getLambdaArguments().isEmpty() ? null : ce.getLambdaArguments().get(0).getLambdaExpression(); }
  // A lambda inlined (a scope function's, synchronized's): its parameter (or `it`) bound to a value, its statements
  // before, its last expression its value.
  X inline(KtLambdaExpression l, String it, X v, Ctx c, boolean stmt, String p) {
    if (c.cond > 0) return no1(l, "a scope function inside a condition");
    String name = l.getValueParameters().isEmpty() ? "it" : l.getValueParameters().get(0).getName();
    String bound = "$it" + (tmp++);
    if (v != null) { c.pre.add(s("set", p, "to", var(bound, p), "x", v.ir())); }
    Ctx in = new Ctx(c.pre, new HashMap<>(c.locals), 0, c.init);
    if (v != null) { in.locals.put(bound, v.t()); in.locals.put(name, v.t()); c.pre.add(s("set", p, "to", var(name, p), "x", var(bound, p))); }
    List<KtExpression> ss = l.getBodyExpression() == null ? List.of() : l.getBodyExpression().getStatements();
    for (int i = 0; i < ss.size() - 1; i++) c.pre.addAll(stmt(ss.get(i), in, null));
    if (ss.isEmpty()) return new X(x("none", p), new JT("void"));
    KtExpression last = ss.get(ss.size() - 1);
    if (stmt) { c.pre.addAll(stmt(last, in, null)); return new X(x("none", p), new JT("void")); }
    return ex(last, in);
  }
  // A call: the class's own function (inlined), a data class's copy, the standard library's (lowered), a scope
  // function (inlined), or other code's (`ext`).
  X call(KtCallExpression ce, X recv, JT staticOwner, Ctx c, String p, String t, JT want, boolean stmt) {
    String n = ce.getCalleeExpression() == null ? "?" : ce.getCalleeExpression().getText();
    KtLambdaExpression lam = lambda(ce);
    List<KtValueArgument> vas = ce.getValueArguments().stream().filter(a -> !(a instanceof KtLambdaArgument)).map(a -> (KtValueArgument) a).toList();
    // synchronized(x) { }, x.withLock { }: the step atomic
    if ((recv == null && n.equals("synchronized") && lam != null) || (recv != null && n.equals("withLock") && lam != null)) {
      Ctx in = new Ctx(new ArrayList<>(), new HashMap<>(c.locals), 0, c.init);
      List<Object> body = new ArrayList<>();
      for (KtExpression s : lam.getBodyExpression().getStatements()) body.addAll(stmt(s, in, null));
      if (!stmt) return no1(ce, "synchronized as a value");
      return new X(x("$stmts", p, "ss", List.of(with(body, p, t))), null);
    }
    // scope functions
    if (recv != null && lam != null && vas.isEmpty() && Set.of("let", "also", "run", "apply", "takeIf", "takeUnless").contains(n)) {
      if (n.equals("run") || n.equals("apply")) return no1(ce, n + " (a lambda with a receiver)");
      if (n.equals("takeIf") || n.equals("takeUnless")) {
        String v = "$take" + (tmp++);
        c.pre.add(s("set", p, "to", var(v, p), "x", recv.ir()));
        c.locals.put(v, recv.t());
        X pred = inline(lam, null, new X(var(v, p), recv.t()), c, false, p);
        Map<String, Object> cnd = n.equals("takeIf") ? pred.ir() : not(pred.ir(), p);
        return new X(x("ite", p, "c", cnd, "a", var(v, p), "b", x("none", p)), recv.t() == null ? null : recv.t().nullable(true));
      }
      X body = inline(lam, null, recv, c, stmt && n.equals("let"), p);
      return n.equals("also") ? recv : body;
    }
    List<Map<String, Object>> args = new ArrayList<>();
    List<JT> argT = new ArrayList<>();
    List<Object> kw = new ArrayList<>();
    boolean pure = true;
    // the class's own function: its parameters' types given to the arguments
    KtNamedFunction own = recv == null && staticOwner == null ? method(n, vas.size()) : recv != null && recv.t() != null && (recv.t().n.equals(selfName) || chain(self).stream().anyMatch(k -> binOf(k).equals(recv.t().n))) ? method(n, vas.size()) : null;
    for (int i = 0; i < vas.size(); i++) {
      KtValueArgument a = vas.get(i);
      JT pt = own != null && i < own.getValueParameters().size() ? type(own.getValueParameters().get(i).getTypeReference()) : null;
      X v = ex(a.getArgumentExpression(), c.under(), pt);
      pure &= v.ir().toString().indexOf("call") < 0;
      if (a.getArgumentName() != null) { kw.add(List.of(a.getArgumentName().getAsName().asString(), v.ir())); continue; }
      args.add(pt != null && num(pt) ? at(v.ir(), v.t(), pt) : v.ir());
      argT.add(pt != null && num(pt) ? pt : v.t());
    }
    if (own != null) {
      KtClassOrObject k = ownerOf(own);
      Map<String, Object> f = get(recv == null ? self(p) : recv.ir(), key(k, own), p, n);
      return new X(m("e", "call", "p", p, "text", t, "f", f, "args", args, "kw", kw), type(own.getTypeReference()));
    }
    if (recv == null && staticOwner == null && n.equals("copy") || (recv != null && n.equals("copy") && recv.t() != null && classes.get(recv.t().n) instanceof KtClass kc && kc.isData())) {
      if (!args.isEmpty()) return no1(ce, "copy given arguments by position");
      List<Object> fs = new ArrayList<>();
      for (Object k0 : kw) fs.add(k0);
      return new X(x("upd", p, "x", recv == null ? self(p) : recv.ir(), "fields", fs, "text", t), recv == null ? new JT(selfName) : recv.t());
    }
    // a constructor: a class of the code's own (made from its fields), an atomic, a map, a lock
    String ctorOf = recv == null && Character.isUpperCase(n.charAt(0)) ? resolve(n) : null;
    if (ctorOf != null) {
      JT ty = new JT(ctorOf);
      if (atomic(ty)) return new X(args.isEmpty() ? lit(0, held(ty), p) : at(args.get(0), argT.get(0), held(ty)), ty);
      if (map(ty)) return new X(x("dict", p, "keys", List.of(), "vals", List.of(), "text", t), ty);
      if (LOCKS.contains(ty.n) || ty.is("java.lang.Object")) return new X(lock(p, t), ty);
      String r = rec(ctorOf);
      if (r != null) return new X(m("e", "call", "p", p, "text", t, "f", x("cls", p, "rec", r), "args", args, "kw", kw), ty);
      if (ctorOf.equals(selfName)) return no1(ce, "an object of the class read made inside it");
    }
    if (recv == null && (n.equals("mutableMapOf") || n.equals("hashMapOf") || n.equals("linkedMapOf")) && args.isEmpty()) return new X(x("dict", p, "keys", List.of(), "vals", List.of(), "text", t), new JT("java.util.Map"));
    if (recv == null && n.equals("atomic") && args.size() == 1) return new X(args.get(0), new JT("kotlinx.atomicfu.Atomic" + (argT.get(0) != null && "long".equals(prim(argT.get(0))) ? "Long" : "Int")));
    if (recv != null && recv.t() != null && integral(recv.t()) && args.size() <= 2) {
      JT rt = recv.t();
      switch (n) {
        case "coerceAtLeast": return new X(x("minmax", p, "op", "max", "xs", List.of(at(recv.ir(), rt, rt), at(args.get(0), argT.get(0), rt)), "ity", ity(rt), "text", t), rt);
        case "coerceAtMost": return new X(x("minmax", p, "op", "min", "xs", List.of(at(recv.ir(), rt, rt), at(args.get(0), argT.get(0), rt)), "ity", ity(rt), "text", t), rt);
        case "coerceIn": if (args.size() == 2) return new X(x("minmax", p, "op", "max", "xs", List.of(at(args.get(0), argT.get(0), rt), x("minmax", p, "op", "min", "xs", List.of(at(recv.ir(), rt, rt), at(args.get(1), argT.get(1), rt)), "ity", ity(rt))), "ity", ity(rt), "text", t), rt); break;
        case "toLong": return new X(at(recv.ir(), rt, new JT("long")), new JT("long"));
        case "toInt": return "int".equals(prim(rt)) ? recv : new X(x("conv", p, "x", recv.ir(), "ity", ity(new JT("int")), "why", t), new JT("int"));
        case "absoluteValue": break;
      }
    }
    if (recv == null && (n.equals("minOf") || n.equals("maxOf")) && args.size() == 2) { JT w = promote(argT.get(0), argT.get(1)); return new X(x("minmax", p, "op", n.equals("minOf") ? "min" : "max", "xs", List.of(at(args.get(0), argT.get(0), w), at(args.get(1), argT.get(1), w)), "ity", ity(w), "why", t, "text", t), w); }
    if (recv == null && n.equals("TODO")) return stmt ? new X(x("$stmts", p, "ss", List.of(fail(p, t + " (a NotImplementedError)"))), null) : no1(ce, "TODO as a value");
    // the library, through the JVM layer
    String owner = staticOwner != null ? staticOwner.n : recv == null ? "kotlin.StandardKt" : recv.t() == null ? "?" : recv.t().n;
    JT out = want;
    if (recv != null && recv.t() != null && map(recv.t())) out = n.equals("get") || n.equals("remove") || n.equals("put") ? recv.t().arg(1).nullable(true) : n.equals("getOrDefault") || n.equals("getValue") ? recv.t().arg(1) : n.equals("containsKey") ? new JT("boolean") : want;
    if (recv != null && recv.t() != null && atomic(recv.t())) out = Set.of("compareAndSet", "weakCompareAndSet").contains(n) ? new JT("boolean") : held(recv.t());
    if (staticOwner != null && staticOwner.is("java.lang.System")) out = new JT("long");
    if ((n.equals("check") || n.equals("require") || n.equals("error")) && recv == null) out = new JT("void");
    Low l = lib(new Jvm.Call(owner, n, recv == null ? null : recv.ir(), recv == null ? staticOwner : recv.t(), args, argT, out, p, t, stmt, pure));
    if (l != null) {
      if (l.x() != null && "clock".equals(l.x().get("e"))) rewrites.add(m("span", span(ce.getParent() instanceof KtDotQualifiedExpression dq && dq.getSelectorExpression() == ce ? dq : ce), "to", "now"));
      if (l.ss() != null) return new X(x("$stmts", p, "ss", l.ss()), null);
      JT rt = out;
      if ("expect".equals(l.x().get("e")) && !args.isEmpty()) rt = argT.get(0) == null ? null : argT.get(0).nullable(false);
      return new X(l.x(), rt);
    }
    PsiElement site = ce.getParent() instanceof KtDotQualifiedExpression dq && dq.getSelectorExpression() == ce ? dq : ce;
    String callee = recv == null ? n : text(((KtDotQualifiedExpression) site).getReceiverExpression()).replace("this.", "") + "." + n;
    return new X(m("e", "call", "p", p, "text", t, "f", x("ext", p, "q", owner + "." + n, "text", callee, "patch", m("mod", owner, "path", List.of(n))), "args", args, "kw", kw,
      "jt", String.valueOf(want), "decl", owner, "span", span(site), "tag", tag(site)), want);
  }
}
