// The extractor's Java reader (core/extract-jvm.ts): a class read through the JDK's own compiler (javac's tree API,
// com.sun.source, its types attributed by javac against the project's sources and classpath) and lowered into the
// shared step IR (core/extract-step.ts's SModule, as JSON on stdout). Nothing here decides what is in the subset beyond
// the syntax: a construct the IR has no node for becomes {"e": "no"} or {"s": "no"} with the reason, refused by the
// executor only where a step reaches it. Java's semantics are made explicit as the IR's operations: int and long
// arithmetic wraps at its width (binary promotion as `as` on the operands), Math's exact arithmetic traps, / and %
// truncate, a switch is a chain of ifs inside a block a break leaves, a compare-and-set loop is its first pass,
// synchronized and a ReentrantLock's lock()/finally unlock() make the step atomic, a throw is the step's failure.
//
//   java -cp <tools> gdp.jvm.JavaReader '{"root": <dir>, "file": <file>, "names": ["Class"], "classpath": "<cp>"}'
package gdp.jvm;

import com.sun.source.tree.*;
import com.sun.source.util.*;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import javax.lang.model.element.*;
import javax.lang.model.type.*;
import javax.lang.model.util.*;
import javax.tools.*;
import static gdp.jvm.Jvm.*;

public final class JavaReader implements Jvm.Env {
  Trees trees; Elements els; Types types; SourcePositions sp;
  final Map<String, Object> recs = new LinkedHashMap<>(), funcs = new LinkedHashMap<>();
  final List<Object> rewrites = new ArrayList<>();
  final Map<String, Object> jvm = new LinkedHashMap<>();
  final Set<String> reading = new HashSet<>();
  // The class whose method is being lowered (its own calls are inlined), and the file's `// gdp:` tags.
  TypeElement self;
  final Map<CompilationUnitTree, TreeMap<Integer, String>> tagsOf = new HashMap<>();
  int tmp = 0;

  public static void main(String[] argv) throws Exception {
    Map<?, ?> req = (Map<?, ?>) parse(argv[0]);
    JavaReader r = new JavaReader();
    System.out.println(json(r.read(req)));
  }

  Map<String, Object> read(Map<?, ?> req) throws IOException {
    String root = (String) req.get("root"), file = (String) req.get("file"), cp = (String) req.get("classpath");
    JavaCompiler jc = ToolProvider.getSystemJavaCompiler();
    StandardJavaFileManager fm = jc.getStandardFileManager(null, null, StandardCharsets.UTF_8);
    List<String> opts = new ArrayList<>(List.of("-proc:none", "-Xlint:none", "-sourcepath", root));
    if (cp != null && !cp.isEmpty()) { opts.add("-cp"); opts.add(cp); }
    List<String> errs = new ArrayList<>();
    JavacTask task = (JavacTask) jc.getTask(new StringWriter(), fm, d -> { if (d.getKind() == Diagnostic.Kind.ERROR) errs.add(d.getMessage(null)); }, opts, null, fm.getJavaFileObjects(file));
    Iterable<? extends CompilationUnitTree> cus = task.parse();
    task.analyze();
    trees = Trees.instance(task); els = task.getElements(); types = task.getTypes(); sp = trees.getSourcePositions();
    CompilationUnitTree cu = cus.iterator().next();
    Map<String, Object> out = m("lang", "java", "file", new File(file).getName(), "path", new File(file).getAbsolutePath(), "module", pkg(cu), "root", new File(root).getAbsolutePath());
    List<Object> entries = new ArrayList<>();
    for (Object n : (List<?>) req.get("names")) {
      TypeElement te = find(cu, (String) n);
      if (te == null) { entries.add(m("k", "missing", "name", n)); continue; }
      jvm.put("ctorArity", req.get("ctor"));
      entries.add(m("k", "class", "rec", entry(te)));
    }
    out.put("entries", entries); out.put("recs", recs); out.put("funcs", funcs);
    jvm.put("rewrites", rewrites);
    if (!errs.isEmpty()) jvm.put("javac", errs.subList(0, Math.min(5, errs.size())));
    out.put("jvm", jvm);
    return out;
  }
  static String pkg(CompilationUnitTree cu) { return cu.getPackageName() == null ? "" : cu.getPackageName().toString(); }
  TypeElement find(CompilationUnitTree cu, String name) {
    List<TypeElement> all = new ArrayList<>();
    new TreePathScanner<Void, Void>() { @Override public Void visitClass(ClassTree c, Void v) { Element e = trees.getElement(getCurrentPath()); if (e instanceof TypeElement t) all.add(t); return super.visitClass(c, v); } }.scan(cu, null);
    for (TypeElement t : all) { String q = t.getQualifiedName().toString(); if (q.equals(name) || q.endsWith("." + name) || t.getSimpleName().contentEquals(name)) return t; }
    return null;
  }

  // --- positions and text --------------------------------------------------------------------------------------------
  CompilationUnitTree cuOf(TreePath p) { return p.getCompilationUnit(); }
  String where(TreePath path, Tree t) {
    CompilationUnitTree cu = path.getCompilationUnit();
    long s = sp.getStartPosition(cu, t);
    if (s < 0) return new File(cu.getSourceFile().getName()).getName() + ":0:0";
    return new File(cu.getSourceFile().getName()).getName() + ":" + cu.getLineMap().getLineNumber(s) + ":" + cu.getLineMap().getColumnNumber(s);
  }
  String text(TreePath path, Tree t) {
    try {
      CompilationUnitTree cu = path.getCompilationUnit();
      String src = cu.getSourceFile().getCharContent(true).toString();
      long s = sp.getStartPosition(cu, t), e = sp.getEndPosition(cu, t);
      if (s < 0 || e < s) return t.toString();
      String x = src.substring((int) s, (int) e).replaceAll("\\s+", " ");
      return x.length() <= 60 ? x : x.substring(0, 57) + "...";
    } catch (IOException ex) { return t.toString(); }
  }
  List<Object> span(TreePath path, Tree t) { CompilationUnitTree cu = path.getCompilationUnit(); return List.of(sp.getStartPosition(cu, t), sp.getEndPosition(cu, t)); }
  String tag(TreePath path, Tree t) {
    CompilationUnitTree cu = path.getCompilationUnit();
    TreeMap<Integer, String> tg = tagsOf.computeIfAbsent(cu, c -> { try { return tags(c.getSourceFile().getCharContent(true).toString()); } catch (IOException e) { return new TreeMap<>(); } });
    long s = sp.getStartPosition(cu, t), e = sp.getEndPosition(cu, t);
    if (s < 0) return null;
    int l0 = (int) cu.getLineMap().getLineNumber(s), l1 = (int) cu.getLineMap().getLineNumber(Math.max(s, Math.min(e, s + 1)));
    var hit = tg.subMap(l0, true, Math.max(l0, l1), true);
    return hit.isEmpty() ? null : String.join("; ", hit.values());
  }

  // --- types ---------------------------------------------------------------------------------------------------------
  JT jt(TypeMirror tm) {
    if (tm == null) return null;
    switch (tm.getKind()) {
      case INT: case LONG: case SHORT: case BYTE: case CHAR: case BOOLEAN: case FLOAT: case DOUBLE: case VOID: return new JT(tm.getKind().name().toLowerCase());
      case DECLARED: {
        DeclaredType d = (DeclaredType) tm;
        List<JT> as = new ArrayList<>();
        for (TypeMirror a : d.getTypeArguments()) { JT x = jt(a); as.add(x == null ? new JT("java.lang.Object") : x); }
        return new JT(((TypeElement) d.asElement()).getQualifiedName().toString(), as, false);
      }
      case WILDCARD: { TypeMirror b = ((WildcardType) tm).getExtendsBound(); return b == null ? new JT("java.lang.Object") : jt(b); }
      case TYPEVAR: return new JT("typevar:" + tm);
      case ARRAY: return new JT("array:" + tm);
      case NULL: return new JT("null");
      default: return null;
    }
  }
  JT ty(TreePath pp, Tree t) { try { return jt(trees.getTypeMirror(new TreePath(pp, t))); } catch (RuntimeException e) { return null; } }
  String erased(TypeMirror tm) {
    TypeMirror e = types.erasure(tm);
    if (e.getKind() == TypeKind.DECLARED) return els.getBinaryName((TypeElement) ((DeclaredType) e).asElement()).toString();
    return e.toString();
  }
  @Override public List<String> enumValues(String fq) {
    TypeElement te = els.getTypeElement(fq);
    if (te == null || te.getKind() != ElementKind.ENUM) return null;
    List<String> out = new ArrayList<>();
    for (Element e : te.getEnclosedElements()) if (e.getKind() == ElementKind.ENUM_CONSTANT) out.add(e.getSimpleName().toString());
    return out;
  }
  // A class of the code's own sources read as a record (a value): a Java record, or a class whose fields its one
  // constructor sets from its arguments (Lombok's @Value, @Data and plain beans too).
  @Override public String rec(String fq) {
    TypeElement te = els.getTypeElement(fq);
    if (te == null || trees.getPath(te) == null || te.getKind() == ElementKind.ENUM || te.getKind() == ElementKind.INTERFACE) return null;
    String name = els.getBinaryName(te).toString();
    if (recs.containsKey(name) || reading.contains(name)) return name;
    return valueRec(te);
  }
  Map<String, Object> st(TypeMirror tm) { JT t = jt(tm); return stype(t, this); }
  boolean iface(TypeMirror tm) { return tm.getKind() == TypeKind.DECLARED && ((DeclaredType) tm).asElement().getKind() == ElementKind.INTERFACE; }
  List<Object> annos(TreePath path, List<? extends AnnotationTree> as) {
    List<Object> out = new ArrayList<>();
    for (AnnotationTree a : as) {
      TypeMirror t = trees.getTypeMirror(new TreePath(path, a.getAnnotationType()));
      String fq = t != null && t.getKind() == TypeKind.DECLARED ? ((TypeElement) ((DeclaredType) t).asElement()).getQualifiedName().toString() : a.getAnnotationType().toString();
      out.add(anno(fq.substring(fq.lastIndexOf('.') + 1), fq, a.toString()));
    }
    return out;
  }
  static boolean has(List<Object> annos, String name) { for (Object a : annos) if (name.equals(((Map<?, ?>) a).get("name"))) return true; return false; }

  // --- the classes ---------------------------------------------------------------------------------------------------
  // The class read (its supertypes of the code's own sources merged in): its fields, its constructor as __init__, its
  // methods; what the harness is told (its binary name, each method's JVM name and parameter types).
  List<TypeElement> chain(TypeElement te) {
    List<TypeElement> out = new ArrayList<>();
    for (TypeElement t = te; t != null && trees.getPath(t) != null; ) {
      out.add(t);
      TypeMirror sup = t.getSuperclass();
      t = sup.getKind() == TypeKind.DECLARED ? (TypeElement) ((DeclaredType) sup).asElement() : null;
    }
    return out;
  }
  String entry(TypeElement te) {
    String name = els.getBinaryName(te).toString();
    reading.add(name);
    self = te;
    TreePath cpath = trees.getPath(te);
    ClassTree ct = (ClassTree) cpath.getLeaf();
    List<String> kinds = new ArrayList<>();
    if (!te.getTypeParameters().isEmpty()) kinds.add("generic:" + te.getTypeParameters());
    if (te.getNestingKind() == NestingKind.MEMBER && !te.getModifiers().contains(Modifier.STATIC) && te.getKind() == ElementKind.CLASS) return refusedRec(te, name, "an inner class (it holds its outer object; the subset reads a top-level or static nested class)");
    if (te.getModifiers().contains(Modifier.ABSTRACT)) kinds.add("abstract");
    List<TypeElement> ch = chain(te);
    Map<String, Object> methods = new LinkedHashMap<>(), sigs = new LinkedHashMap<>();
    List<Object> fields = new ArrayList<>(), jfields = new ArrayList<>();
    // fields, from the root class down
    for (int i = ch.size() - 1; i >= 0; i--) {
      TypeElement c = ch.get(i);
      TreePath cp = trees.getPath(c);
      for (Element e : c.getEnclosedElements()) {
        if (e.getKind() != ElementKind.FIELD || e.getModifiers().contains(Modifier.STATIC)) continue;
        VariableTree vt = (VariableTree) trees.getTree(e);
        TreePath vp = trees.getPath(e);
        JT t = jt(e.asType());
        if (t != null && nullable(c, (VariableElement) e, vt)) t = t.nullable(true);
        fields.add(m("name", e.getSimpleName().toString(), "t", stype(t, this)));
        jfields.add(m("name", e.getSimpleName().toString(), "jt", String.valueOf(t), "iface", iface(e.asType()) ? true : null, "annos", vp == null ? null : annos(vp, vt.getModifiers().getAnnotations()), "tag", vp == null ? null : tag(vp, vt)));
      }
    }
    // methods: each class's own, the subclass's overriding (a private or overloaded one keyed apart)
    Set<String> seen = new HashSet<>();
    for (TypeElement c : ch) {
      for (Element e : c.getEnclosedElements()) {
        if (e.getKind() != ElementKind.METHOD || e.getModifiers().contains(Modifier.ABSTRACT)) continue;
        ExecutableElement me = (ExecutableElement) e;
        String key = key(me);
        if (!seen.add(key)) continue;
        String id = fid(me);
        methods.put(key, id);
        sigs.put(key, sig(me));
        funcs.put(id, func(me));
      }
    }
    // the constructor: the one there is, or the one of the arity asked for
    List<ExecutableElement> ctors = new ArrayList<>();
    for (Element e : te.getEnclosedElements()) if (e.getKind() == ElementKind.CONSTRUCTOR) ctors.add((ExecutableElement) e);
    Object want = jvm.get("ctorArity");
    List<ExecutableElement> pick = ctors.stream().filter(c -> want == null || c.getParameters().size() == ((Number) want).intValue()).toList();
    Map<String, Object> jctor = m();
    if (pick.size() != 1) {
      methods.put("__init__", name + "#<init>");
      funcs.put(name + "#<init>", stub(te, cpath, "<init>", pick.isEmpty() ? "no constructor of the arity asked for (ctor)" : "a class with " + pick.size() + " constructors (name one by its arity: ctor)"));
    } else {
      ExecutableElement c = pick.get(0);
      methods.put("__init__", name + "#<init>");
      funcs.put(name + "#<init>", ctor(te, c, cpath));
      for (ExecutableElement o : ctors) if (o != c) { methods.put("__init__/" + o.getParameters().size(), fid(o)); funcs.put(fid(o), ctor(te, o, cpath)); }
      jctor = m("params", c.getParameters().stream().map(v -> erased(v.asType())).toList(), "names", c.getParameters().stream().map(v -> v.getSimpleName().toString()).toList(),
        "jts", c.getParameters().stream().map(v -> String.valueOf(jt(v.asType()))).toList(), "ifaces", c.getParameters().stream().map(v -> iface(v.asType())).toList(),
        "annos", trees.getPath(c) == null ? List.of() : annos(trees.getPath(c), ((MethodTree) trees.getTree(c)).getModifiers().getAnnotations()),
        "paramAnnos", trees.getPath(c) == null ? List.of() : ((MethodTree) trees.getTree(c)).getParameters().stream().map(v -> annos(trees.getPath(c), v.getModifiers().getAnnotations())).toList());
    }
    recs.put(name, m("name", name, "short", te.getSimpleName().toString(), "fields", fields, "methods", methods, "kinds", kinds, "own", true, "module", pkg(cpath.getCompilationUnit()), "p", where(cpath, ct),
      "jvm", m("fields", jfields, "annos", annos(cpath, ct.getModifiers().getAnnotations()), "ctor", jctor)));
    jvm.put("cls", name);
    jvm.put("ctor", jctor.get("params"));
    jvm.put("methods", sigs);
    reading.remove(name);
    return name;
  }
  String refusedRec(TypeElement te, String name, String why) {
    TreePath cp = trees.getPath(te);
    funcs.put(name + "#<init>", stub(te, cp, "<init>", why));
    recs.put(name, m("name", name, "short", te.getSimpleName().toString(), "fields", List.of(), "methods", m("__init__", name + "#<init>"), "kinds", List.of(), "own", true, "module", pkg(cp.getCompilationUnit()), "p", where(cp, cp.getLeaf())));
    return name;
  }
  Map<String, Object> stub(TypeElement te, TreePath cp, String n, String why) {
    String p = where(cp, cp.getLeaf());
    return m("id", els.getBinaryName(te) + "#" + n, "name", n, "cls", els.getBinaryName(te).toString(), "p", p, "span", List.of(p.split(":")[0], 0, 0), "params", List.of(m("name", "self", "t", m("k", "any"), "self", true)), "ret", m("k", "none"), "body", List.of(sno(p, why)), "decorators", List.of());
  }
  // A reference field may be null where the class says so: @Nullable, null assigned to it, or no initializer that
  // the constructors don't all set.
  boolean nullable(TypeElement c, VariableElement f, VariableTree vt) {
    if (f.asType().getKind().isPrimitive()) return false;
    if (vt != null && vt.getModifiers().getAnnotations().stream().anyMatch(a -> a.getAnnotationType().toString().endsWith("Nullable"))) return true;
    JT t = jt(f.asType());
    if (t != null && (t.is("java.util.Optional") || atomic(t) || map(t) || LOCKS.contains(t.n))) return false;
    boolean[] nul = {vt != null && vt.getInitializer() != null && vt.getInitializer().getKind() == Tree.Kind.NULL_LITERAL};
    boolean[] setInCtor = {vt != null && vt.getInitializer() != null};
    TreePath cp = trees.getPath(c);
    new TreePathScanner<Void, Void>() {
      @Override public Void visitAssignment(AssignmentTree a, Void v) {
        Element e = trees.getElement(new TreePath(getCurrentPath(), a.getVariable()));
        if (f.equals(e)) {
          if (a.getExpression().getKind() == Tree.Kind.NULL_LITERAL) nul[0] = true;
          for (TreePath q = getCurrentPath(); q != null; q = q.getParentPath()) if (q.getLeaf() instanceof MethodTree mt && mt.getName().contentEquals("<init>")) setInCtor[0] = true;
        }
        return super.visitAssignment(a, v);
      }
    }.scan(cp, null);
    return nul[0] || !setInCtor[0];
  }
  String key(ExecutableElement me) {
    String n = me.getSimpleName().toString();
    TypeElement owner = (TypeElement) me.getEnclosingElement();
    long same = owner.getEnclosedElements().stream().filter(e -> e.getKind() == ElementKind.METHOD && e.getSimpleName().contentEquals(n)).count();
    String k = same > 1 ? n + "/" + me.getParameters().size() : n;
    boolean hidden = me.getModifiers().contains(Modifier.PRIVATE) || Set.of("equals", "hashCode", "toString").contains(n);
    return hidden ? "_" + k : k;
  }
  String fid(ExecutableElement me) { return els.getBinaryName((TypeElement) me.getEnclosingElement()) + "#" + me.getSimpleName() + "(" + String.join(",", me.getParameters().stream().map(v -> erased(v.asType())).toList()) + ")"; }
  Map<String, Object> sig(ExecutableElement me) { return m("name", me.getSimpleName().toString(), "params", me.getParameters().stream().map(v -> erased(v.asType())).toList(), "static", me.getModifiers().contains(Modifier.STATIC) ? true : null, "decl", els.getBinaryName((TypeElement) me.getEnclosingElement()).toString()); }
  // A value record: its fields (a record's components, or the class's fields), no constructor of its own (the executor
  // makes it from its fields in order), its getters read as the fields.
  String valueRec(TypeElement te) {
    String name = els.getBinaryName(te).toString();
    reading.add(name);
    List<Object> fields = new ArrayList<>();
    Map<String, Object> methods = new LinkedHashMap<>();
    List<String> fnames = new ArrayList<>();
    for (Element e : te.getEnclosedElements()) {
      if (e.getKind() != ElementKind.FIELD || e.getModifiers().contains(Modifier.STATIC)) continue;
      fnames.add(e.getSimpleName().toString());
      fields.add(m("name", e.getSimpleName().toString(), "t", st(e.asType())));
    }
    List<ExecutableElement> ctors = new ArrayList<>();
    for (Element e : te.getEnclosedElements()) if (e.getKind() == ElementKind.CONSTRUCTOR) ctors.add((ExecutableElement) e);
    boolean plain = te.getKind() == ElementKind.RECORD || ctors.stream().anyMatch(c -> c.getParameters().size() == fnames.size() && fnames.equals(assignedInOrder(c)));
    TreePath cp = trees.getPath(te);
    recs.put(name, m("name", name, "short", te.getSimpleName().toString(), "fields", fields, "methods", methods, "kinds", plain ? List.of("dataclass") : List.of("value"), "own", true, "module", pkg(cp.getCompilationUnit()), "p", where(cp, cp.getLeaf()), "jvm", m("record", te.getKind() == ElementKind.RECORD ? true : null)));
    reading.remove(name);
    return name;
  }
  // The fields a constructor sets from its arguments, in order (null where it does anything else).
  List<String> assignedInOrder(ExecutableElement c) {
    MethodTree mt = (MethodTree) trees.getTree(c);
    if (mt == null || mt.getBody() == null) return null;
    List<String> out = new ArrayList<>();
    for (StatementTree s : mt.getBody().getStatements()) {
      if (s instanceof ExpressionStatementTree es && es.getExpression() instanceof MethodInvocationTree mi && mi.getMethodSelect().toString().equals("super") && mi.getArguments().isEmpty()) continue;
      if (!(s instanceof ExpressionStatementTree es && es.getExpression() instanceof AssignmentTree a && a.getExpression() instanceof IdentifierTree id)) return null;
      String to = a.getVariable().toString().replace("this.", "");
      if (!to.equals(id.getName().toString()) || out.size() >= c.getParameters().size() || !c.getParameters().get(out.size()).getSimpleName().contentEquals(id.getName())) return null;
      out.add(to);
    }
    return out;
  }
  // The field a getter returns (`return f;` or `return this.f;`), for a value record's calls.
  String getter(ExecutableElement me) {
    TypeElement owner = (TypeElement) me.getEnclosingElement();
    if (owner.getKind() == ElementKind.RECORD && me.getParameters().isEmpty()) for (Element e : owner.getEnclosedElements()) if (e.getKind() == ElementKind.FIELD && e.getSimpleName().contentEquals(me.getSimpleName())) return e.getSimpleName().toString();
    MethodTree mt = (MethodTree) trees.getTree(me);
    if (mt == null || mt.getBody() == null || mt.getBody().getStatements().size() != 1 || !me.getParameters().isEmpty()) {
      // Lombok: a getter generated for a field
      if (owner.getAnnotationMirrors().stream().anyMatch(a -> Set.of("Value", "Data", "Getter").contains(a.getAnnotationType().asElement().getSimpleName().toString()))) {
        String n = me.getSimpleName().toString();
        for (Element e : owner.getEnclosedElements()) if (e.getKind() == ElementKind.FIELD) { String f = e.getSimpleName().toString(); if (n.equals("get" + cap(f)) || n.equals("is" + cap(f))) return f; }
      }
      return null;
    }
    if (mt.getBody().getStatements().get(0) instanceof ReturnTree rt && rt.getExpression() != null) {
      String x = rt.getExpression().toString().replace("this.", "");
      for (Element e : owner.getEnclosedElements()) if (e.getKind() == ElementKind.FIELD && e.getSimpleName().contentEquals(x)) return x;
    }
    return null;
  }
  static String cap(String s) { return s.isEmpty() ? s : Character.toUpperCase(s.charAt(0)) + s.substring(1); }
  boolean own(TypeElement t) { return t != null && (chain(self).contains(t)); }

  // --- functions -------------------------------------------------------------------------------------------------------
  Map<String, Object> fn(ExecutableElement me, String id, String name, TreePath path, List<Object> body, List<Object> params) {
    CompilationUnitTree cu = path.getCompilationUnit();
    Tree t = path.getLeaf();
    long s = sp.getStartPosition(cu, t), e = sp.getEndPosition(cu, t);
    List<Object> ps = new ArrayList<>();
    if (!me.getModifiers().contains(Modifier.STATIC)) ps.add(m("name", "self", "t", m("k", "any"), "self", true));
    ps.addAll(params);
    return m("id", id, "name", name, "cls", els.getBinaryName((TypeElement) me.getEnclosingElement()).toString(), "p", where(path, t), "span", List.of(new File(cu.getSourceFile().getName()).getName(), cu.getLineMap().getLineNumber(Math.max(0, s)), cu.getLineMap().getLineNumber(Math.max(0, e))),
      "params", ps, "ret", st(me.getReturnType()), "body", body, "decorators", List.of(), "static", me.getModifiers().contains(Modifier.STATIC) ? true : null,
      "generic", me.getTypeParameters().isEmpty() ? null : true, "annos", annos(path, ((MethodTree) t).getModifiers().getAnnotations()), "tag", tag(path, t), "jt", String.valueOf(jt(me.getReturnType())));
  }
  List<Object> params(ExecutableElement me, TreePath path) {
    List<Object> out = new ArrayList<>();
    MethodTree mt = (MethodTree) path.getLeaf();
    for (int i = 0; i < me.getParameters().size(); i++) {
      VariableElement v = me.getParameters().get(i);
      out.add(m("name", v.getSimpleName().toString(), "t", pstype(jt(v.asType()), this), "jt", String.valueOf(jt(v.asType())), "iface", iface(v.asType()) ? true : null, "annos", annos(path, mt.getParameters().get(i).getModifiers().getAnnotations())));
    }
    return out;
  }
  Map<String, Object> func(ExecutableElement me) {
    TreePath path = trees.getPath(me);
    MethodTree mt = (MethodTree) path.getLeaf();
    String id = fid(me), p = where(path, mt);
    List<Object> body = new ArrayList<>();
    if (mt.getBody() == null) body.add(sno(p, me.getSimpleName() + ": a method with no body (native)"));
    else body.addAll(block(mt.getBody().getStatements(), new TreePath(path, mt.getBody())));
    if (me.getModifiers().contains(Modifier.SYNCHRONIZED)) body = new ArrayList<>(List.of(with(body, p, "synchronized " + me.getSimpleName())));
    return fn(me, id, me.getSimpleName().toString(), path, body, params(me, path));
  }
  // A constructor: its super(...) first (a superclass of the code's own sources: its constructor inlined), then the
  // fields' defaults and initializers in order (unless it delegates with this(...)), then its body.
  Map<String, Object> ctor(TypeElement te, ExecutableElement c, TreePath cpath) {
    TreePath path = trees.getPath(c);
    MethodTree mt = path == null ? null : (MethodTree) path.getLeaf();
    String p = path == null ? where(cpath, cpath.getLeaf()) : where(path, mt);
    String z = p.split(":")[0] + ":0:0";
    List<Object> body = new ArrayList<>();
    List<? extends StatementTree> ss = mt == null || mt.getBody() == null ? List.of() : mt.getBody().getStatements();
    boolean delegates = false;
    if (!ss.isEmpty() && ss.get(0) instanceof ExpressionStatementTree es && es.getExpression() instanceof MethodInvocationTree mi && (mi.getMethodSelect().toString().equals("super") || mi.getMethodSelect().toString().equals("this"))) {
      TreePath bp = new TreePath(path, mt.getBody());
      TreePath ip = new TreePath(new TreePath(bp, es), mi);
      ExecutableElement callee = (ExecutableElement) trees.getElement(ip);
      List<Object> args = new ArrayList<>();
      for (ExpressionTree a : mi.getArguments()) args.add(ex(a, ip));
      if (mi.getMethodSelect().toString().equals("this")) { delegates = true; body.add(s("expr", p, "x", call(get(self(p), "__init__/" + callee.getParameters().size(), p, "this"), args, p, text(ip, mi)))); }
      else if (callee != null && trees.getPath(callee) != null) {
        String sid = fid(callee);
        if (!funcs.containsKey(sid)) funcs.put(sid, ctor((TypeElement) callee.getEnclosingElement(), callee, trees.getPath(callee.getEnclosingElement())));
        args.add(0, self(p));
        body.add(s("expr", p, "x", call(x("fn", p, "id", sid), args, p, text(ip, mi))));
      } else if (callee != null && !((TypeElement) callee.getEnclosingElement()).getQualifiedName().contentEquals("java.lang.Object")) body.add(sno(p, "super(...): a superclass of other code (its constructor and fields unread)"));
      ss = ss.subList(1, ss.size());
    } else if (te.getSuperclass().getKind() == TypeKind.DECLARED) {
      TypeElement sup = (TypeElement) ((DeclaredType) te.getSuperclass()).asElement();
      if (trees.getPath(sup) != null) {
        ExecutableElement sc = null;
        for (Element e : sup.getEnclosedElements()) if (e.getKind() == ElementKind.CONSTRUCTOR && ((ExecutableElement) e).getParameters().isEmpty()) sc = (ExecutableElement) e;
        if (sc != null) { String sid = fid(sc); if (!funcs.containsKey(sid)) funcs.put(sid, ctor(sup, sc, trees.getPath(sup))); body.add(s("expr", p, "x", call(x("fn", p, "id", sid), List.of(self(p)), p, "super()"))); }
      }
    }
    if (!delegates) {
      ClassTree ct = (ClassTree) cpath.getLeaf();
      for (Tree mem : ct.getMembers()) {
        TreePath mp = new TreePath(cpath, mem);
        if (mem instanceof VariableTree vt) {
          VariableElement f = (VariableElement) trees.getElement(mp);
          if (f == null || f.getModifiers().contains(Modifier.STATIC)) continue;
          Map<String, Object> to = get(self(z), vt.getName().toString(), z, "this." + vt.getName());
          JT t = jt(f.asType());
          if (t != null && nullable(te, f, vt)) t = t.nullable(true);
          Map<String, Object> init = vt.getInitializer() == null ? zero(t, z) : at(ex(vt.getInitializer(), mp), ty(mp, vt.getInitializer()), atomic(t) ? held(t) : t);
          body.add(s("set", vt.getInitializer() == null ? z : where(mp, vt), "to", to, "x", init, "t", stype(t, this)));
        } else if (mem instanceof BlockTree bt && !bt.isStatic()) body.addAll(block(bt.getStatements(), mp));
      }
    }
    if (mt != null && mt.getBody() != null) body.addAll(block(ss, new TreePath(path, mt.getBody())));
    List<Object> ps = new ArrayList<>(List.of(m("name", "self", "t", m("k", "any"), "self", true)));
    if (path != null) ps.addAll(params(c, path)); else ps.addAll(c.getParameters().stream().map(v -> (Object) m("name", v.getSimpleName().toString(), "t", st(v.asType()))).toList());
    String id = fid(c);
    return m("id", id, "name", "__init__", "cls", els.getBinaryName(te).toString(), "p", p, "span", List.of(p.split(":")[0], 0, 0), "params", ps, "ret", m("k", "none"), "body", body, "decorators", List.of());
  }
  Map<String, Object> zero(JT t, String p) {
    if (t == null) return x("none", p);
    if (t.nul) return x("none", p);
    String q = prim(t);
    if (q != null) return q.equals("boolean") ? x("bool", p, "v", false) : floating(t) ? x("int", p, "v", "0", "float", true) : lit(0, t, p);
    return x("none", p);
  }

  // --- statements ----------------------------------------------------------------------------------------------------
  List<Object> block(List<? extends StatementTree> ss, TreePath pp) {
    List<Object> out = new ArrayList<>();
    for (int i = 0; i < ss.size(); i++) {
      StatementTree s = ss.get(i);
      TreePath sp1 = new TreePath(pp, s);
      // lock.lock(); try { ... } finally { lock.unlock(); }: the step atomic
      if (i + 1 < ss.size() && lockCall(s, "lock") != null && ss.get(i + 1) instanceof TryTree tt && tt.getCatches().isEmpty() && tt.getFinallyBlock() != null
          && tt.getFinallyBlock().getStatements().size() == 1 && Objects.equals(lockCall(tt.getFinallyBlock().getStatements().get(0), "unlock"), lockCall(s, "lock"))) {
        TreePath tp = new TreePath(pp, tt);
        out.add(with(block(tt.getBlock().getStatements(), new TreePath(tp, tt.getBlock())), where(sp1, s), text(sp1, s)));
        i++;
        continue;
      }
      out.addAll(stmt(s, sp1));
    }
    return out;
  }
  static String lockCall(StatementTree s, String m) {
    if (s instanceof ExpressionStatementTree es && es.getExpression() instanceof MethodInvocationTree mi && mi.getArguments().isEmpty() && mi.getMethodSelect() instanceof MemberSelectTree ms && ms.getIdentifier().contentEquals(m))
      return ms.getExpression().toString().replace("this.", "");
    return null;
  }
  List<Object> stmt(StatementTree s, TreePath path) {
    String p = where(path, s);
    switch (s.getKind()) {
      case BLOCK: return block(((BlockTree) s).getStatements(), path);
      case EMPTY_STATEMENT: return List.of();
      case VARIABLE: {
        VariableTree v = (VariableTree) s;
        JT t = jt(trees.getElement(path).asType());
        Map<String, Object> init = v.getInitializer() == null ? zero(t, p) : at(ex(v.getInitializer(), path), ty(path, v.getInitializer()), t);
        return List.of(s("set", p, "to", var(v.getName().toString(), p), "x", init, "t", stype(t, this)));
      }
      case EXPRESSION_STATEMENT: return exprStmt(((ExpressionStatementTree) s).getExpression(), new TreePath(path, ((ExpressionStatementTree) s).getExpression()), p);
      case IF: {
        IfTree it = (IfTree) s;
        List<Object> el = it.getElseStatement() == null ? List.of() : stmt(it.getElseStatement(), new TreePath(path, it.getElseStatement()));
        return List.of(s("if", p, "c", ex(it.getCondition(), path), "then", stmt(it.getThenStatement(), new TreePath(path, it.getThenStatement())), "else", el));
      }
      case RETURN: {
        ReturnTree r = (ReturnTree) s;
        if (r.getExpression() == null) return List.of(s("ret", p));
        TreePath mp = path; while (mp != null && !(mp.getLeaf() instanceof MethodTree)) mp = mp.getParentPath();
        JT rt = mp == null ? null : jt(((ExecutableElement) trees.getElement(mp)).getReturnType());
        return List.of(s("ret", p, "x", at(ex(r.getExpression(), path), ty(path, r.getExpression()), rt)));
      }
      case THROW: return List.of(fail(p, text(path, s)));
      case SYNCHRONIZED: { SynchronizedTree st = (SynchronizedTree) s; return List.of(with(block(st.getBlock().getStatements(), new TreePath(path, st.getBlock())), p, "synchronized (" + st.getExpression().toString().replaceAll("^\\(|\\)$", "") + ")")); }
      case SWITCH: { SwitchTree sw = (SwitchTree) s; return sw(sw.getExpression(), sw.getCases(), path, p); }
      case BREAK: return ((BreakTree) s).getLabel() == null ? List.of(s("break", p)) : List.of(sno(p, "a labeled break"));
      case CONTINUE: return List.of(sno(p, "continue (a loop's next pass: the subset reads a compare-and-set loop's first)"));
      case ASSERT: return List.of();
      case WHILE_LOOP: { WhileLoopTree w = (WhileLoopTree) s; return once(w.getCondition(), w.getStatement(), path, p); }
      case DO_WHILE_LOOP: { DoWhileLoopTree w = (DoWhileLoopTree) s; return once(w.getCondition(), w.getStatement(), path, p); }
      case FOR_LOOP: { ForLoopTree f = (ForLoopTree) s; if (f.getCondition() == null && f.getInitializer().isEmpty() && f.getUpdate().isEmpty()) return once(null, f.getStatement(), path, p); return List.of(sno(p, "a loop")); }
      case ENHANCED_FOR_LOOP: return List.of(sno(p, "a loop over a collection"));
      case TRY: return List.of(sno(p, "try (an exception caught, or a finally of other than a lock's unlock: the subset reads an exception only as the step's failure)"));
      case LABELED_STATEMENT: return List.of(sno(p, "a labeled statement"));
      case YIELD: return List.of(sno(p, "yield (a switch expression's block)"));
      default: return List.of(sno(p, s.getKind().toString().toLowerCase().replace('_', ' ') + " (outside the subset)"));
    }
  }
  // while (true) / for (;;) / do ... while (true): a compare-and-set retry loop, read as its first pass (the CAS succeeds
  // the first time when calls don't interleave); a pass that would go around again is refused where it is reached.
  List<Object> once(ExpressionTree cond, StatementTree body, TreePath path, String p) {
    ExpressionTree c = cond; while (c instanceof ParenthesizedTree pt) c = pt.getExpression();
    if (c != null && !(c instanceof LiteralTree lt && Boolean.TRUE.equals(lt.getValue()))) return List.of(sno(p, "a loop"));
    List<Object> b = new ArrayList<>(stmt(body, new TreePath(path, body)));
    b.add(sno(p, "the loop goes around again (the subset reads a retry loop's first pass: a compare-and-set that succeeds when calls don't interleave)"));
    return List.of(breakable(b, p));
  }
  // A switch: a chain of ifs on ==, each case's arm its statements and those it falls through into, inside a block a
  // break leaves.
  List<Object> sw(ExpressionTree sel, List<? extends CaseTree> cases, TreePath path, String p) {
    List<Object> out = new ArrayList<>();
    String tv = "$sw" + (tmp++);
    out.add(s("set", p, "to", var(tv, p), "x", ex(sel, path)));
    JT st = ty(path, sel);
    List<List<Object>> bodies = new ArrayList<>();
    List<Boolean> ends = new ArrayList<>();
    for (CaseTree c : cases) {
      TreePath cp = new TreePath(path, c);
      List<Object> b = new ArrayList<>();
      if (c.getCaseKind() == CaseTree.CaseKind.RULE) {
        Tree body = c.getBody();
        if (body instanceof StatementTree bs) b.addAll(stmt(bs, new TreePath(cp, bs))); else b.add(s("expr", where(cp, body), "x", ex((ExpressionTree) body, cp)));
        ends.add(true);
      } else {
        b.addAll(block(c.getStatements(), cp));
        StatementTree last = c.getStatements().isEmpty() ? null : c.getStatements().get(c.getStatements().size() - 1);
        ends.add(last != null && (last instanceof BreakTree || last instanceof ReturnTree || last instanceof ThrowTree || last instanceof ContinueTree));
      }
      bodies.add(b);
    }
    // each case's arm: its body, and the next ones' while it falls through
    List<Object> chain = new ArrayList<>(), dflt = List.of();
    List<Object[]> arms = new ArrayList<>();
    for (int i = 0; i < cases.size(); i++) {
      List<Object> arm = new ArrayList<>();
      for (int j = i; j < cases.size(); j++) { arm.addAll(bodies.get(j)); if (ends.get(j)) break; }
      CaseTree c = cases.get(i);
      TreePath cp = new TreePath(path, c);
      if (c.getExpressions().isEmpty()) { dflt = arm; continue; }
      List<Object> conds = new ArrayList<>();
      for (ExpressionTree e : c.getExpressions()) conds.add(cmp("==", var(tv, p), label(e, new TreePath(cp, e), st), where(cp, e), text(cp, e)));
      arms.add(new Object[]{conds.size() == 1 ? conds.get(0) : x("or", where(cp, c), "xs", conds), arm, where(cp, c)});
    }
    List<Object> acc = dflt;
    for (int i = arms.size() - 1; i >= 0; i--) { @SuppressWarnings("unchecked") List<Object> a = (List<Object>) arms.get(i)[1]; acc = List.of(s("if", p.split(":")[0] + ":0:0", "c", arms.get(i)[0], "then", a, "else", acc)); }
    chain.addAll(acc);
    out.add(breakable(chain, p));
    return out;
  }
  Map<String, Object> label(ExpressionTree e, TreePath path, JT st) {
    Element el = trees.getElement(path);
    if (el != null && el.getKind() == ElementKind.ENUM_CONSTANT) return str(el.getSimpleName().toString(), where(path, e));
    return at(ex(e, path), ty(path, e), st);
  }
  // An expression used as a statement: an assignment, ++ and --, a call (a map's put, an atomic's set, a check).
  List<Object> exprStmt(ExpressionTree e, TreePath path, String p) {
    switch (e.getKind()) {
      case ASSIGNMENT: {
        AssignmentTree a = (AssignmentTree) e;
        TreePath vp = new TreePath(path, a.getVariable());
        JT t = ty(path, a.getVariable());
        return List.of(s("set", p, "to", place(a.getVariable(), path), "x", at(ex(a.getExpression(), path), ty(path, a.getExpression()), t)));
      }
      case PLUS_ASSIGNMENT: case MINUS_ASSIGNMENT: case MULTIPLY_ASSIGNMENT: case DIVIDE_ASSIGNMENT: case REMAINDER_ASSIGNMENT: {
        CompoundAssignmentTree a = (CompoundAssignmentTree) e;
        JT t = ty(path, a.getVariable()), u = ty(path, a.getExpression());
        String op = switch (e.getKind()) { case PLUS_ASSIGNMENT -> "+"; case MINUS_ASSIGNMENT -> "-"; case MULTIPLY_ASSIGNMENT -> "*"; case DIVIDE_ASSIGNMENT -> "/"; default -> "%"; };
        if (t != null && t.is("java.lang.String")) return List.of(s("set", p, "to", place(a.getVariable(), path), "x", x("bin", p, "op", "+", "x", ex(a.getVariable(), path), "y", ex(a.getExpression(), path), "text", text(path, e))));
        JT w = promote(t, u);
        Map<String, Object> v = arith(op, ex(a.getVariable(), path), t, ex(a.getExpression(), path), u, w, "wrap", p, text(path, e));
        return List.of(s("set", p, "to", place(a.getVariable(), path), "x", narrow(v, w, t, p)));
      }
      case PREFIX_INCREMENT: case POSTFIX_INCREMENT: case PREFIX_DECREMENT: case POSTFIX_DECREMENT: {
        ExpressionTree v = ((UnaryTree) e).getExpression();
        JT t = ty(path, v), w = promote(t, new JT("int"));
        boolean inc = e.getKind() == Tree.Kind.PREFIX_INCREMENT || e.getKind() == Tree.Kind.POSTFIX_INCREMENT;
        return List.of(s("set", p, "to", place(v, path), "x", narrow(arith(inc ? "+" : "-", ex(v, path), t, lit(1, w, p), w, w, "wrap", p, text(path, e)), w, t, p)));
      }
      case METHOD_INVOCATION: {
        Object r = invoke((MethodInvocationTree) e, path, true);
        if (r instanceof Low l && l.ss() != null) return l.ss();
        return List.of(s("expr", p, "x", r instanceof Low l ? l.x() : r));
      }
      default: return List.of(s("expr", p, "x", ex(e, path)));
    }
  }
  // A value computed at a wider type put back at a narrower one (a compound assignment's implicit cast): wrapped.
  Map<String, Object> narrow(Map<String, Object> v, JT from, JT to, String p) {
    if (to == null || from == null || Objects.equals(prim(from), prim(to)) || ity(to) == null) return v;
    return x("conv", p, "x", v, "ity", ity(to), "why", "a conversion");
  }
  Map<String, Object> place(ExpressionTree v, TreePath path) {
    TreePath vp = new TreePath(path, v);
    Element el = trees.getElement(vp);
    String p = where(vp, v);
    if (el != null && el.getKind() == ElementKind.FIELD && !el.getModifiers().contains(Modifier.STATIC)) {
      Map<String, Object> o = v instanceof MemberSelectTree ms ? ex(ms.getExpression(), vp) : self(p);
      return get(o, el.getSimpleName().toString(), p, text(vp, v));
    }
    if (el != null && (el.getKind() == ElementKind.LOCAL_VARIABLE || el.getKind() == ElementKind.PARAMETER)) return var(el.getSimpleName().toString(), p);
    if (v instanceof ArrayAccessTree) return no(p, text(vp, v) + ": an array's item");
    if (el != null && el.getModifiers().contains(Modifier.STATIC)) return no(p, text(vp, v) + ": a static field (shared by every object, outside the object's state)");
    return no(p, text(vp, v) + ": an assignment the subset doesn't read");
  }

  // --- expressions ---------------------------------------------------------------------------------------------------
  Map<String, Object> ex(ExpressionTree e, TreePath pp) {
    TreePath path = new TreePath(pp, e);
    String p = where(path, e), t = text(path, e);
    JT type = ty(pp, e);
    switch (e.getKind()) {
      case PARENTHESIZED: return ex(((ParenthesizedTree) e).getExpression(), path);
      case INT_LITERAL: case LONG_LITERAL: return lit(((Number) ((LiteralTree) e).getValue()).longValue(), type, p);
      case CHAR_LITERAL: return lit((Character) ((LiteralTree) e).getValue(), new JT("char"), p);
      case BOOLEAN_LITERAL: return x("bool", p, "v", ((LiteralTree) e).getValue());
      case STRING_LITERAL: return str((String) ((LiteralTree) e).getValue(), p);
      case NULL_LITERAL: return x("none", p);
      case FLOAT_LITERAL: case DOUBLE_LITERAL: {
        double d = ((Number) ((LiteralTree) e).getValue()).doubleValue();
        return d == Math.floor(d) && Math.abs(d) < 9.007199254740992E15 ? x("int", p, "v", Long.toString((long) d), "float", true) : no(p, t + ": a float that isn't whole (a binary fraction)");
      }
      case IDENTIFIER: case MEMBER_SELECT: return name(e, path, p, t, type);
      case METHOD_INVOCATION: { Object r = invoke((MethodInvocationTree) e, pp, false); return r instanceof Low l ? (l.x() != null ? l.x() : no(p, t + ": a call used as a value")) : (Map<String, Object>) r; }
      case NEW_CLASS: return make((NewClassTree) e, path, p, t, type);
      case CONDITIONAL_EXPRESSION: { ConditionalExpressionTree c = (ConditionalExpressionTree) e; return x("ite", p, "c", ex(c.getCondition(), path), "a", at(ex(c.getTrueExpression(), path), ty(path, c.getTrueExpression()), type), "b", at(ex(c.getFalseExpression(), path), ty(path, c.getFalseExpression()), type)); }
      case LOGICAL_COMPLEMENT: return not(ex(((UnaryTree) e).getExpression(), path), p);
      case UNARY_MINUS: { ExpressionTree v = ((UnaryTree) e).getExpression(); if (floating(type)) return x("neg", p, "x", ex(v, path)); return x("unop", p, "op", "-", "x", at(ex(v, path), ty(path, v), type), "text", t); }
      case UNARY_PLUS: return ex(((UnaryTree) e).getExpression(), path);
      case TYPE_CAST: {
        TypeCastTree c = (TypeCastTree) e;
        JT from = ty(path, c.getExpression());
        Map<String, Object> v = ex(c.getExpression(), path);
        if (ity(type) == null || from == null) return v;
        // (a float's whole value into an integer: Java's saturates at the type's range)
        if (floating(from)) return x("bin", p, "op", "+", "x", x("as", p, "x", v, "ity", ity(type)), "y", lit(0, type, p), "ovf", "sat", "text", t);
        int fb = (int) ity(from).get("bits"), tb = (int) ity(type).get("bits");
        return tb >= fb && !"char".equals(prim(type)) ? x("as", p, "x", v, "ity", ity(type)) : x("conv", p, "x", v, "ity", ity(type), "why", t);
      }
      case SWITCH_EXPRESSION: return no(p, t + ": a switch expression (the subset reads switch statements)");
      case LAMBDA_EXPRESSION: case MEMBER_REFERENCE: return no(p, t + ": a lambda (a closure)");
      case INSTANCE_OF: return no(p, t + ": instanceof");
      case ASSIGNMENT: case PLUS_ASSIGNMENT: case MINUS_ASSIGNMENT: case PREFIX_INCREMENT: case POSTFIX_INCREMENT: case PREFIX_DECREMENT: case POSTFIX_DECREMENT: return no(p, t + ": an assignment inside an expression");
      case ARRAY_ACCESS: case NEW_ARRAY: return no(p, t + ": an array (outside the subset)");
      default: break;
    }
    if (e instanceof BinaryTree b) return binary(b, path, p, t, type);
    return no(p, t + ": " + e.getKind().toString().toLowerCase().replace('_', ' ') + " (outside the subset)");
  }
  Map<String, Object> binary(BinaryTree b, TreePath path, String p, String t, JT type) {
    JT ta = ty(path, b.getLeftOperand()), tb = ty(path, b.getRightOperand());
    Map<String, Object> l = ex(b.getLeftOperand(), path), r = ex(b.getRightOperand(), path);
    switch (b.getKind()) {
      case CONDITIONAL_AND: return x("and", p, "xs", List.of(l, r));
      case CONDITIONAL_OR: return x("or", p, "xs", List.of(l, r));
      case AND: case OR: if ("boolean".equals(prim(type))) return x(b.getKind() == Tree.Kind.AND ? "and" : "or", p, "xs", List.of(l, r)); return no(p, t + ": a bit operation (outside the subset)");
      case XOR: if ("boolean".equals(prim(type))) return cmp("!=", l, r, p, t); return no(p, t + ": a bit operation (outside the subset)");
      case EQUAL_TO: case NOT_EQUAL_TO: {
        boolean eq = b.getKind() == Tree.Kind.EQUAL_TO;
        if (b.getRightOperand().getKind() == Tree.Kind.NULL_LITERAL) return cmp(eq ? "is" : "is not", l, r, p, t);
        if (b.getLeftOperand().getKind() == Tree.Kind.NULL_LITERAL) return cmp(eq ? "is" : "is not", r, l, p, t);
        if (num(ta) && num(tb)) { JT w = promote(ta, tb); l = at(l, ta, w); r = at(r, tb, w); }
        return cmp(eq ? "==" : "!=", l, r, p, t);
      }
      case LESS_THAN: case LESS_THAN_EQUAL: case GREATER_THAN: case GREATER_THAN_EQUAL: {
        String op = switch (b.getKind()) { case LESS_THAN -> "<"; case LESS_THAN_EQUAL -> "<="; case GREATER_THAN -> ">"; default -> ">="; };
        return cmp(op, l, r, p, t);
      }
      case PLUS: case MINUS: case MULTIPLY: case DIVIDE: case REMAINDER: {
        if (type != null && type.is("java.lang.String")) return x("bin", p, "op", "+", "x", l, "y", r, "text", t);
        String op = switch (b.getKind()) { case PLUS -> "+"; case MINUS -> "-"; case MULTIPLY -> "*"; case DIVIDE -> "/"; default -> "%"; };
        if (floating(type) && (op.equals("/") || op.equals("%"))) return no(p, t + ": a float division (the subset reads whole numbers)");
        return arith(op, l, ta, r, tb, type, "wrap", p, t);
      }
      case LEFT_SHIFT: case RIGHT_SHIFT: return x("binop", p, "op", b.getKind() == Tree.Kind.LEFT_SHIFT ? "<<" : ">>", "x", at(l, ta, type), "y", r, "text", t);
      default: return no(p, t + ": a bit operation (outside the subset)");
    }
  }
  // A name: a local, a field of this object or another, a constant (folded), an enum's constant (a choice's literal).
  Map<String, Object> name(ExpressionTree e, TreePath path, String p, String t, JT type) {
    if (e instanceof IdentifierTree id && (id.getName().contentEquals("this") || id.getName().contentEquals("super"))) return self(p);
    Element el = trees.getElement(path);
    if (el == null) return no(p, t + ": a name javac couldn't resolve (its class not on the classpath?)");
    switch (el.getKind()) {
      case LOCAL_VARIABLE: case PARAMETER: case RESOURCE_VARIABLE: case BINDING_VARIABLE: case EXCEPTION_PARAMETER: return var(el.getSimpleName().toString(), p);
      case ENUM_CONSTANT: return str(el.getSimpleName().toString(), p);
      case FIELD: {
        VariableElement v = (VariableElement) el;
        Object k = v.getConstantValue();
        if (k instanceof Number n && !(k instanceof Double || k instanceof Float)) return lit(n.longValue(), jt(v.asType()), p);
        if (k instanceof Boolean bo) return x("bool", p, "v", bo);
        if (k instanceof String s) return str(s, p);
        if (k instanceof Character c) return lit(c, new JT("char"), p);
        if (v.getModifiers().contains(Modifier.STATIC)) {
          String q = ((TypeElement) v.getEnclosingElement()).getQualifiedName() + "." + v.getSimpleName();
          return x("opaque", p, "why", t + ": a static field (shared by every object, outside the object's state)", "q", q);
        }
        if (e instanceof MemberSelectTree ms) {
          if (ms.getExpression() instanceof IdentifierTree id && id.getName().contentEquals("this")) return get(self(p), v.getSimpleName().toString(), p, t);
          return get(ex(ms.getExpression(), path), v.getSimpleName().toString(), p, t);
        }
        return get(self(p), v.getSimpleName().toString(), p, t);
      }
      default:
        if (e instanceof IdentifierTree id && id.getName().contentEquals("this")) return self(p);
        if (e instanceof MemberSelectTree ms && ms.getIdentifier().contentEquals("length")) return no(p, t + ": an array's length");
        return no(p, t + ": " + el.getKind().toString().toLowerCase() + " (outside the subset)");
    }
  }
  // `new`: a record of the code's own (made from its fields), an atomic (its value), a map (empty), a lock or a
  // monitor (Object), an exception (only thrown); anything else is other code's object.
  Map<String, Object> make(NewClassTree n, TreePath path, String p, String t, JT type) {
    if (n.getClassBody() != null) return no(p, t + ": an anonymous class");
    List<Map<String, Object>> args = new ArrayList<>();
    ExecutableElement c = (ExecutableElement) trees.getElement(path);
    for (int i = 0; i < n.getArguments().size(); i++) {
      ExpressionTree a = n.getArguments().get(i);
      JT pt = c != null && i < c.getParameters().size() ? jt(c.getParameters().get(i).asType()) : null;
      args.add(at(ex(a, path), ty(path, a), pt));
    }
    if (type == null) return no(p, t + ": a class javac couldn't resolve");
    if (atomic(type)) return args.isEmpty() ? zero(held(type), p) : at(args.get(0), ty(path, n.getArguments().get(0)), held(type));
    if (map(type)) return args.isEmpty() || (n.getArguments().size() == 1 && num(ty(path, n.getArguments().get(0)))) ? x("dict", p, "keys", List.of(), "vals", List.of(), "text", t) : no(p, t + ": a map made from another");
    if (LOCKS.contains(type.n) || type.is("java.lang.Object")) return lock(p, t);
    String r = rec(type.n);
    if (r != null) return call(x("cls", p, "rec", r), args, p, t);
    return x("opaque", p, "why", t + ": an object of other code made", "jt", type.toString());
  }
  // A call: the class's own method (inlined), the library's (lowered), or other code's (`ext`: answered or skipped by
  // the caller, else refused). The site's span and type are kept for the check (an answered call's stub) and for the
  // boundary's inference (the callee's declared type, whether its owner is an interface).
  Object invoke(MethodInvocationTree mi, TreePath pp, boolean stmt) {
    TreePath path = new TreePath(pp, mi);
    String p = where(path, mi), t = text(path, mi);
    Element el = trees.getElement(path);
    if (!(el instanceof ExecutableElement me)) return no(p, t + ": a call javac couldn't resolve (its class not on the classpath?)");
    TypeElement owner = (TypeElement) me.getEnclosingElement();
    ExpressionTree sel = mi.getMethodSelect();
    Map<String, Object> recv = null;
    JT recvT = null;
    boolean isStatic = me.getModifiers().contains(Modifier.STATIC), sup = false;
    if (sel instanceof MemberSelectTree ms && !isStatic) {
      ExpressionTree r = ms.getExpression();
      if (r instanceof IdentifierTree id && id.getName().contentEquals("super")) { sup = true; recv = self(p); }
      else { recv = ex(r, path); recvT = ty(path, r); }
    } else if (!isStatic) recv = self(p);
    List<Map<String, Object>> args = new ArrayList<>();
    List<JT> argT = new ArrayList<>();
    boolean pure = true;
    for (int i = 0; i < mi.getArguments().size(); i++) {
      ExpressionTree a = mi.getArguments().get(i);
      JT pt = i < me.getParameters().size() && !me.isVarArgs() ? jt(me.getParameters().get(i).asType()) : null;
      JT at0 = ty(path, a);
      args.add(pt != null && num(pt) ? at(ex(a, path), at0, pt) : ex(a, path));
      argT.add(pt != null && num(pt) ? pt : at0);
      pure &= pure(a);
    }
    JT out = ty(pp, mi);
    String oq = owner.getQualifiedName().toString(), n = me.getSimpleName().toString();
    if (own(owner) || (recvT != null && rec(recvT.n) != null && trees.getPath(owner) != null)) {
      if (isStatic) { String id = fid(me); if (!funcs.containsKey(id)) funcs.put(id, func(me)); return call(x("fn", p, "id", id), args, p, t); }
      if (!own(owner)) { String f = getter(me); if (f != null) return get(recv, f, p, t); return no(p, t + ": a method of a value record (the subset reads its getters)"); }
      if (sup) { String id = fid(me); if (!funcs.containsKey(id)) funcs.put(id, func(me)); return call(x("fn", p, "id", id), prepend(recv, args), p, t); }
      return call(get(recv, key(me), p, t), args, p, t);
    }
    Low l = lib(new Call(oq, n, recv, recvT == null ? jt(owner.asType()) : recvT, args, argT, out, p, t, stmt, pure && (recv == null || pure(sel))));
    if (l != null) {
      if (l.x() != null && "clock".equals(l.x().get("e"))) rewrites.add(m("span", span(path, mi), "to", "now"));
      return l;
    }
    String callee = sel.toString().replace("this.", "");
    return m("e", "call", "p", p, "text", t, "f", x("ext", p, "q", oq + "." + n, "text", callee, "patch", m("mod", oq, "path", List.of(n))), "args", argsRead(args), "kw", List.of(),
      "jt", String.valueOf(out), "ity", ity(out), "decl", oq, "iface", owner.getKind() == ElementKind.INTERFACE ? true : null, "span", span(path, mi), "tag", tag(path, mi));
  }
  static List<Object> prepend(Object a, List<Map<String, Object>> xs) { List<Object> out = new ArrayList<>(); out.add(a); out.addAll(xs); return out; }
  static List<Map<String, Object>> argsRead(List<Map<String, Object>> args) { return args; }
  boolean pure(Tree t) {
    boolean[] ok = {true};
    new TreeScanner<Void, Void>() {
      @Override public Void visitMethodInvocation(MethodInvocationTree n, Void v) { ok[0] = false; return null; }
      @Override public Void visitNewClass(NewClassTree n, Void v) { ok[0] = false; return null; }
      @Override public Void visitAssignment(AssignmentTree n, Void v) { ok[0] = false; return null; }
      @Override public Void visitUnary(UnaryTree n, Void v) { if (n.getKind().toString().contains("CREMENT")) ok[0] = false; return super.visitUnary(n, v); }
    }.scan(t, null);
    return ok[0];
  }
}
