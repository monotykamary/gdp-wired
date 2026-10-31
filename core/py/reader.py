# The extractor's Python reader (core/extract-py.ts): a module read through Python's own parser (ast) and lowered
# into the shared step IR (core/extract-step.ts's SModule, as JSON on stdout), which one TypeScript executor runs into
# the rule. Nothing here decides what is in the subset beyond the syntax: a construct the IR has no node for becomes
# {"e": "no"} or {"s": "no"} with the reason, refused by the executor only where a step reaches it. The record types
# arguments carry are read from the repository's own modules (their class annotations, never run).
#
#   python3 -I core/py/reader.py '{"root": <repo>, "file": <file>, "names": [<classes or functions>]}'
import ast, json, os, sys

BUILTINS = {'min', 'max', 'abs', 'len', 'int', 'float', 'bool', 'str', 'isinstance', 'round', 'sum', 'any', 'all', 'print', 'repr', 'getattr', 'setattr', 'hasattr', 'type', 'list', 'dict', 'set', 'tuple', 'sorted', 'range', 'zip', 'enumerate'}
# Library functions the executor knows (their meaning, not their code).
KNOWN = {'time.time', 'time.monotonic', 'time.perf_counter', 'math.floor', 'math.ceil', 'math.isfinite', 'math.isnan', 'math.isinf', 'threading.Lock', 'threading.RLock', 'asyncio.Lock'}
TRANSPARENT = {'staticmethod', 'classmethod', 'property', 'dataclass', 'dataclasses.dataclass', 'override', 'typing.override', 'abstractmethod'}

def where(file, n):
  return f"{os.path.basename(file)}:{getattr(n, 'lineno', 0)}:{getattr(n, 'col_offset', 0) + 1}"

def text(n):
  try: s = ast.unparse(n)
  except Exception: s = type(n).__name__
  s = ' '.join(s.split())
  return s if len(s) <= 60 else s[:57] + '...'

def dotted(n):
  if isinstance(n, ast.Name): return n.id
  if isinstance(n, ast.Attribute):
    b = dotted(n.value)
    return f"{b}.{n.attr}" if b else None
  return None

def mentioned(n):
  """The names a node the subset doesn't read mentions (the variables it may read or write)."""
  return sorted({x.id for x in ast.walk(n) if isinstance(x, ast.Name)})

def injected(d):
  """A parameter's default that marks it an injected dependency: FastAPI's Depends(...), dependency-injector's Provide[...]."""
  f = d.func if isinstance(d, ast.Call) else d.value if isinstance(d, ast.Subscript) else None
  return (dotted(f) or '').split('.')[-1] in ('Depends', 'Provide', 'Inject') if f is not None else False

class Repo:
  """The repository's modules, parsed once each, for the classes an annotation names."""
  def __init__(self, root):
    self.root, self.trees = root, {}
  def path_of(self, mod):
    base = os.path.join(self.root, *mod.split('.'))
    for p in (base + '.py', os.path.join(base, '__init__.py')):
      if os.path.isfile(p): return p
    return None
  def tree(self, path):
    if path not in self.trees:
      try:
        with open(path, encoding='utf-8') as f: self.trees[path] = ast.parse(f.read(), path)
      except Exception: self.trees[path] = None
    return self.trees[path]
  def module_name(self, path):
    rel = os.path.relpath(path, self.root)[:-3].replace(os.sep, '.')
    return rel[:-9] if rel.endswith('.__init__') else rel

def resolve_from(mod_name, is_pkg, node):
  """The absolute module an `from X import ...` names, relative ones too."""
  if not node.level: return node.module
  parts = mod_name.split('.')
  base = parts if is_pkg else parts[:-1]
  base = base[: len(base) - (node.level - 1)] if node.level > 1 else base
  return '.'.join(base + ([node.module] if node.module else []))

class Module:
  """One module's names: its imports, classes, functions and constants."""
  def __init__(self, repo, path):
    self.repo, self.path, self.tree = repo, path, repo.tree(path)
    self.name = repo.module_name(path)
    self.is_pkg = path.endswith('__init__.py')
    self.imports, self.classes, self.funcs, self.consts = {}, {}, {}, {}
    for n in (self.tree.body if self.tree else []):
      self.scan(n)
  def scan(self, n):
    if isinstance(n, ast.Import):
      for a in n.names: self.imports[(a.asname or a.name).split('.')[0]] = ('module', a.name if a.asname else a.name.split('.')[0])
    elif isinstance(n, ast.ImportFrom):
      m = resolve_from(self.name, self.is_pkg, n)
      for a in n.names: self.imports[a.asname or a.name] = ('name', m, a.name)
    elif isinstance(n, ast.ClassDef): self.classes[n.name] = n
    elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)): self.funcs[n.name] = n
    elif isinstance(n, (ast.Assign, ast.AnnAssign)):
      targets = n.targets if isinstance(n, ast.Assign) else [n.target]
      for t in targets:
        if isinstance(t, ast.Name) and n.value is not None: self.consts[t.id] = n.value
    elif isinstance(n, ast.If):
      # `if TYPE_CHECKING:` imports and aliases: what the names are for the types (its else, `X = Any`, yields to it).
      for m in n.orelse + n.body: self.scan(m)

class Reader:
  def __init__(self, root, file):
    self.repo = Repo(root)
    self.mod = Module(self.repo, os.path.abspath(file))
    self.file = os.path.abspath(file)
    self.recs, self.funcs = {}, {}
    self.local_stack = []

  # --- types -------------------------------------------------------------------------------------------------------
  def find_class(self, mod, name, depth=0):
    """A class a module names, through its imports (re-exports too): (module, ClassDef) or None."""
    if depth > 6 or mod is None: return None
    if name in mod.classes: return (mod, mod.classes[name])
    imp = mod.imports.get(name)
    if imp and imp[0] == 'name':
      p = self.repo.path_of(imp[1])
      if p:
        sub = Module(self.repo, p) if p != mod.path else mod
        return self.find_class(sub, imp[2], depth + 1)
    if name in mod.consts and isinstance(mod.consts[name], ast.Name):  # an alias: X = Y
      return self.find_class(mod, mod.consts[name].id, depth + 1)
    return None
  def ret_of(self, modname, name, depth=0):
    """The declared result type of a function a module of the repository defines (through its re-exports), or None."""
    p = self.repo.path_of(modname) if modname else None
    if depth > 6 or not p: return None
    m = Module(self.repo, p) if p != self.mod.path else self.mod
    f = m.funcs.get(name)
    if f is not None: return self.ty(f.returns, m) if f.returns is not None else None
    imp = m.imports.get(name)
    if imp and imp[0] == 'name': return self.ret_of(imp[1], imp[2], depth + 1)
    return None
  def rec_of(self, mod, cdef):
    """A class as a record type: its fields (annotations, its bases' first), its methods (to resolve calls)."""
    q = f"{mod.name}.{cdef.name}"
    if q in self.recs: return q
    self.recs[q] = None  # (being read)
    fields, methods, bases, kinds, rets = [], {}, [], set(), {}
    for b in cdef.bases:
      bn = dotted(b.value if isinstance(b, ast.Subscript) else b)
      if bn in ('TypedDict', 'typing.TypedDict', 'typing_extensions.TypedDict'): kinds.add('typeddict'); continue
      if bn in ('BaseModel', 'pydantic.BaseModel'): kinds.add('pydantic'); continue
      if bn in ('Protocol', 'typing.Protocol', 'ABC', 'abc.ABC'): kinds.add('protocol'); continue
      if bn in ('Generic', 'object', 'Exception'): continue
      hit = self.find_class(mod, bn.split('.')[-1]) if bn else None
      if hit:
        bq = self.rec_of(*hit)
        if bq and self.recs.get(bq):
          br = self.recs[bq]
          bases.append(bq)
          kinds |= set(br.get('kinds', []))
          for f in br['fields']:
            if not any(g['name'] == f['name'] for g in fields): fields.append(f)
          for m, fid in br['methods'].items(): methods[m] = fid
          rets.update(br.get('rets', {}))
      elif bn: kinds.add('outside-base:' + bn)
    dataclass = any((dotted(d.func if isinstance(d, ast.Call) else d) or '').split('.')[-1] == 'dataclass' for d in cdef.decorator_list)
    frozen = any(isinstance(d, ast.Call) and any(k.arg == 'frozen' and isinstance(k.value, ast.Constant) and k.value.value for k in d.keywords) for d in cdef.decorator_list)
    total = not any(k.arg == 'total' and isinstance(k.value, ast.Constant) and k.value.value is False for k in cdef.keywords)
    # The fields its __init__ sets: annotated there, or set from an annotated argument (a class of another module whose
    # fields aren't declared on the class).
    init = next((n for n in cdef.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name == '__init__'), None)
    if init is not None:
      anns = {x.arg: x.annotation for x in init.args.args + init.args.kwonlyargs if x.annotation is not None}
      for n in ast.walk(init):
        t = None
        if isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Attribute) and isinstance(n.target.value, ast.Name) and n.target.value.id == 'self':
          name, t = n.target.attr, self.ty(n.annotation, mod)
        elif isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Attribute) and isinstance(n.targets[0].value, ast.Name) and n.targets[0].value.id == 'self':
          v = n.value
          if isinstance(v, ast.Name) and v.id in anns: name, t = n.targets[0].attr, self.ty(anns[v.id], mod)
          elif isinstance(v, ast.BoolOp) and isinstance(v.op, ast.Or) and isinstance(v.values[0], ast.Name) and v.values[0].id in anns and not (isinstance(v.values[-1], ast.Constant) and v.values[-1].value is None):
            # `x or DEFAULT`: the argument's type, never None
            name, t = n.targets[0].attr, self.ty(anns[v.values[0].id], mod)
            if t['k'] == 'opt': t = t['of']
        if t is not None and not any(g['name'] == name for g in fields): fields.append({'name': name, 't': t, 'init': True})
    for n in cdef.body:
      if isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name):
        ann = n.annotation
        if dotted(ann.value if isinstance(ann, ast.Subscript) else ann) in ('ClassVar', 'typing.ClassVar'): continue
        f = {'name': n.target.id, 't': self.ty(ann, mod)}
        if n.value is not None: f['dflt'] = self.expr(n.value, mod)
        fields = [g for g in fields if g['name'] != f['name']] + [f]
      elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
        if n.returns is not None: rets[n.name] = self.ty(n.returns, mod)
        else: rets.pop(n.name, None)
        if mod.path == self.file:
          fid = f"{cdef.name}.{n.name}"
          self.funcs[fid] = self.func(n, mod, cdef.name, fid)
          methods[n.name] = fid
        else: methods[n.name] = None  # another module's method: not read
    r = {'name': q, 'short': cdef.name, 'fields': fields, 'methods': methods, 'bases': bases, 'p': where(mod.path, cdef),
         'kinds': sorted(kinds | ({'dataclass'} if dataclass else set()) | ({'frozen'} if frozen else set()) | (set() if total else {'partial'})),
         'own': mod.path == self.file, 'module': mod.name, **({'rets': rets} if rets else {})}
    self.recs[q] = r
    return q
  def ty(self, a, mod):
    if a is None: return {'k': 'any'}
    if isinstance(a, ast.Constant):
      if a.value is None: return {'k': 'none'}
      if isinstance(a.value, str):
        try: return self.ty(ast.parse(a.value, mode='eval').body, mod)
        except SyntaxError: return {'k': 'opaque', 'why': a.value}
    if isinstance(a, ast.BinOp) and isinstance(a.op, ast.BitOr):
      return self.union([self.ty(a.left, mod), self.ty(a.right, mod)], a)
    if isinstance(a, ast.Subscript):
      head = (dotted(a.value) or '').split('.')[-1]
      args = a.slice.elts if isinstance(a.slice, ast.Tuple) else [a.slice]
      if head in ('Optional',): return self.union([self.ty(args[0], mod), {'k': 'none'}], a)
      if head == 'Union': return self.union([self.ty(x, mod) for x in args], a)
      if head in ('Final', 'Annotated', 'ReadOnly', 'Required', 'NotRequired'): return self.ty(args[0], mod)
      if head == 'Literal':
        if all(isinstance(x, ast.Constant) and isinstance(x.value, str) for x in args): return {'k': 'choice', 'values': [x.value for x in args]}
        return {'k': 'opaque', 'why': f"{text(a)}: a Literal of other than strings"}
      if head in ('dict', 'Dict', 'Mapping', 'MutableMapping', 'defaultdict', 'OrderedDict') and len(args) == 2:
        return {'k': 'map', 'key': self.ty(args[0], mod), 'val': self.ty(args[1], mod), 'py': head}
      if head in ('list', 'List', 'Sequence'): return {'k': 'list', 'of': self.ty(args[0], mod)}
      return {'k': 'opaque', 'why': f"{text(a)}"}
    n = dotted(a)
    if n in ('int',): return {'k': 'int'}
    if n in ('float',): return {'k': 'float'}
    if n in ('bool',): return {'k': 'bool'}
    if n in ('str',): return {'k': 'str'}
    if n in ('None',): return {'k': 'none'}
    if n in ('Final', 'Any', 'typing.Any', 'object'): return {'k': 'any'}
    if n in ('dict', 'Dict'): return {'k': 'opaque', 'why': f"{n} with no key and value types"}
    if n in ('threading.Lock', 'asyncio.Lock', 'Lock'): return {'k': 'lock'}
    if n:
      hit = self.find_class(mod, n.split('.')[-1]) if '.' not in n or n.split('.')[0] in mod.imports else None
      if hit:
        q = self.rec_of(*hit)
        if q: return {'k': 'rec', 'name': q}
      return {'k': 'opaque', 'why': f"{n}, a type outside the files read"}
    return {'k': 'opaque', 'why': text(a)}
  def union(self, ts, a):
    none = any(t['k'] == 'none' for t in ts)
    rest = [t for t in ts if t['k'] != 'none']
    flat = []
    for t in rest:
      if t['k'] == 'opt': none = True; t = t['of']
      if t not in flat: flat.append(t)
    if len(flat) == 2 and {t['k'] for t in flat} == {'int', 'float'}: flat = [{'k': 'float'}]
    if len(flat) != 1: return {'k': 'opaque', 'why': f"{text(a)}: a union of several types"}
    return {'k': 'opt', 'of': flat[0]} if none else flat[0]

  # --- functions ---------------------------------------------------------------------------------------------------
  def func(self, n, mod, cls, fid):
    self.local_stack.append(set(self.locals_of(n)))
    try:
      a = n.args
      params = []
      pos = a.posonlyargs + a.args
      dflts = [None] * (len(pos) - len(a.defaults)) + list(a.defaults)
      for i, (x, d) in enumerate(zip(pos, dflts)):
        params.append({'name': x.arg, 't': self.ty(x.annotation, mod), **({'dflt': self.expr(d, mod)} if d is not None else {}), **({'inject': True} if injected(d) else {})})
      for x, d in zip(a.kwonlyargs, a.kw_defaults):
        params.append({'name': x.arg, 't': self.ty(x.annotation, mod), 'kw': True, **({'dflt': self.expr(d, mod)} if d is not None else {}), **({'inject': True} if injected(d) else {})})
      decs = [self.decorator(d) for d in n.decorator_list]
      static = any(d['name'] in ('staticmethod',) for d in decs)
      if cls and not static and params: params[0]['self'] = True
      if a.vararg: params.append({'name': a.vararg.arg, 't': {'k': 'opaque', 'why': '*args'}, 'star': 1})
      if a.kwarg: params.append({'name': a.kwarg.arg, 't': {'k': 'opaque', 'why': '**kwargs'}, 'star': 2})
      body = self.block(n.body, mod)
      return {'id': fid, 'name': n.name, **({'cls': cls} if cls else {}), 'p': where(self.file, n), 'span': [os.path.basename(self.file), n.lineno, n.end_lineno],
              'params': params, 'ret': self.ty(n.returns, mod), 'body': body, 'async': isinstance(n, ast.AsyncFunctionDef), 'decorators': decs, 'static': static}
    finally:
      self.local_stack.pop()
  def decorator(self, d):
    f = d.func if isinstance(d, ast.Call) else d
    return {'name': dotted(f) or text(f), 'text': text(d), 'p': where(self.file, d)}
  def locals_of(self, fn):
    out = {x.arg for x in fn.args.posonlyargs + fn.args.args + fn.args.kwonlyargs}
    if fn.args.vararg: out.add(fn.args.vararg.arg)
    if fn.args.kwarg: out.add(fn.args.kwarg.arg)
    for n in ast.walk(fn):
      if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store): out.add(n.id)
      if isinstance(n, (ast.Import, ast.ImportFrom)):
        for a in n.names: out.add((a.asname or a.name).split('.')[0])
    return out
  # --- statements --------------------------------------------------------------------------------------------------
  def block(self, ss, mod):
    out = []
    for s in ss:
      for r in self.stmt(s, mod):
        if r.get('s') == 'no' and 'names' not in r: r['names'] = mentioned(s)
        out.append(r)
    return out
  def stmt(self, s, mod):
    p = where(self.file, s)
    E = lambda x: self.expr(x, mod)
    if isinstance(s, ast.Expr):
      if isinstance(s.value, ast.Constant) and isinstance(s.value.value, str): return []  # a docstring
      return [{'s': 'expr', 'p': p, 'x': E(s.value)}]
    if isinstance(s, ast.Pass): return []
    if isinstance(s, (ast.Assign, ast.AnnAssign)):
      if s.value is None: return []  # a declaration: `x: int`
      targets = s.targets if isinstance(s, ast.Assign) else [s.target]
      x = E(s.value)
      ann = self.ty(s.annotation, mod) if isinstance(s, ast.AnnAssign) else None
      out = []
      for t in targets: out.append({'s': 'set', 'p': p, 'to': self.target(t, mod), 'x': x, **({'t': ann} if ann and ann['k'] != 'any' else {})})
      return out
    if isinstance(s, ast.AugAssign):
      op = self.binop(s.op)
      t = self.target(s.target, mod)
      return [{'s': 'set', 'p': p, 'to': t, 'x': {'e': 'bin', 'op': op, 'x': self.expr(s.target, mod), 'y': E(s.value), 'p': p, 'text': text(s)} if op else {'e': 'no', 'why': f"{text(s)}: {type(s.op).__name__} (outside the subset)", 'p': p}}]
    if isinstance(s, ast.If):
      return [{'s': 'if', 'p': p, 'c': E(s.test), 'then': self.block(s.body, mod), 'else': self.block(s.orelse, mod)}]
    if isinstance(s, ast.Return): return [{'s': 'ret', 'p': p, **({'x': E(s.value)} if s.value is not None else {})}]
    if isinstance(s, ast.Raise):
      return [{'s': 'fail', 'p': p, 'why': f"raise {text(s.exc) if s.exc else ''}".strip(), **({'x': E(s.exc)} if s.exc else {})}]
    if isinstance(s, ast.Assert):
      return [{'s': 'if', 'p': p, 'c': E(s.test), 'then': [], 'else': [{'s': 'fail', 'p': p, 'why': f"assert {text(s.test)}"}]}]
    if isinstance(s, (ast.With, ast.AsyncWith)):
      items = [{'x': E(i.context_expr), **({'as': self.target(i.optional_vars, mod)} if i.optional_vars is not None else {})} for i in s.items]
      return [{'s': 'with', 'p': p, 'items': items, 'body': self.block(s.body, mod), 'async': isinstance(s, ast.AsyncWith)}]
    if isinstance(s, ast.Delete):
      return [{'s': 'del', 'p': p, 'x': self.target(t, mod)} for t in s.targets]
    if isinstance(s, (ast.Import, ast.ImportFrom)):
      names = {}
      for a in s.names:
        if isinstance(s, ast.Import): names[(a.asname or a.name).split('.')[0]] = {'mod': a.name if a.asname else a.name.split('.')[0]}
        else:
          m = resolve_from(self.mod.name, self.mod.is_pkg, s)
          ret = self.ret_of(m, a.name)
          names[a.asname or a.name] = {'mod': m, 'name': a.name, **({'ret': ret} if ret else {})}
      return [{'s': 'import', 'p': p, 'names': names}]
    if isinstance(s, (ast.For, ast.AsyncFor, ast.While)): return [{'s': 'no', 'p': p, 'why': f"a loop ({type(s).__name__.lower().replace('async', 'async ')})"}]
    if isinstance(s, ast.Try) or type(s).__name__ == 'TryStar': return [{'s': 'no', 'p': p, 'why': 'try/except (an exception caught: the subset reads one only as the step\'s failure)'}]
    if isinstance(s, (ast.Global, ast.Nonlocal)): return [{'s': 'no', 'p': p, 'why': f"{type(s).__name__.lower()} (a variable every call shares)"}]
    if isinstance(s, ast.Match): return [{'s': 'no', 'p': p, 'why': 'match'}]
    if isinstance(s, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)): return [{'s': 'no', 'p': p, 'why': f"a {'class' if isinstance(s, ast.ClassDef) else 'function'} defined in a function (a closure)"}]
    return [{'s': 'no', 'p': p, 'why': f"{type(s).__name__} (a statement outside the subset)"}]
  def target(self, t, mod):
    p = where(self.file, t)
    if isinstance(t, ast.Name): return {'e': 'var', 'n': t.id, 'p': p}
    if isinstance(t, ast.Attribute): return {'e': 'get', 'x': self.expr(t.value, mod), 'f': t.attr, 'p': p, 'text': text(t)}
    if isinstance(t, ast.Subscript): return {'e': 'idx', 'x': self.expr(t.value, mod), 'i': self.expr(t.slice, mod), 'p': p, 'text': text(t)}
    if isinstance(t, (ast.Tuple, ast.List)): return {'e': 'tuple', 'xs': [self.target(x, mod) for x in t.elts], 'p': p}
    return {'e': 'no', 'why': f"{text(t)}: an assignment to other than a name, a field or an item", 'p': p}

  # --- expressions -------------------------------------------------------------------------------------------------
  def binop(self, op):
    return {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.FloorDiv: '//', ast.Mod: '%', ast.Div: '/'}.get(type(op))
  def name(self, n, mod, p):
    """What a name is where it is read: a local, a constant, a function or class of the module, an import, a builtin."""
    if self.local_stack and n in self.local_stack[-1]: return {'e': 'var', 'n': n, 'p': p}
    if n in mod.funcs: return {'e': 'fn', 'id': n, 'p': p}
    if n in mod.classes:
      q = self.rec_of(mod, mod.classes[n])
      return {'e': 'cls', 'rec': q, 'p': p}
    if n in mod.imports:
      imp = mod.imports[n]
      if imp[0] == 'module': return {'e': 'ext', 'q': imp[1], 'text': n, 'patch': {'mod': mod.name, 'path': [n]}, 'p': p}
      hit = self.find_class(mod, n)
      if hit: return {'e': 'cls', 'rec': self.rec_of(*hit), 'q': f"{imp[1]}.{imp[2]}", 'patch': {'mod': mod.name, 'path': [n]}, 'p': p}
      ret = self.ret_of(imp[1], imp[2])
      return {'e': 'ext', 'q': f"{imp[1]}.{imp[2]}", 'text': n, 'patch': {'mod': mod.name, 'path': [n]}, 'p': p, **({'ret': ret} if ret else {})}
    if n in mod.consts:
      v = mod.consts[n]
      if isinstance(v, ast.Constant) or (isinstance(v, ast.UnaryOp) and isinstance(v.operand, ast.Constant)): return self.expr(v, mod)
      return {'e': 'ext', 'q': f"{mod.name}.{n}", 'text': n, 'patch': {'mod': mod.name, 'path': [n]}, 'global': True, 'p': p}
    if n in ('True', 'False', 'None'): return self.expr(ast.Constant({'True': True, 'False': False, 'None': None}[n]), mod)
    if n in BUILTINS: return {'e': 'builtin', 'n': n, 'p': p}
    return {'e': 'ext', 'q': n, 'text': n, 'p': p, 'unbound': True}
  def expr(self, x, mod):
    r = self.expr1(x, mod)
    if r.get('e') == 'no' and 'names' not in r: r['names'] = mentioned(x)
    return r
  def expr1(self, x, mod):
    p = where(self.file, x)
    E = lambda y: self.expr(y, mod)
    if isinstance(x, ast.Constant):
      v = x.value
      if isinstance(v, bool): return {'e': 'bool', 'v': v, 'p': p}
      if isinstance(v, int): return {'e': 'int', 'v': str(v), 'p': p}
      if isinstance(v, float):
        if v.is_integer() and abs(v) < 2 ** 53: return {'e': 'int', 'v': str(int(v)), 'float': True, 'p': p}
        return {'e': 'no', 'why': f"{text(x)}: a float that isn't whole (a binary fraction)", 'p': p}
      if isinstance(v, str): return {'e': 'str', 'v': v, 'p': p}
      if v is None: return {'e': 'none', 'p': p}
      return {'e': 'no', 'why': f"{text(x)}: a constant outside the subset", 'p': p}
    if isinstance(x, ast.Name): return self.name(x.id, mod, p)
    if isinstance(x, ast.Attribute):
      d = dotted(x)
      base = d.split('.')[0] if d else None
      if d and base in mod.imports and mod.imports[base][0] == 'module' and not (self.local_stack and base in self.local_stack[-1]):
        q = mod.imports[base][1] + d[len(base):]
        if q in KNOWN: return {'e': 'lib', 'q': q, 'p': p}
        ret = self.ret_of(q.rpartition('.')[0], q.rpartition('.')[2])
        return {'e': 'ext', 'q': q, 'text': d, 'patch': {'mod': mod.name, 'path': d.split('.')}, 'p': p, **({'ret': ret} if ret else {})}
      return {'e': 'get', 'x': E(x.value), 'f': x.attr, 'p': p, 'text': text(x)}
    if isinstance(x, ast.BinOp):
      op = self.binop(x.op)
      if not op: return {'e': 'no', 'why': f"{text(x)}: {type(x.op).__name__} (outside the subset)", 'p': p}
      return {'e': 'bin', 'op': op, 'x': E(x.left), 'y': E(x.right), 'p': p, 'text': text(x)}
    if isinstance(x, ast.UnaryOp):
      if isinstance(x.op, ast.USub): return {'e': 'neg', 'x': E(x.operand), 'p': p}
      if isinstance(x.op, ast.UAdd): return E(x.operand)
      if isinstance(x.op, ast.Not): return {'e': 'not', 'x': E(x.operand), 'p': p}
      return {'e': 'no', 'why': f"{text(x)}: a bit operation", 'p': p}
    if isinstance(x, ast.BoolOp): return {'e': 'and' if isinstance(x.op, ast.And) else 'or', 'xs': [E(v) for v in x.values], 'p': p}
    if isinstance(x, ast.Compare):
      ops = {ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=', ast.Eq: '==', ast.NotEq: '!=', ast.Is: 'is', ast.IsNot: 'is not', ast.In: 'in', ast.NotIn: 'not in'}
      parts, left = [], x.left
      for op, right in zip(x.ops, x.comparators):
        parts.append({'e': 'cmp', 'op': ops[type(op)], 'x': E(left), 'y': E(right), 'p': p, 'text': text(x)})
        left = right
      return parts[0] if len(parts) == 1 else {'e': 'and', 'xs': parts, 'p': p}
    if isinstance(x, ast.IfExp): return {'e': 'ite', 'c': E(x.test), 'a': E(x.body), 'b': E(x.orelse), 'p': p}
    if isinstance(x, ast.Await): return {'e': 'await', 'x': E(x.value), 'p': p}
    if isinstance(x, ast.Call):
      f = E(x.func)
      if f.get('e') == 'ext' and f.get('q') in KNOWN: f = {'e': 'lib', 'q': f['q'], 'p': f['p']}
      args = [E(a) if not isinstance(a, ast.Starred) else {'e': 'no', 'why': f"{text(a)}: *args", 'p': p} for a in x.args]
      kw = [[k.arg, E(k.value)] if k.arg else ['**', {'e': 'no', 'why': f"**{text(k.value)}", 'p': p}] for k in x.keywords]
      return {'e': 'call', 'f': f, 'args': args, 'kw': kw, 'p': p, 'text': text(x)}
    if isinstance(x, ast.Subscript): return {'e': 'idx', 'x': E(x.value), 'i': E(x.slice), 'p': p, 'text': text(x)}
    if isinstance(x, ast.Dict):
      if any(k is None for k in x.keys): return {'e': 'no', 'why': f"{text(x)}: a dict spread", 'p': p}
      return {'e': 'dict', 'keys': [E(k) for k in x.keys], 'vals': [E(v) for v in x.values], 'p': p}
    if isinstance(x, ast.Tuple): return {'e': 'tuple', 'xs': [E(v) for v in x.elts], 'p': p}
    if isinstance(x, ast.JoinedStr):
      parts = []
      for v in x.values:
        if isinstance(v, ast.Constant): parts.append(v.value)
        elif isinstance(v, ast.FormattedValue): parts.append({'x': E(v.value), 'plain': v.conversion == -1 and v.format_spec is None})
      return {'e': 'fstr', 'parts': parts, 'p': p, 'text': text(x)}
    if isinstance(x, ast.List): return {'e': 'list', 'xs': [E(v) for v in x.elts], 'p': p}
    if isinstance(x, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)): return {'e': 'no', 'why': f"{text(x)}: a comprehension (a loop)", 'p': p}
    if isinstance(x, ast.Lambda):
      # (read as a key function where one is taken, min/max(xs, key=lambda o: ...); anywhere else refused, a closure)
      a = x.args
      if a.vararg or a.kwarg or a.kwonlyargs or a.defaults or a.posonlyargs or len(a.args) != 1: return {'e': 'no', 'why': f"{text(x)}: a lambda (a closure)", 'p': p}
      ps = [y.arg for y in a.args]
      self.local_stack.append((self.local_stack[-1] if self.local_stack else set()) | set(ps))
      try: body = E(x.body)
      finally: self.local_stack.pop()
      return {'e': 'lambda', 'params': ps, 'x': body, 'p': p, 'text': text(x)}
    return {'e': 'no', 'why': f"{text(x)}: {type(x).__name__} (outside the subset)", 'p': p}

def main():
  req = json.loads(sys.argv[1])
  r = Reader(req['root'], req['file'])
  mod = r.mod
  if mod.tree is None:
    print(json.dumps({'error': f"{req['file']} doesn't parse"})); return
  out = {'lang': 'python', 'file': os.path.basename(r.file), 'path': r.file, 'module': mod.name, 'root': os.path.abspath(req['root']), 'entries': []}
  for n in req['names'] or list(mod.classes):
    if n in mod.classes: out['entries'].append({'k': 'class', 'rec': r.rec_of(mod, mod.classes[n])})
    elif n in mod.funcs:
      r.local_stack = []
      r.funcs[n] = r.func(mod.funcs[n], mod, None, n)
      out['entries'].append({'k': 'func', 'id': n})
    else: out['entries'].append({'k': 'missing', 'name': n})
  # The module's other functions, for the calls the entries make (each read once).
  for n, f in mod.funcs.items():
    if n not in r.funcs: r.funcs[n] = r.func(f, mod, None, n)
  out['recs'] = {k: v for k, v in r.recs.items() if v}
  out['funcs'] = r.funcs
  print(json.dumps(out))

if __name__ == '__main__':
  main()
