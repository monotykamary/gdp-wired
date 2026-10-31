# The Python side of the extractor's check (core/extract-step.ts's checkStep): the module imported as it ships, its
# object made, set to a state, called with the rule's requests and read back, one JSON line a request over two named
# pipes. What the caller stated is enforced here: an answered call stubbed with the request's input, a store given as
# one that keeps what is set, the clock read as the request's time. Line events count the branch arms reached.
#
#   python3 core/py/harness.py <in-fifo> <out-fifo>
import asyncio, dataclasses, datetime, importlib, inspect, json, os, sys, types
import time as time_module

NOW = [0]
CUR = {}
HIT = set()
S = {}

def enc_num(v):
  if isinstance(v, bool): return v
  if isinstance(v, int): return str(v)
  if isinstance(v, float):
    return str(int(v)) if v.is_integer() and abs(v) < 2 ** 63 else f"f:{v!r}"
  return f"?:{type(v).__name__}"

def tag(v):
  if v is None or isinstance(v, bool): return v
  if isinstance(v, (int, float)): return {'n': enc_num(v)}
  if isinstance(v, str): return {'s': v}
  return {'o': type(v).__name__}

class Inert:
  """A value of a type outside the subset the rule never reads: any attribute an inert value, a call a no-op."""
  def __getattr__(self, n):
    if n.startswith('__'): raise AttributeError(n)
    return Inert()
  def __call__(self, *a, **k):
    async def noop(): return None
    return noop()

def resolve(q):
  mod, _, name = q.rpartition('.')
  return getattr(importlib.import_module(mod), name)

class FakeStore:
  """A store as the caller stated it: get, set and delete over a dict that keeps what is set (no expiry)."""
  def __init__(self, decl, name=None):
    self.data, self.name = {}, name
    for path, v in (decl.get('attrs') or {}).items():
      o, parts = self, path.split('.')
      for p in parts[:-1]:
        if not hasattr(o, p): setattr(o, p, types.SimpleNamespace())
        o = getattr(o, p)
      setattr(o, parts[-1], v)
    asyncs = decl.get('async') or {}
    def mk(kind, name):
      # (the key by position, or as key= or name=, redis-py's; nx and xx as redis-py's: True where it set, else None)
      kk = lambda a, k: k.get('key', k.get('name', a[0] if a else None))
      def get(*a, **k): return self.data.get(kk(a, k))
      def set_(*a, **k):
        key = kk(a, k); val = k.get('value', a[1] if len(a) > 1 else None)
        if (k.get('nx') and key in self.data) or (k.get('xx') and key not in self.data): return None
        self.data[key] = val
        if k.get('nx') or k.get('xx'): return True
      def delete(*a, **k): self.data.pop(kk(a, k), None)
      f0, key = {'get': get, 'set': set_, 'delete': delete}[kind], f"{self.name}.{name}"
      # (where the request says the operation raises, inside a try that catches it)
      def f(*a, **k):
        r = (CUR.get(key) or {}).get('raise')
        if r is not None and raises_here(key): raise raised(r)
        return f0(*a, **k)
      if asyncs.get(name):
        async def af(*a, **k): return f(*a, **k)
        return af
      return f
    for kind, dflt in (('get', ['get', 'async_get_cache', 'get_cache']), ('set', ['set', 'async_set_cache', 'set_cache']), ('delete', ['delete', 'delete_cache', 'async_delete_cache'])):
      for m in decl.get(kind) or dflt: setattr(self, m, mk(kind, m))
    # (a method left out: nothing, as the rule takes it; any other is no method of this store, and fails)
    for m in decl.get('skip') or []:
      async def anop(*a, **k): return None
      setattr(self, m, (lambda *a, **k: anop()) if asyncs.get(m) else (lambda *a, **k: None))
    # (an injected dependency's other methods: each answered by the request's input)
    for a in S.get('answers') or []:
      if a['patch'].get('store') == name and not a.get('pass'): setattr(self, a['patch']['path'][-1], stub(a['key'], a['async']))

def build(spec, stores):
  if 'in' in spec:
    v = spec['in']
    return float(v) if spec.get('float') and isinstance(v, int) and not isinstance(v, bool) else v
  if spec.get('none'): return None
  if spec.get('inert'): return {} if spec.get('dict') else Inert()
  if 'store' in spec: return stores.setdefault(spec['store'], FakeStore(S['stores'].get(spec['store'], {}), spec['store']))
  if 'list' in spec: return [build(x, stores) for x in spec['list']]
  if 'rec' in spec:
    cls = resolve(spec['rec'])
    f = {k: build(v, stores) for k, v in spec['f'].items()}
    return make_rec(cls, f)
  raise ValueError(f"an argument spec {spec}")

SUBS = {}
def make_rec(cls, f):
  # A record of the inputs the rule reads: every other field inert (the code may read it, the rule claims nothing of it).
  if hasattr(cls, 'model_construct'):
    fields = getattr(cls, 'model_fields', {}) or {}
    rest = {n: Inert() for n, fi in fields.items() if n not in f and getattr(fi, 'is_required', lambda: False)()}
    return cls.model_construct(**rest, **f)
  if getattr(cls, '__annotations__', None) is not None and isinstance(cls, type) and issubclass(cls, dict): return dict(f)
  if dataclasses.is_dataclass(cls):
    o = object.__new__(cls)
    for k, v in f.items(): object.__setattr__(o, k, v)
    return o
  sub = SUBS.get(cls)
  if sub is None:
    try: sub = SUBS[cls] = type(cls.__name__, (cls,), {'__getattr__': lambda self, n: Inert() if not n.startswith('__') else object.__getattribute__(self, n), '__module__': cls.__module__})
    except TypeError: sub = SUBS[cls] = cls
  o = object.__new__(sub)
  for k, v in f.items(): setattr(o, k, v)
  return o

def fixed_args(spec_list, inputs):
  """Arguments from their specs, the string inputs kept strings where the leaf is a string."""
  out = {}
  for name, spec in spec_list:
    if spec.get('dflt'): continue
    out[name] = build(spec, OBJ_STORES)
  return out

OBJS = {}
OBJ_STORES = {}

def walk(o, path):
  for p in path: o = o[p] if isinstance(o, dict) else getattr(o, p)
  return o

def put(o, path, v):
  parent = walk(o, path[:-1])
  if isinstance(parent, dict): parent[path[-1]] = v
  elif dataclasses.is_dataclass(parent) and getattr(type(parent), '__dataclass_params__', None) and type(parent).__dataclass_params__.frozen: object.__setattr__(parent, path[-1], v)
  else: setattr(parent, path[-1], v)

def tpl_match(tpl, key):
  pre, _, post = tpl.partition('{}')
  if not isinstance(key, str) or not key.startswith(pre) or not key.endswith(post) or len(key) < len(pre) + len(post): return None
  return key[len(pre): len(key) - len(post)] if '{}' in tpl else ('' if key == tpl else None)

def owns(l, key):
  """The part of a store's key a leaf's template takes, where no more specific template of the store takes it (the
  templates name distinct keys: "{}:lock" keys aren't "{}" ones)."""
  h = tpl_match(l['tpl'], key)
  if h is None: return None
  for m in S['leaves']:
    if m.get('store') == l['store'] and m is not l and len(m['tpl']) > len(l['tpl']) and tpl_match(m['tpl'], key) is not None: return None
  return h

def state_of(obj, stores):
  s = {}
  for l in S['leaves']:
    k = l['kind']
    if k == 'frame': continue
    if l.get('store'):
      st = stores.get(l['store'])
      cells = {}
      for key, v in (st.data.items() if st else []):
        h = owns(l, key)
        if h is None: continue
        if l.get('json'):
          # (a JSON record: its fields kept, an optional one beside whether the key holds a value; strings left out)
          d, c = json.loads(v), {}
          for f in l['json']:
            if f.get('out'): continue
            x = d.get(f['name']) if f.get('opt') else d[f['name']]
            if f.get('opt'): c[f['name'] + '_has'] = x is not None
            c[f['name']] = (x if x is not None else (f['vals'][0] if f.get('choice') else 0)) if f.get('choice') else enc_num(0 if x is None else x)
          cells[h] = c
        else: cells[h] = {'value': v if l.get('choice') else enc_num(v)}
      s[l['name']] = cells
      continue
    v = walk(obj, l['path'])
    if k == 'none': s[l['name']] = v is None
    elif k == 'num': s[l['name']] = '0' if v is None else enc_num(v)
    elif k in ('str', 'choice'): s[l['name']] = '' if v is None else v
    elif k == 'bool': s[l['name']] = False if v is None else v
    elif k == 'map':
      cells = {}
      # (a list: its items by their places, 0 first)
      for key, x in (enumerate(v or []) if l.get('ordered') else (v or {}).items()):
        if l.get('fields'): cells[str(key)] = {f['name']: (lambda y: y if f.get('choice') else enc_num(y))(x[f['name']] if isinstance(x, dict) else getattr(x, f['name'])) for f in l['fields']}
        else: cells[str(key)] = {'value': enc_num(x)}
      s[l['name']] = cells
  # A store's key no template names: the code keeps state the rule has no place for.
  for name, st in stores.items():
    tpls = [l['tpl'] for l in S['leaves'] if l.get('store') == name]
    for key in st.data:
      if not any(tpl_match(t, key) is not None for t in tpls): raise ValueError(f"the store {name} holds {key!r}, a key no template of the rule names")
  return s

def num_in(x, flt):
  return float(int(x)) if flt else int(x)

def set_state(obj, stores, state):
  for l in S['leaves']:
    k = l['kind']
    if k in ('frame', 'none'): continue
    v = state.get(l['name'])
    if l.get('store'):
      st = stores[l['store']]
      pre, _, post = l['tpl'].partition('{}')
      for key in [kk for kk in st.data if owns(l, kk) is not None]: del st.data[key]
      for h, c in (v or {}).items():
        at = pre + h + post if '{}' in l['tpl'] else l['tpl']
        if l.get('json'): st.data[at] = json.dumps({f['name']: (c[f['name']] if f.get('choice') else num_in(c[f['name']], False)) for f in l['json'] if not f.get('out') and (not f.get('opt') or c.get(f['name'] + '_has'))})
        else: st.data[at] = c['value'] if l.get('choice') else num_in(c['value'], l.get('float'))
      continue
    if k == 'num': put(obj, l['path'], num_in(v, l.get('float')))
    elif k in ('str', 'choice', 'bool'): put(obj, l['path'], v)
    elif k == 'map':
      d = {}
      for key, c in (v or {}).items():
        kk = int(key) if l.get('key') == 'num' else key
        if l.get('fields'):
          d[kk] = make_rec(resolve(l['cls']), {f['name']: (num_in(c[f['name']], f.get('float')) if isinstance(c[f['name']], str) and not f.get('choice') else c[f['name']]) for f in l['fields']})
        else: d[kk] = num_in(c['value'], l.get('float')) if isinstance(c['value'], str) else c['value']
      put(obj, l['path'], [d[kk] for kk in sorted(d)] if l.get('ordered') else d)
  for l in S['leaves']:
    if l['kind'] == 'none' and state.get(l['name']) is True: put(obj, l['path'], None)

def frames(obj):
  out = {}
  if obj is None: return out
  for l in S['leaves']:
    if l['kind'] == 'frame' and not l.get('cls'):
      try:
        v = walk(obj, l['path'])
        out['.'.join(l['path'])] = json.dumps(v, sort_keys=True)
      except Exception: pass
  return out

REAL = {}
def tracer(frame, event, arg):
  f = frame.f_code.co_filename
  if f not in REAL: REAL[f] = os.path.realpath(f)
  if REAL[f] == S['path']:
    def local(fr, ev, a):
      if ev == 'line': HIT.add(fr.f_lineno)
      return local
    return local
  return None

class Clock:
  def __init__(self, real): self.real = real
  def time(self): return float(NOW[0])
  def monotonic(self): return float(NOW[0])
  def perf_counter(self): return float(NOW[0])
  def __getattr__(self, n): return getattr(self.real, n)

class _Now(datetime.datetime):
  """datetime.datetime with now() the request's time (local, naive, as the code's own now())."""
  @classmethod
  def now(cls, tz=None): return datetime.datetime.fromtimestamp(NOW[0], tz)

def pin_clocks(root):
  """The clock the repository's modules read (time.time(), datetime.now()) made the request's time."""
  root = os.path.realpath(root)
  dtm = types.SimpleNamespace(**{k: getattr(datetime, k) for k in dir(datetime) if not k.startswith('__')})
  dtm.datetime = _Now
  for m in list(sys.modules.values()):
    f = getattr(m, '__file__', None)
    if not f or not os.path.realpath(f).startswith(root + os.sep): continue
    for n, v in list(vars(m).items()):
      if v is time_module: setattr(m, n, Clock(v))
      elif v is datetime: setattr(m, n, dtm)
      elif v is datetime.datetime: setattr(m, n, _Now)

def raises_here(key):
  """Whether a call left out raises here, as the request says: only at the sites the rule read it may raise (a call of
  the same callee elsewhere, outside a try that catches it, runs as it is)."""
  a = next((x for x in S.get('answers') or [] if x['key'] == key), None)
  if not a or not a.get('pass') or not a.get('at'): return True
  f = sys._getframe(1)
  while f is not None and os.path.realpath(f.f_code.co_filename) == os.path.realpath(__file__): f = f.f_back
  if f is None: return True
  here, line = os.path.basename(f.f_code.co_filename), f.f_lineno
  for site in a['at']:
    file, l0 = site['p'].split(':')[0], int(site['p'].split(':')[1])
    l1 = int(site['end'].split(':')[0]) if site.get('end') and site['end'].split(':')[0].isdigit() else l0
    if file == here and l0 <= line <= l1: return True
  return False

def raised(r):
  """The exception a stub raises where the request says: the class a handler names, made without its arguments."""
  cls = eval(r[1], vars(importlib.import_module(r[0])))
  try: return cls('gdp: raised where the request says')
  except Exception:
    e = cls.__new__(cls); e.args = ('gdp: raised where the request says',); return e

def stub(key, is_async, orig=None):
  # (orig: a call left out, run as it is unless the request says it raises)
  def value(a_, k_):
    a = CUR.get(key)
    if a is not None and a.get('raise') is not None and raises_here(key): raise raised(a['raise'])
    if orig is not None: return orig(*a_, **k_)
    if a is None or a.get('none'): return None
    return build(a, {})
  if is_async:
    async def f(*a, **k):
      v = value(a, k)
      return (await v) if orig is not None and inspect.isawaitable(v) else v
    return f
  def g(*a, **k): return value(a, k)
  return g

def patch_target(p):
  mod = importlib.import_module(p['mod'])
  o = mod
  for part in p['path'][:-1]: o = getattr(o, part)
  return o, p['path'][-1]

def hello(req):
  S.update(req)
  S['path'] = os.path.realpath(req['path'])
  sys.path.insert(0, req['root'])
  S['mod'] = importlib.import_module(req['module'])
  mod = S['mod']
  pin_clocks(req['root'])
  S['self_stubs'] = []
  for a in req['answers']:
    p = a['patch']
    if p.get('store'): continue
    if p.get('self'): S['self_stubs'].append((p['self'], a))
    else:
      o, name = patch_target(p)
      raw = inspect.getattr_static(o, name, None)
      f = stub(a['key'], a['async'], getattr(o, name) if a.get('pass') else None)
      setattr(o, name, staticmethod(f) if isinstance(raw, staticmethod) else classmethod(lambda cls, *x, **k: f(*x, **k)) if isinstance(raw, classmethod) else f)
  S['cls'] = getattr(mod, req['cls'].rpartition('.')[2]) if req.get('cls') else None
  S['loop'] = asyncio.new_event_loop()
  asyncio.set_event_loop(S['loop'])
  return {'ok': True}

def make(args):
  global OBJ_STORES
  OBJ_STORES = {}
  if S['cls'] is None: obj = types.SimpleNamespace()
  else:
    kw = fixed_args(args, {})
    sys.settrace(tracer)
    try: obj = run(S['cls'](**kw))
    finally: sys.settrace(None)
  for name, a in S['self_stubs']: obj.__dict__[name] = stub(a['key'], a['async'], getattr(obj, name) if a.get('pass') else None)
  for name in S.get('inject') or []: setattr(obj, name, build({'store': name}, OBJ_STORES))
  i = len(OBJS) + 1
  OBJS[i] = (obj, OBJ_STORES)
  return i

def run(x):
  return S['loop'].run_until_complete(x) if inspect.isawaitable(x) else x

def call(req):
  obj, stores = OBJS[req['id']]
  global OBJ_STORES
  OBJ_STORES = stores
  NOW[0] = int(req.get('now') or 0)
  CUR.clear(); CUR.update(req.get('answers') or {})
  fn = getattr(obj, req['m']) if S['cls'] is not None else getattr(S['mod'], req['m'])
  kwargs = fixed_args(req['a'], {})
  before = frames(obj if S['cls'] is not None else None)
  snap = state_of(obj, stores) if S.get('discard') and S['cls'] is not None else None
  sys.settrace(tracer)
  try:
    out = run(fn(**kwargs))
    err = None
  except Exception as e:
    out, err = None, f"{type(e).__name__}: {e}"[:300]
    # (GDP_HARNESS_LOG: each exception the code raised, with its traceback, appended there)
    if os.environ.get('GDP_HARNESS_LOG'):
      import traceback
      with open(os.environ['GDP_HARNESS_LOG'], 'a') as f: f.write(f"{req['m']} {json.dumps(req.get('answers'))}\n{traceback.format_exc()}\n")
  finally:
    sys.settrace(None)
  if err is not None and snap is not None: set_state(obj, stores, snap)
  after = frames(obj if S['cls'] is not None else None)
  for k in before:
    if after.get(k) != before[k]: return {'frame': k}
  return {'out': tag(out), **({'err': err} if err is not None else {})}

def main():
  fin = open(sys.argv[1], 'r'); fout = open(sys.argv[2], 'w')
  for line in fin:
    req = json.loads(line)
    op = req['op']
    try:
      if op in ('new', 'at'): NOW[0] = int(req.get('now') or 0)
      if op == 'hello': res = hello(req)
      elif op == 'new':
        try: res = {'id': make(req['a'])}
        except Exception as e: res = {'err': f"{type(e).__name__}: {e}"[:300]}
      elif op == 'at':
        try:
          i = make(req['a'])
          set_state(OBJS[i][0], OBJS[i][1], req['state'])
          res = {'id': i}
        except Exception as e: res = {'bad': f"{type(e).__name__}: {e}"[:300]}
      elif op == 'get':
        obj, stores = OBJS[req['id']]
        res = {'state': state_of(obj, stores)}
      elif op == 'call': res = call(req)
      elif op == 'coverage': res = {'hit': [[os.path.basename(S['path']), n] for n in sorted(HIT)]}
      else: res = {'error': f"no op {op}"}
    except Exception as e:
      res = {'error': f"{type(e).__name__}: {e}"[:500]}
    fout.write(json.dumps(res) + '\n'); fout.flush()

if __name__ == '__main__':
  main()
