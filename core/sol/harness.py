"""The Solidity front end's check harness (core/extract-sol.ts): the contract's bytecode, compiled by the same solc, run
on foundry's anvil (an EVM over JSON-RPC), spoken to in the step harness's JSON lines over two named pipes (hello, new,
at, get, call, coverage). The standard library only.

How the rule's values are the code's:
- an address is a natural below 2^26: n is the address BASE + n, 0 is address(0);
- a uint256 is a value below the rule's width W (the object's own, any W above the code's constants): v below
  H = ceil(W/2) is v, any other is 2^256 - (W - v). Sums, differences, order and checked overflow are the same on both
  sides wherever no value lands between the two bands; a code value there is outside what the rule compares (a value
  string the step harness reads as outside the rule's numbers);
- a mapping's cell is held where it isn't zero; the cells read are those of every key the object was given or called
  with (the rule's keys are the request's values);
- the contract's ether is `balance`.
"""
import json
import os
import random
import socket
import subprocess
import sys
import time
import urllib.request

TWO256 = 1 << 256
BASE = 1 << 152
S = {}
OBJS = {}
PORT = [0]
RPC_ID = [0]
SHA = {}


def rpc(method, params):
  RPC_ID[0] += 1
  body = json.dumps({'jsonrpc': '2.0', 'id': RPC_ID[0], 'method': method, 'params': params}).encode()
  req = urllib.request.Request(f'http://127.0.0.1:{PORT[0]}', data=body, headers={'content-type': 'application/json'})
  with urllib.request.urlopen(req, timeout=60) as r:
    out = json.loads(r.read())
  if 'error' in out: raise RpcError(out['error'])
  return out['result']


# Many calls in one request (JSON-RPC's batch): their results in order.
def rpc_batch(calls):
  if not calls: return []
  body = []
  for m, p in calls:
    RPC_ID[0] += 1
    body.append({'jsonrpc': '2.0', 'id': RPC_ID[0], 'method': m, 'params': p})
  req = urllib.request.Request(f'http://127.0.0.1:{PORT[0]}', data=json.dumps(body).encode(), headers={'content-type': 'application/json'})
  with urllib.request.urlopen(req, timeout=120) as r:
    out = {x['id']: x for x in json.loads(r.read())}
  res = []
  for b in body:
    x = out[b['id']]
    if 'error' in x: raise RpcError(x['error'])
    res.append(x['result'])
  return res


def keccak_many(hexes):
  todo = [h for h in dict.fromkeys(hexes) if h not in SHA]
  for h, r in zip(todo, rpc_batch([('web3_sha3', ['0x' + h]) for h in todo])): SHA[h] = r[2:]


class RpcError(Exception):
  pass


def start_anvil():
  exe = os.environ.get('GDP_ANVIL') or 'anvil'
  for _ in range(20):
    port = random.randint(20000, 60000)
    with socket.socket() as s:
      if s.connect_ex(('127.0.0.1', port)) == 0: continue
    p = subprocess.Popen([exe, '--port', str(port), '--silent', '--gas-price', '0', '--base-fee', '0', '--disable-block-gas-limit', '--disable-code-size-limit', '--auto-impersonate', '--accounts', '1', '--hardfork', 'cancun'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    S['anvil'] = p
    PORT[0] = port
    for _ in range(100):
      try:
        rpc('web3_clientVersion', [])
        return
      except Exception:
        if p.poll() is not None: break
        time.sleep(0.05)
    p.kill()
  raise RuntimeError('anvil did not start (foundry\'s anvil on the PATH, or $GDP_ANVIL)')


def keccak(hexdata):
  h = SHA.get(hexdata)
  if h is None: h = SHA[hexdata] = rpc('web3_sha3', ['0x' + hexdata])[2:]
  return h


def word(n): return format(n % TWO256, '064x')
def addr_of(n): return 0 if n == 0 else BASE + n
def addr_hex(n): return '0x' + format(addr_of(n), '040x')
def addr_limit(): return 1 << (S['addrBits'] or 152)
def n_of_addr(a):
  if a == 0: return 0
  n = a - BASE
  if 0 < n < addr_limit(): return n
  return None


def half(W): return (W + 1) // 2
def to_code(v, W):
  return v if v < half(W) else TWO256 - (W - v)
def to_rule(c, W):
  if c < half(W): return c
  if c >= TWO256 - (W - half(W)): return W - (TWO256 - c)
  return None


# A value of a kind, the rule's to the code's and back (None: outside what the rule compares).
def enc(kind, v, W):
  if kind == 'u256': return to_code(int(v), W)
  if kind == 'addr': return addr_of(int(v))
  if kind == 'bool': return 1 if v is True or v == 'true' else 0
  if kind.startswith('choice:'): return kind[7:].split('|').index(v)
  if kind.startswith('i'): return int(v) % (1 << int(kind[1:]))
  return int(v)


def dec(kind, c, W):
  if kind == 'u256':
    r = to_rule(c, W)
    return 'outside' if r is None else str(r)
  if kind == 'addr':
    r = n_of_addr(c)
    return 'outside' if r is None else str(r)
  if kind == 'bool': return c != 0
  if kind.startswith('choice:'):
    vals = kind[7:].split('|')
    return vals[c] if c < len(vals) else 'outside'
  if kind.startswith('i'):
    b = int(kind[1:])
    return str(c - (1 << b) if c >= 1 << (b - 1) else c)
  return str(c)


def fits(kind, v, W):
  if kind == 'u256': return 0 <= int(v) < W
  if kind == 'addr': return 0 <= int(v) < addr_limit()
  if kind.startswith('u') and kind[1:].isdigit(): return 0 <= int(v) < (1 << int(kind[1:]))
  if kind.startswith('i') and kind[1:].isdigit(): b = int(kind[1:]); return -(1 << (b - 1)) <= int(v) < (1 << (b - 1))
  return True


# --- storage ------------------------------------------------------------------------------------------------------------
def slot_of(label):
  return S['slots'][label]


def key_word(kind, k, W):
  return word(enc(kind, k, W))


def cell_slot(label, key, W):
  s = slot_of(label)
  base = int(s['slot'])
  kk = S['keys'][label]
  return int(keccak(key_word(kk[0], key, W) + word(base)), 16)


# A mapping of mappings the rule reads as any value (an input of the request): every cell of the addresses the object
# has seen set to it before the call, as the code then reads it.
def set_havoc(o, label, v, W):
  kk, base, cs = S['keys'][label], word(int(slot_of(label)['slot'])), sorted(c for c in o['cands'] if c >= 0)
  outer = [key_word(kk[0], a, W) + base for a in cs if fits(kk[0], a, W)]
  keccak_many(outer)
  inner = [key_word(kk[1], b, W) + keccak(h) for h in outer for b in cs if fits(kk[1], b, W)]
  keccak_many(inner)
  rpc_batch([('anvil_setStorageAt', [o['addr'], '0x' + keccak(h), '0x' + word(v)]) for h in inner])


def read_slot(addr, slot):
  return int(rpc('eth_getStorageAt', [addr, hex(slot), 'latest']), 16)


def write_slot(addr, slot, value):
  rpc('anvil_setStorageAt', [addr, '0x' + word(slot), '0x' + word(value)])


def read_field(o, label):
  s = slot_of(label)
  w = read_slot(o['addr'], int(s['slot']))
  return (w >> (8 * s['offset'])) & ((1 << (8 * s['bytes'])) - 1)


def write_field(o, label, value):
  s = slot_of(label)
  slot = int(s['slot'])
  w = read_slot(o['addr'], slot)
  mask = ((1 << (8 * s['bytes'])) - 1) << (8 * s['offset'])
  write_slot(o['addr'], slot, (w & ~mask) | ((value << (8 * s['offset'])) & mask))


# --- requests -------------------------------------------------------------------------------------------------------------
def hello(req):
  S.update(req['sol'])
  S['leaves'] = req['leaves']
  S['ctorSpec'] = req['ctor']
  # Each mapping's key kinds (one, or two for a mapping of mappings) and value kind.
  S['keys'] = {}
  for label, k in S['kinds'].items():
    if k.startswith('map:'): S['keys'][label] = S['mapKeys'][label]
  start_anvil()
  return {'ok': True}


def fund(a, value):
  # (exactly the value: gas costs nothing here, and an account that receives a value near 2^256 must have room for it)
  rpc('anvil_setBalance', [a, hex(value)])


def arg_value(spec):
  if 'in' in spec: return spec['in']
  return 0


def send(frm, to, data, value, deploy=False):
  tx = {'from': frm, 'data': '0x' + data, 'value': hex(value), 'gas': hex(30_000_000), 'gasPrice': '0x0'}
  if not deploy: tx['to'] = to
  fund(frm, value)
  try:
    h = rpc('eth_sendTransaction', [tx])
  except RpcError as e:
    return None, str(e)[:300]
  r = None
  for i in range(200):
    r = rpc('eth_getTransactionReceipt', [h])
    if r is not None: break
    time.sleep(0.002 * (i + 1))
  if r is None: return None, 'no receipt'
  if int(r['status'], 16) != 1: return None, 'reverted'
  return r, None


def abi_args(types, vals, W):
  return ''.join(word(enc(kind_of_type(t), v, W)) for t, v in zip(types, vals))


def kind_of_type(t):
  t = t.split(' ')[0] if not t.startswith('enum ') else t
  if t == 'uint256': return 'u256'
  if t.startswith('address'): return 'addr'
  if t == 'bool': return 'bool'
  if t.startswith('enum '): return 'u8'
  if t.startswith('uint'): return 'u' + t[4:]
  if t.startswith('int'): return 'i' + t[3:]
  raise ValueError(f'an argument of {t}')


def make(args):
  a = dict((n, arg_value(s)) for n, s in args)
  W = int(a.get(S['mod'], 0))
  if W < S['minW']: raise ValueError(f'a width below {S["minW"]}')
  # (a width the bands can't hold apart: sums of small values would land between them)
  if W < (1 << 40): raise ValueError('a width below 2^40 (the check compares the code at 2^52 and at the prover\'s witnesses from 2^40)')
  sender = int(a.get('msg.sender', 1))
  if not 0 < sender < addr_limit(): raise ValueError('msg.sender outside the addresses')
  params = [n for n, _ in args if n not in (S['mod'], 'msg.sender', 'msg.value')]
  for n, t in zip(params, S['ctor']['inputs']):
    if not fits(kind_of_type(t), a[n], W): raise ValueError(f'{n} outside its type')
  if not fits('u256', a.get('msg.value', 0), W): raise ValueError('msg.value outside its type')
  data = S['creation'] + abi_args(S['ctor']['inputs'], [a[n] for n in params], W)
  r, err = send(addr_hex(sender), None, data, to_code(int(a.get('msg.value', 0)), W), deploy=True)
  if err: raise ValueError(err)
  i = len(OBJS) + 1
  OBJS[i] = {'addr': r['contractAddress'], 'W': W, 'cands': {0, sender} | set(int(a[n]) for n, t in zip(params, S['ctor']['inputs']) if kind_of_type(t) in ('addr', 'u256')), 'held': {}}
  return i


FRESH = [0]
def at(args, state):
  i = make(args)
  o = OBJS[i]
  W = o['W']
  # A fresh address with the contract's code, its storage only what the state says.
  FRESH[0] += 1
  fresh = '0x' + format(0xC0DE << 140 | FRESH[0], '040x')
  rpc('anvil_setCode', [fresh, rpc('eth_getCode', [o['addr'], 'latest'])])
  o['addr'] = fresh
  for l in S['leaves']:
    if l['kind'] == 'frame': continue
    label = l['path'][0]
    v = state.get(l['name'])
    if label == S['mod']:
      if int(v) != W: raise ValueError('a width other than the object\'s')
      continue
    if label == 'balance':
      if not fits('u256', v, W): raise ValueError('a balance outside its type')
      rpc('anvil_setBalance', [fresh, hex(to_code(int(v), W))])
      continue
    k = S['kinds'][label]
    if l['kind'] == 'map':
      vk = k[4:]
      for key, c in (v or {}).items():
        key = int(key)
        x = c['value']
        if x in (0, '0', False): raise ValueError('a cell held at zero (no state of a mapping)')
        if not fits(vk, x, W): raise ValueError('a cell outside its type')
        if not key_fits(label, key, W): raise ValueError('a key outside its type')
        write_slot(fresh, cell_slot(label, key, W), enc(vk, x, W))
        o['held'].setdefault(label, set()).add(key)
        note_key(o, label, key)
      continue
    if not fits(k, v, W): raise ValueError(f'{label} outside its type')
    write_field(o, label, enc(k, v, W))
    if k in ('addr', 'u256'): o['cands'].add(int(v))
  return i


def key_fits(label, key, W): return fits(S['keys'][label][0], key, W)
def note_key(o, label, key): o['cands'].add(key)
def keys_of(o, label, W): return [c for c in sorted(o['cands']) if c >= 0 and key_fits(label, c, W)]


def state_of(i):
  o = OBJS[i]
  W = o['W']
  s = {}
  # (every slot the state reads, hashed and read in two batches)
  cells = [(l, key) for l in S['leaves'] if l['kind'] == 'map' for key in keys_of(o, l['path'][0], W)]
  keccak_many([key_word(S['keys'][l['path'][0]][0], key, W) + word(int(slot_of(l['path'][0])['slot'])) for l, key in cells])
  slots = [cell_slot(l['path'][0], key, W) for l, key in cells]
  vals = dict(zip([(l['name'], key) for l, key in cells], [int(x, 16) for x in rpc_batch([('eth_getStorageAt', [o['addr'], hex(sl), 'latest']) for sl in slots])]))
  for l in S['leaves']:
    if l['kind'] == 'frame': continue
    label = l['path'][0]
    if label == S['mod']: s[l['name']] = str(W); continue
    if label == 'balance':
      s[l['name']] = dec('u256', int(rpc('eth_getBalance', [o['addr'], 'latest']), 16), W)
      continue
    k = S['kinds'][label]
    if l['kind'] == 'map':
      vk = k[4:]
      cells = {}
      for key in keys_of(o, label, W):
        c = vals[(l['name'], key)]
        if c != 0: cells[str(key)] = {'value': dec(vk, c, W)}
      s[l['name']] = cells
      continue
    s[l['name']] = dec(k, read_field(o, label), W)
  return s


def call(req):
  o = OBJS[req['id']]
  W = o['W']
  m = req['m']
  e = S['entries'][m]
  a = dict((n, arg_value(s)) for n, s in req['a'])
  sender = int(a.get('msg.sender', 0))
  if not 0 < sender < addr_limit(): return {'err': 'msg.sender outside the addresses'}
  if req.get('now'):
    try: rpc('evm_setNextBlockTimestamp', [int(req['now'])])
    except RpcError as x: return {'bad': f'the time {req["now"]}: {x}'}
  data, value, bad = calldata(o, m, req['a'], W)
  if bad: return {'err': bad}
  bad = havoc(o, req.get('answers') or {}, W)
  if bad: return {'err': bad}
  frm = addr_hex(sender)
  fund(frm, value)
  tx = {'from': frm, 'to': o['addr'], 'data': '0x' + data, 'value': hex(value), 'gas': hex(30_000_000), 'gasPrice': '0x0'}
  try:
    ret = rpc('eth_call', [tx, 'latest'])
  except RpcError as x:
    return {'err': f'reverted: {str(x)[:200]}'}
  r, err = send(frm, o['addr'], data, value)
  if err: return {'err': err}
  out = None
  if e.get('out'):
    c = int(ret[2:66] or '0', 16)
    k = kind_of_type(e['out'])
    v = dec(k, c, W)
    out = v if isinstance(v, bool) else {'n': v}
  return {'out': out}


# A call's data and value (the rule's arguments as the code's), or why it can't be made.
def calldata(o, m, args, W):
  e = S['entries'][m]
  a = dict((n, arg_value(s)) for n, s in args)
  params = [n for n, _ in args if n not in ('msg.sender', 'msg.value')]
  for n, t in zip(params, e['inputs']):
    if not fits(kind_of_type(t), a[n], W): return None, None, f'{n} outside its type'
    if kind_of_type(t) in ('addr', 'u256'): o['cands'].add(int(a[n]))
  o['cands'].add(int(a.get('msg.sender', 0)))
  if not fits('u256', a.get('msg.value', 0), W): return None, None, 'msg.value outside its type'
  data = '' if m in ('receive', 'fallback') else S['ids'][e['sig']] + abi_args(e['inputs'], [a[n] for n in params], W)
  return data, to_code(int(a.get('msg.value', 0)), W), None


# The answers of the mappings of mappings read (the rule's inputs): each set in the code's cells.
def havoc(o, answers, W):
  for label in S.get('havoc') or []:
    a = answers.get(label)
    if a is None: continue
    v = a.get('in', 0)
    kind = S['kinds'][label][4:]
    if not fits(kind, v, W): return f'{label} answers {v}, outside its type'
    set_havoc(o, label, enc(kind, v, W), W)
  return None


# --- re-entrant runs replayed: an Agent at every address, a Director with the run's script --------------------------------
DIRECTOR = 0xD1EC70


def abi_dyn(t, kinds, froms, values, rets, datas):
  def arr(xs): return word(len(xs)) + ''.join(word(x) for x in xs)
  def barr(bs):
    heads, tails, off = [], [], 32 * len(bs)
    for b in bs:
      raw = bytes.fromhex(b)
      body = word(len(raw)) + raw.hex() + '00' * ((32 - len(raw) % 32) % 32)
      heads.append(word(off)); tails.append(body); off += len(body) // 2
    return word(len(bs)) + ''.join(heads) + ''.join(tails)
  parts = [arr(kinds), arr(froms), arr(values), arr([1 if r else 0 for r in rets]), barr(datas)]
  head, off, tail = word(t), 32 * 6, ''
  for p in parts:
    head += word(off); tail += p; off += len(p) // 2
  return head + tail


def replay(req):
  hello({'sol': req['sol'], 'leaves': req['leaves'], 'ctor': req['ctorSpec']})
  i = make(req['ctor'])
  o = OBJS[i]
  W = o['W']
  d = '0x' + format(DIRECTOR, '040x')
  rpc('anvil_setCode', [d, '0x' + req['director']])
  run_sel = keccak('run(address,uint8[],address[],uint256[],bool[],bytes[])'.encode().hex())[:8]
  oks_sel, count_sel = keccak('oks(uint256)'.encode().hex())[:8], keccak('count()'.encode().hex())[:8]
  agents = set()
  out = {'states': [], 'oks': []}
  for g in req['groups']:
    kinds, froms, values, rets, datas = [], [], [], [], []
    for e in g:
      if e['kind'] == 'ret':
        kinds.append(1); froms.append(0); values.append(0); rets.append(bool(e['ok'])); datas.append('')
        continue
      a = dict((n, arg_value(s)) for n, s in e['a'])
      data, value, bad = calldata(o, e['m'], e['a'], W)
      if bad: return {'error': f'a call the code can\'t be given: {bad}'}
      sender = int(a.get('msg.sender', 0))
      if not 0 < sender < addr_limit(): return {'error': 'msg.sender outside the addresses'}
      if sender not in agents:
        rpc('anvil_setCode', [addr_hex(sender), '0x' + req['agent']])
        agents.add(sender)
      rpc('anvil_setBalance', [addr_hex(sender), hex(min(value + (1 << 128), TWO256 - 1))])
      if e.get('answers'):
        if len(g) > 1: return {'error': 'a mapping of mappings read inside a call of another (the replay sets its cells before a transaction)'}
        bad = havoc(o, e['answers'], W)
        if bad: return {'error': bad}
      kinds.append(0); froms.append(addr_of(sender)); values.append(value); rets.append(False); datas.append(data)
    frm = '0x' + format(0xBEEF << 140, '040x')
    r, err = send(frm, d, run_sel + abi_dyn(int(o['addr'], 16), kinds, froms, values, rets, datas), 0)
    if err: return {'error': f'transaction {len(out["states"]) + 1} reverts: {err}', **out}
    n = int(rpc('eth_call', [{'to': d, 'data': '0x' + count_sel}, 'latest']), 16)
    out['oks'].append([int(rpc('eth_call', [{'to': d, 'data': '0x' + oks_sel + word(k)}, 'latest']), 16) == 1 for k in range(n)])
    out['states'].append(state_of(i))
  return out


def main():
  if sys.argv[1] == '--replay':
    req = json.load(open(sys.argv[2]))
    try: res = replay(req)
    except Exception as e: res = {'error': f'{type(e).__name__}: {e}'[:500]}
    finally:
      if S.get('anvil'): S['anvil'].kill()
    print(json.dumps(res))
    return
  fin = open(sys.argv[1], 'r'); fout = open(sys.argv[2], 'w')
  try:
    for line in fin:
      req = json.loads(line)
      op = req['op']
      try:
        if op == 'hello': res = hello(req)
        elif op == 'new':
          try: res = {'id': make(req['a'])}
          except Exception as e: res = {'err': f'{type(e).__name__}: {e}'[:300]}
        elif op == 'at':
          try: res = {'id': at(req['a'], req['state'])}
          except Exception as e: res = {'bad': f'{type(e).__name__}: {e}'[:300]}
        elif op == 'get': res = {'state': state_of(req['id'])}
        elif op == 'call': res = call(req)
        elif op == 'coverage': res = {'hit': []}
        else: res = {'error': f'no op {op}'}
      except Exception as e:
        res = {'error': f'{type(e).__name__}: {e}'[:500]}
      fout.write(json.dumps(res) + '\n'); fout.flush()
  finally:
    if S.get('anvil'): S['anvil'].kill()


if __name__ == '__main__':
  main()
