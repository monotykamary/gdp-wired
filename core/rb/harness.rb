# The Ruby side of the extractor's check (core/extract-step.ts's checkStep): the file loaded as it ships, its object
# made, set to a state, called with the rule's requests and read back, one JSON line a request over two named pipes.
# The clock is the request's time: Time.now, Process.clock_gettime and a clock object the caller stated (its
# current_time and now) read it. Line events (TracePoint) count the branch arms reached. A library the file requires
# and this Ruby lacks is skipped (only the class read runs).
#
#   ruby core/rb/harness.rb <in-fifo> <out-fifo>
require 'json'

NOW = [0]
HIT = {}
S = {}
OBJS = {}
# Real references retained strongly: object_id reuse must never create aliases.
NATIVE_OBJECTS = {}.compare_by_identity
NATIVE_INVOCATION = [0]
NATIVE_IS = Object.instance_method(:instance_of?)
NATIVE_CLASS = Object.instance_method(:class)
NATIVE_CLASS_NAME = Module.instance_method(:name)
NATIVE_VARS = Object.instance_method(:instance_variables)
NATIVE_GET_VAR = Object.instance_method(:instance_variable_get)
NATIVE_EQUAL = BasicObject.instance_method(:equal?)
NATIVE_COPY_STRING = String.method(:new)
NATIVE_ARRAY_EACH = Array.instance_method(:each)
NATIVE_HASH_EACH = Hash.instance_method(:each_pair)
NATIVE_HASH_DEFAULT = Hash.instance_method(:default)
NATIVE_HASH_DEFAULT_PROC = Hash.instance_method(:default_proc)
def native_is?(value, klass) = NATIVE_IS.bind_call(value, klass)
def native_same?(a, b) = NATIVE_EQUAL.bind_call(a, b)
def native_class(value) = NATIVE_CLASS.bind_call(value)
def native_class_name(value) = NATIVE_CLASS_NAME.bind_call(native_class(value))
def native_state(root, bindings: false, records: false)
  seen = {}
  nodes = 0
  encode = nil
  encode = lambda do |value, object_root = false|
    nodes += 1
    raise ArgumentError, 'native snapshot exceeds node bound' if nodes > 10000
    return value if native_same?(value, nil) || native_same?(value, true) || native_same?(value, false)
    return NATIVE_COPY_STRING.call(value).freeze if native_is?(value, String)
    # Symbols cross the wire as native enum labels, never choice indexes.
    return value.to_s if native_is?(value, Symbol)
    if native_is?(value, Integer) || native_is?(value, Float)
      raise ArgumentError, 'native snapshot number is outside exact integer range' unless value.finite? && value.abs <= 9007199254740991 && value == value.to_i
      return value.to_i
    end
    # A store exposes its actual Hash, retaining keys and native identity.
    value = value.data if native_is?(value, GdpStore)
    unless NATIVE_OBJECTS.key?(value)
      raise ArgumentError, 'native snapshot exceeds identity bound' if NATIVE_OBJECTS.length >= 100000
      NATIVE_OBJECTS[value] = (NATIVE_OBJECTS.length + 1).to_s
    end
    id = NATIVE_OBJECTS[value]
    return {'kind' => 'ref', 'id' => id} if seen[id]
    seen[id] = true
    if native_is?(value, Array)
      kind, items = 'array', []
      NATIVE_ARRAY_EACH.bind_call(value) { |v| items << encode.call(v) }
    elsif native_is?(value, Hash)
      raise ArgumentError, 'unsupported native Hash default' unless native_same?(NATIVE_HASH_DEFAULT.bind_call(value), nil) && native_same?(NATIVE_HASH_DEFAULT_PROC.bind_call(value), nil)
      kind = object_root || records ? 'object' : 'map'
      items = []
      NATIVE_HASH_EACH.bind_call(value) do |k, v|
        valid = object_root || records ? native_is?(k, String) : native_is?(k, String) || native_is?(k, Integer)
        raise ArgumentError, 'unsupported native snapshot map key' unless valid
        items << [encode.call(k), encode.call(v)]
      end
    else
      # Opaque Time/IO/Mutex/etc. have no faithful wire encoding.
      vars = NATIVE_VARS.bind_call(value)
      # An uninitialized Ruby instance variable reads as nil. Observe that
      # actual read for source-declared roots too (e.g. @last before first hit).
      if native_same?(value, root) && !bindings
        declared = (S['leaves'] || []).filter_map { |l| l['path']&.first if l['kind'] != 'frame' }
        vars |= declared.filter_map { |name| name.to_sym if name.is_a?(String) && name.start_with?('@') }
      end
      raise ArgumentError, "unsupported native snapshot object #{native_class(value)}" if vars.empty? && native_class(value) != S['cls']
      kind = 'object'
      items = vars.map { |k| [k.to_s.delete_prefix('@'), encode.call(NATIVE_GET_VAR.bind_call(value, k))] }
    end
    {'kind' => kind, 'id' => id, 'items' => items}
  end
  {'version' => 1, 'root' => encode.call(root, bindings)}
end

# Invocation-local observations contain only values a native operation actually
# returned/raised. Missing calls stay absent; repeated inconsistent reads refuse.
NATIVE_EVENTS = [nil]
NATIVE_EVENT_ERROR = [nil]
NATIVE_CALL_TYPES = {}
def native_scalar(value)
  return value if native_same?(value, nil) || native_same?(value, true) || native_same?(value, false)
  return NATIVE_COPY_STRING.call(value).freeze if native_is?(value, String)
  return value.to_s.freeze if native_is?(value, Symbol)
  if native_is?(value, Integer) || native_is?(value, Float)
    raise ArgumentError, 'native observation number is outside exact integer range' unless value.finite? && value.abs <= 9007199254740991 && value == value.to_i
    return value.to_i
  end
  raise ArgumentError, "unsupported native observation value #{native_class(value)}"
end
def native_record(key, outcome, native_type = nil)
  return unless (events = NATIVE_EVENTS[0])
  before = events['calls'][key]
  previous_type = NATIVE_CALL_TYPES[key]
  if native_type && previous_type && !native_same?(native_type, previous_type)
    raise ArgumentError, "inconsistent native call type #{key}"
  end
  NATIVE_CALL_TYPES[key] = native_type if native_type
  raise ArgumentError, "inconsistent native call #{key}" if before && before != outcome
  events['calls'][key] = outcome
rescue StandardError => e
  NATIVE_EVENT_ERROR[0] ||= "#{e.class}: #{e.message}"[0, 300]
end
def native_call(key)
  value = yield
  if NATIVE_EVENTS[0]
    begin
      native_record(key, {'kind' => 'returned', 'value' => native_scalar(value)}, native_class(value))
    rescue StandardError => e
      NATIVE_EVENT_ERROR[0] ||= "#{e.class}: #{e.message}"[0, 300]
    end
  end
  value
rescue Exception => e # Record the actual runtime class, never the requested handler.
  native_record(key, {'kind' => 'raised', 'raised' => native_class_name(e)})
  raise
end
def native_clock(value)
  if (events = NATIVE_EVENTS[0])
    begin
      actual = native_scalar(value)
      raise ArgumentError, 'inconsistent native clock reads' if events.key?('clock') && events['clock'] != actual
      events['clock'] = actual
    rescue StandardError => e
      NATIVE_EVENT_ERROR[0] ||= "#{e.class}: #{e.message}"[0, 300]
    end
  end
  value
end
module GdpClock
  def now(*)
    value = Time.at(NOW[0])
    native_clock(value.to_i)
    value
  end
end
Time.singleton_class.prepend(GdpClock)
module GdpMono
  def clock_gettime(*a) = native_clock(a.length > 1 && a[1] != :float_second ? NOW[0] : NOW[0].to_f)
end
Process.singleton_class.prepend(GdpMono)
# A clock object the caller stated: its time is the request's.
class GdpStatedClock
  def current_time = native_clock(NOW[0])
  def now = native_clock(NOW[0])
end

def enc_num(v)
  return v if v == true || v == false
  return v.to_s if v.is_a?(Integer)
  return (v.finite? && v == v.floor && v.abs < 2**63 ? v.to_i.to_s : "f:#{v}") if v.is_a?(Float)
  "?:#{v.class}"
end
def tag(v)
  return v if v.nil? || v == true || v == false
  return {'n' => enc_num(v)} if v.is_a?(Numeric)
  return {'s' => v.to_s} if v.is_a?(String) || v.is_a?(Symbol)
  {'o' => v.class.name}
end
# An answered call's value: the request's input for it (core/extract-step.ts's answers), None where it says so.
CUR = {}
def answer(key) = (a = CUR[key]).nil? || a['none'] ? nil : build(a)
# (a call inside a rescue's begin: raises the class the request says; one left out runs as it is unless it raises)
def raising(key) = (r = CUR[key]&.[]('raise')) && raise(Object.const_get(r), 'gdp: raised where the request says')
def stub(key) = proc { |*_a, **_k| native_call(key) { raising(key); answer(key) } }
# A store (stated, or an injected dependency inferred): get, set and delete over a Hash that keeps what is set; its
# other methods answered.
class GdpStore
  attr_reader :data
  def initialize(name, decl)
    @data = {}
    {'get' => %w[get], 'set' => %w[set], 'delete' => %w[delete]}.each do |kind, dflt|
      (decl[kind] || dflt).each do |m|
        define_singleton_method(m) do |*a, **k|
          raising("#{name}.#{m}")
          key = k[:key] || a[0]
          case kind
          when 'get' then @data[key]
          when 'set' then @data[key] = k.key?(:value) ? k[:value] : a[1]
          else @data.delete(key)
          end
        end
      end
    end
    # (a method left out: nothing, as the rule takes it; any other is no method of this store, and fails)
    (decl['skip'] || []).each { |m| define_singleton_method(m) { |*_a, **_k| nil } }
    S['answers'].each { |x| define_singleton_method(x['patch']['path'][-1], &stub(x['key'])) if x['patch']['store'] == name && !x['pass'] }
  end
end
# (each object's stores, by its id; the one being made's in $stores)
SOBJ = {}
$stores = {}
def tpl_match(tpl, key)
  pre, post = tpl.split('{}', 2)
  return (key == tpl ? '' : nil) if post.nil?
  key.is_a?(String) && key.start_with?(pre) && key.end_with?(post) && key.length >= pre.length + post.length ? key[pre.length...(key.length - post.length)] : nil
end
def sym?(t) = t.is_a?(Hash) && (t['sym'] || (t['k'] == 'opt' && t['of'].is_a?(Hash) && t['of']['sym']))
def build(spec)
  return nil if spec['none']
  return ($stores[spec['store']] ||= GdpStore.new(spec['store'], S['stores'][spec['store']] || {})) if spec['store']
  if spec.key?('in')
    v = spec['in']
    return v.to_sym if spec['sym'] && v.is_a?(String)
    return spec['float'] ? Integer(v).to_f : (v.is_a?(String) && v =~ /\A-?\d+\z/ ? Integer(v) : v)
  end
  raise ArgumentError, "an argument spec #{spec}"
end
def walk(o, path) = path.reduce(o) { |x, p| x.instance_variable_get(p) }
def put(o, path, v) = walk(o, path[0..-2]).instance_variable_set(path[-1], v)

def state_of(obj)
  S['leaves'].each_with_object({}) do |l, s|
    k = l['kind']
    if l['store']
      s[l['name']] = (SOBJ[obj.object_id]&.[](l['store'])&.data || {}).each_with_object({}) { |(key, v), c| h = tpl_match(l['tpl'], key); c[h] = {'value' => enc_num(v)} if h }
      next
    end
    next if k == 'frame' || k == 'map'
    v = walk(obj, l['path'])
    s[l['name']] = case k
                   when 'none' then v.nil?
                   when 'num' then v.nil? ? '0' : enc_num(v)
                   when 'str', 'choice' then v.nil? ? '' : v.to_s
                   when 'bool' then v.nil? ? false : v
                   end
  end
end
def set_state(obj, st)
  S['leaves'].each do |l|
    k, v = l['kind'], st[l['name']]
    if l['store'] && (d = SOBJ[obj.object_id]&.[](l['store'])&.data)
      d.delete_if { |key, _| tpl_match(l['tpl'], key) }
      pre, post = l['tpl'].split('{}', 2)
      (v || {}).each { |h, c| d[post.nil? ? l['tpl'] : "#{pre}#{h}#{post}"] = l['float'] ? Integer(c['value']).to_f : Integer(c['value']) }
      next
    end
    case k
    when 'num' then put(obj, l['path'], l['float'] ? Integer(v).to_f : Integer(v))
    when 'str', 'choice' then put(obj, l['path'], sym?(l['t']) ? v.to_sym : v)
    when 'bool' then put(obj, l['path'], v)
    end
  end
  S['leaves'].each { |l| put(obj, l['path'], nil) if l['kind'] == 'none' && st[l['name']] == true }
end
def frames(obj)
  S['leaves'].select { |l| l['kind'] == 'frame' && !l['cls'] }.each_with_object({}) do |l, out|
    out[l['path'].join('.')] = (walk(obj, l['path']).inspect rescue nil)
  end
end
# The arguments, by the method's own parameters: positional ones in order, keywords by name; a stated clock given.
def call_args(m, specs)
  given = specs.to_h
  pos, kw = [], {}
  m.parameters.each do |kind, name|
    n = name.to_s
    if S['clocks'].include?(n) && %i[key keyreq].include?(kind) then kw[name] = GdpStatedClock.new; next end
    spec = given[n]
    next if spec.nil? || spec['dflt']
    # (an argument the rule doesn't read: nil where it is required, else its default)
    if spec['inert'] then kind == :req ? pos << nil : kind == :keyreq ? kw[name] = nil : nil; next end
    if spec['store'] && %i[key keyreq].include?(kind) then kw[name] = build(spec); next end
    %i[key keyreq].include?(kind) ? kw[name] = build(spec) : pos << build(spec)
  end
  [pos, kw]
end
def traced
  tp = TracePoint.new(:line) { |t| HIT[t.lineno] = true if t.path == S['path'] }
  tp.enable { yield }
end

def hello(req)
  S.update(req)
  S['path'] = File.realpath(req['path'])
  S['clocks'] ||= []
  $LOAD_PATH.unshift(req['root'])
  # (a library the file requires that this Ruby lacks: taken as loaded, the class read being the code's own)
  tries = 0
  begin
    [*S['loads'], S['path']].each { |f| load f }
  rescue LoadError => e
    raise if (tries += 1) > 20 || !e.path
    $LOADED_FEATURES << "#{e.path}.rb"
    retry
  end
  S['cls'] = Object.const_get(req['cls'])
  # (an answered call of another class's code: the stub prepended to that class's method, as the clock's is; the class
  # made where a library is missing)
  S['answers'].each do |a|
    next unless (mod = a['patch']['mod'])
    c = mod.split('::').reject(&:empty?).reduce(Object) { |o, n| o.const_defined?(n, false) ? o.const_get(n, false) : o.const_set(n, Module.new) }
    m, st, key = a['patch']['path'][-1], stub(a['key']), a['key']
    c.singleton_class.prepend(Module.new { a['pass'] ? define_method(m) { |*x, **k, &b| native_call(key) { raising(key); super(*x, **k, &b) } } : define_method(m, &st) })
  end
  {'ok' => true, 'nativeSnapshot' => 1, 'nativeBindings' => 1, 'nativeObservations' => 1, 'nativeEquality' => 'scalar'}
end
def make(specs)
  $stores = {}
  pos, kw = call_args(S['cls'].instance_method(:initialize), specs)
  obj = traced { S['cls'].new(*pos, **kw) }
  SOBJ[obj.object_id] = $stores
  OBJS[OBJS.length + 1] = obj
  OBJS.length
end
def call(req)
  obj = OBJS[req['id']]
  NOW[0] = Integer(req['now'] || 0)
  CUR.replace(req['answers'] || {})
  NATIVE_INVOCATION[0] += 1
  raise ArgumentError, 'native invocation exceeds exact integer range' if NATIVE_INVOCATION[0] > 9007199254740991
  NATIVE_EVENTS[0] = {'invocation' => NATIVE_INVOCATION[0], 'calls' => {}}
  NATIVE_EVENT_ERROR[0] = nil
  NATIVE_CALL_TYPES.clear
  m = obj.method(req['m'])
  pos, kw = call_args(m, req['a'])
  before = frames(obj)
  snap = S['discard'] ? state_of(obj) : nil
  out, err = nil, nil
  bindings = {'error' => 'native method entry was not observed'}
  entered = false
  # Defaults and keyword arguments are bound before :call. Read actual locals
  # before the first body instruction, never the request's argument envelopes.
  capture = TracePoint.new(:call) do |event|
    next if entered || !event.self.equal?(obj) || event.defined_class != m.owner || event.method_id != m.original_name
    entered = true
    begin
      values = m.parameters.to_h do |kind, name|
        raise ArgumentError, 'unsupported anonymous or block native parameter' if name.nil? || kind == :block
        [name.to_s, event.binding.local_variable_get(name)]
      end
      bindings = {'snapshot' => native_state(values, bindings: true)}
    rescue StandardError => e
      bindings = {'error' => "#{e.class}: #{e.message}"[0, 300]}
    end
  end
  begin
    capture.enable
    out = traced { m.call(*pos, **kw) }
  rescue StandardError => e
    err = "#{e.class}: #{e.message}"[0, 300]
  ensure
    capture.disable
  end
  set_state(obj, snap) if err && snap
  after = frames(obj)
  before.each { |k, v| return {'frame' => k} if after[k] != v }
  observations = begin
    raise ArgumentError, NATIVE_EVENT_ERROR[0] if NATIVE_EVENT_ERROR[0]
    {'snapshot' => native_state(NATIVE_EVENTS[0], bindings: true, records: true)}
  rescue StandardError => e
    {'error' => "#{e.class}: #{e.message}"[0, 300]}
  ensure
    NATIVE_EVENTS[0] = nil
  end
  {'out' => tag(out), 'nativeBindings' => bindings, 'nativeObservations' => observations, **(err ? {'err' => err} : {})}
end

fin, fout = File.open(ARGV[0], 'r'), File.open(ARGV[1], 'w')
fin.each_line do |line|
  req = JSON.parse(line)
  op = req['op']
  res = begin
    NOW[0] = Integer(req['now'] || 0) if %w[new at].include?(op)
    case op
    when 'hello' then hello(req)
    when 'new'
      begin
        {'id' => make(req['a'])}
      rescue StandardError => e
        {'err' => "#{e.class}: #{e.message}"[0, 300]}
      end
    when 'at'
      begin
        i = make(req['a'])
        set_state(OBJS[i], req['state'])
        {'id' => i}
      rescue StandardError => e
        {'bad' => "#{e.class}: #{e.message}"[0, 300]}
      end
    when 'get' then {'state' => state_of(OBJS[req['id']])}
    when 'native' then {'snapshot' => native_state(OBJS[req['id']])}
    when 'call' then call(req)
    when 'coverage' then {'hit' => HIT.keys.sort.map { |n| [File.basename(S['path']), n] }}
    else {'error' => "no op #{op}"}
    end
  rescue StandardError, ScriptError => e
    {'error' => "#{e.class}: #{e.message}"[0, 500]}
  end
  fout.write("#{JSON.generate(res)}\n")
  fout.flush
end
