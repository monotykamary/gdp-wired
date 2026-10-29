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

module GdpClock
  def now(*) = Time.at(NOW[0])
end
Time.singleton_class.prepend(GdpClock)
module GdpMono
  def clock_gettime(*a) = a.length > 1 && a[1] != :float_second ? NOW[0] : NOW[0].to_f
end
Process.singleton_class.prepend(GdpMono)
# A clock object the caller stated: its time is the request's.
class GdpStatedClock
  def current_time = NOW[0]
  def now = NOW[0]
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
def sym?(t) = t.is_a?(Hash) && (t['sym'] || (t['k'] == 'opt' && t['of'].is_a?(Hash) && t['of']['sym']))
def build(spec)
  return nil if spec['none']
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
    next if spec.nil? || spec['dflt'] || spec['inert']
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
  {'ok' => true}
end
def make(specs)
  pos, kw = call_args(S['cls'].instance_method(:initialize), specs)
  obj = traced { S['cls'].new(*pos, **kw) }
  OBJS[OBJS.length + 1] = obj
  OBJS.length
end
def call(req)
  obj = OBJS[req['id']]
  NOW[0] = Integer(req['now'] || 0)
  m = obj.method(req['m'])
  pos, kw = call_args(m, req['a'])
  before = frames(obj)
  snap = S['discard'] ? state_of(obj) : nil
  out, err = nil, nil
  begin
    out = traced { m.call(*pos, **kw) }
  rescue StandardError => e
    err = "#{e.class}: #{e.message}"[0, 300]
  end
  set_state(obj, snap) if err && snap
  after = frames(obj)
  before.each { |k, v| return {'frame' => k} if after[k] != v }
  {'out' => tag(out), **(err ? {'err' => err} : {})}
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
