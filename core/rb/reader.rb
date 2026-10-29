# The extractor's Ruby reader (core/extract-rb.ts): a file read through Ruby's own parser (Prism) and lowered into the
# shared step IR (core/extract-step.ts's SModule, as JSON on stdout), which one TypeScript executor runs into the rule.
# Nothing here decides what is in the subset beyond the syntax: a construct the IR has no node for becomes
# {"e": "no"} or {"s": "no"} with the reason, refused by the executor only where a step reaches it. Ruby states no
# types, so the reader infers them from the code itself: a field's from what is assigned to it (symbols a choice, nil
# with numbers an optional number), an argument's from what it is compared with or computed into. The check runs the
# code, so a type inferred wrong is a refusal, never a rule that lies. A method's last expression is its result, a
# field read before it is set is nil, and only nil and false are false.
#
#   ruby core/rb/reader.rb '{"root": <dir>, "file": <file>, "names": ["Mod::Class"], "clocks": ["clock"]}'
require 'json'
require 'prism'

class Reader
  ARITH = %i[+ - * / %].freeze
  CMP = {:< => '<', :<= => '<=', :> => '>', :>= => '>=', :== => '==', :!= => '!='}.freeze

  def initialize(req)
    @root, @file, @clocks = File.expand_path(req['root']), File.expand_path(req['file']), req['clocks'] || []
    @base = File.basename(@file)
    @consts = {}
    Dir.glob(File.join(@root, '**', '*.rb')).each { |f| index_consts(f) rescue nil }
    @recs, @funcs, @loads = {}, {}, []
  end

  # --- constants of the code: Mod::NAME = literal, from every file under the root -----------------------------------
  def index_consts(f)
    walk = lambda do |n, nest|
      case n
      when Prism::ModuleNode, Prism::ClassNode then n.body&.body&.each { |m| walk.(m, nest + [n.constant_path.slice]) }
      when Prism::ConstantWriteNode
        v = n.value
        lit = case v
              when Prism::SymbolNode then {'e' => 'str', 'v' => v.unescaped, 'sym' => true}
              when Prism::IntegerNode then {'e' => 'int', 'v' => v.value.to_s}
              when Prism::StringNode then {'e' => 'str', 'v' => v.unescaped}
              when Prism::TrueNode, Prism::FalseNode then {'e' => 'bool', 'v' => v.is_a?(Prism::TrueNode)}
              end
        @consts[(nest + [n.name.to_s]).join('::')] = lit.merge('file' => f) if lit
      end
    end
    Prism.parse_file(f).value.statements.body.each { |n| walk.(n, []) }
  end
  # A constant's literal, and the file defining it kept (the check loads it before the file read).
  def const(n, nest)
    full = n.slice.sub(/\A::/, '')
    c = nest.length.downto(0).lazy.map { |i| @consts[(nest[0, i] + [full]).join('::')] }.find(&:itself) || @consts.find { |k, _| k.end_with?("::#{full}") }&.last
    (@loads << c['file'] unless @loads.include?(c['file']) || c['file'] == @file) if c
    c
  end
  attr_reader :loads

  def where(n) = "#{@base}:#{n.location.start_line}:#{n.location.start_column + 1}"
  def text(n) = (s = n.slice.split.join(' ')).length <= 60 ? s : "#{s[0, 57]}..."
  def no(n, why) = {'e' => 'no', 'why' => why, 'p' => where(n)}

  # --- the classes --------------------------------------------------------------------------------------------------
  def classes
    out = {}
    walk = lambda do |n, nest|
      case n
      when Prism::ModuleNode then n.body&.body&.each { |m| walk.(m, nest + [n.constant_path.slice]) }
      when Prism::ClassNode
        q = (nest + [n.constant_path.slice]).join('::')
        out[q] = [n, nest + [n.constant_path.slice]]
        n.body&.body&.each { |m| walk.(m, nest + [n.constant_path.slice]) }
      end
    end
    Prism.parse_file(@file).value.statements.body.each { |n| walk.(n, []) }
    out
  end

  def rec_of(q, cdef, nest)
    @nest, @cls = nest, q
    defs, attrs = {}, {}
    (cdef.body&.body || []).each do |n|
      n = n.arguments.arguments.first if n.is_a?(Prism::CallNode) && %i[private protected public].include?(n.name) && n.arguments&.arguments&.first.is_a?(Prism::DefNode)
      if n.is_a?(Prism::DefNode) && !n.receiver then defs[n.name.to_s] = n
      elsif n.is_a?(Prism::CallNode) && !n.receiver && %i[attr_reader attr_writer attr_accessor].include?(n.name)
        (n.arguments&.arguments || []).each { |a| attrs[a.unescaped] = [n.name, n] if a.is_a?(Prism::SymbolNode) }
      end
    end
    @defs, @attrs = defs, attrs
    # Every field the class assigns, and what each is: the state's types (a field read before it is set is nil).
    @ivars, @lvars = {}, {}
    each_node(cdef) do |n|
      case n
      when Prism::LocalVariableWriteNode then (@lvars[n.name.to_s] ||= []) << n.value
      when Prism::InstanceVariableWriteNode then (@ivars[n.name.to_s] ||= []) << n.value
      when Prism::InstanceVariableOperatorWriteNode, Prism::InstanceVariableOrWriteNode then (@ivars[n.name.to_s] ||= []) << :int
      when Prism::CallNode
        w = n.name.to_s.chomp('=')
        if n.name.to_s.end_with?('=') && n.receiver.is_a?(Prism::SelfNode) && attrs[w] && n.arguments then (@ivars["@#{w}"] ||= []) << n.arguments.arguments.first end
        # (a field computed with or ordered against: a number)
        if (ARITH.include?(n.name) || %i[< <= > >=].include?(n.name)) && n.receiver && n.arguments&.arguments&.length == 1
          [n.receiver, n.arguments.arguments.first].each { |x| iv = field_read(x); (@ivars[iv] ||= []) << :int if iv }
        end
      end
    end
    fields = @ivars.map { |iv, _| {'name' => iv, 't' => ivar_type(iv)} }
    methods, z = {}, "#{@base}:0:0"
    attrs.each do |name, (kind, node)|
      if kind != :attr_writer && !defs[name]
        fid = "#{q}##{name}"; methods[name] = fid
        @funcs[fid] = fn_of(fid, name, node, [], [{'s' => 'ret', 'p' => z, 'x' => ivar("@#{name}", node)}])
      end
      next if kind == :attr_reader || defs["#{name}="]
      fid = "#{q}##{name}="; methods["#{name}="] = fid
      @funcs[fid] = fn_of(fid, "#{name}=", node, [{'name' => 'v', 't' => {'k' => 'any'}}], [{'s' => 'set', 'p' => z, 'to' => ivar("@#{name}", node), 'x' => {'e' => 'var', 'n' => 'v', 'p' => where(node)}}, {'s' => 'ret', 'p' => z, 'x' => {'e' => 'var', 'n' => 'v', 'p' => where(node)}}])
    end
    defs.each do |name, d|
      key = name == 'initialize' ? '__init__' : name
      fid = "#{q}##{name}"; methods[key] = fid
      @funcs[fid] = func(fid, d, name == 'initialize' ? fields.map { |f| f['name'] } : nil)
    end
    # (no initialize: every field nil, as Ruby's are)
    unless defs['initialize'] || fields.empty?
      fid = "#{q}#initialize"; methods['__init__'] = fid
      @funcs[fid] = fn_of(fid, 'initialize', cdef, [], fields.map { |f| {'s' => 'set', 'p' => z, 'to' => ivar(f['name'], cdef), 'x' => {'e' => 'none', 'p' => where(cdef)}} })
    end
    @recs[q] = {'name' => q, 'short' => q.split('::').last, 'fields' => fields, 'methods' => methods, 'kinds' => [], 'own' => true, 'module' => q, 'p' => where(cdef)}
    q
  end
  # The field an expression reads: @x, or x / self.x of an attribute reader.
  def field_read(x)
    return x.name.to_s if x.is_a?(Prism::InstanceVariableReadNode)
    "@#{x.name}" if x.is_a?(Prism::CallNode) && (!x.receiver || x.receiver.is_a?(Prism::SelfNode)) && !x.arguments && @attrs[x.name.to_s] && @attrs[x.name.to_s][0] != :attr_writer
  end
  def each_node(n, &b)
    yield n
    n.compact_child_nodes.each { |c| each_node(c, &b) }
  end

  # --- types, inferred ----------------------------------------------------------------------------------------------
  def kind(v, locals = {})
    return 'int' if v == :int
    case v
    when Prism::NilNode then 'none'
    when Prism::IntegerNode then 'int'
    when Prism::FloatNode then 'float'
    when Prism::TrueNode, Prism::FalseNode then 'bool'
    when Prism::StringNode, Prism::InterpolatedStringNode then 'str'
    when Prism::SymbolNode then [:sym, v.unescaped]
    when Prism::ConstantReadNode, Prism::ConstantPathNode
      c = const(v, @nest)
      c && (c['sym'] ? [:sym, c['v']] : c['e'] == 'int' ? 'int' : c['e'] == 'bool' ? 'bool' : 'str')
    when Prism::LocalVariableReadNode
      # (a local: what the class assigns to one of its name)
      locals[v.name.to_s] || (locals.key?(:seen) ? nil : (@lvars[v.name.to_s] || []).map { |w| kind(w, {seen: true}) }.compact.uniq.then { |ks| ks.length == 1 ? ks[0] : nil })
    when Prism::InstanceVariableReadNode
      # (another field: what the class assigns to it)
      locals.key?(:fields) ? nil : (@ivars[v.name.to_s] || []).map { |w| kind(w, {fields: true}) }.compact.reject { |k| k == 'none' }.uniq.then { |ks| ks.length == 1 ? ks[0] : nil }
    when Prism::ParenthesesNode then kind(v.body&.body&.last, locals)
    when Prism::IfNode then [kind(v.statements&.body&.last, locals), kind(else_of(v), locals)]
    when Prism::CallNode
      return 'int' if clock?(v) || (ARITH.include?(v.name) && v.receiver) || %i[min max abs to_i size length count].include?(v.name)
      return 'bool' if CMP.key?(v.name) || v.name.to_s.end_with?('?')
      nil
    end
  end
  def else_of(n)
    e = n.respond_to?(:subsequent) ? n.subsequent : n.consequent
    e.is_a?(Prism::ElseNode) ? e.statements&.body&.last : e
  end
  # The kinds a field is given: symbols a choice, nil an option, the others one scalar type (or none known).
  def ivar_type(iv)
    ks = (@ivars[iv] || []).flat_map { |v| k = kind(v, {}); k.is_a?(Array) && k[0] != :sym ? k : [k] }.compact
    syms = ks.select { |k| k.is_a?(Array) }.map(&:last).uniq
    rest = ks.reject { |k| k.is_a?(Array) }.uniq
    none = rest.delete('none')
    t = if syms.any? && rest.empty? then {'k' => 'choice', 'values' => syms, 'sym' => true}
        elsif syms.empty? && rest.length == 1 then {'k' => rest[0]}
        elsif syms.empty? && rest.sort == %w[float int] then {'k' => 'float'}
        end
    return {'k' => 'any'} unless t
    none ? {'k' => 'opt', 'of' => t} : t
  end
  # An argument's type: what the method compares it with, computes it into, or its default.
  def param_type(d, name, dflt)
    syms, ints = [], false
    each_node(d) do |n|
      if n.is_a?(Prism::CaseNode) && n.predicate.is_a?(Prism::LocalVariableReadNode) && n.predicate.name.to_s == name
        n.conditions.each { |w| w.conditions.each { |c| k = kind(c); syms << k[1] if k.is_a?(Array) } }
      elsif n.is_a?(Prism::CallNode) && n.receiver && n.arguments&.arguments&.length == 1
        a, b = n.receiver, n.arguments.arguments.first
        [[a, b], [b, a]].each do |x, y|
          next unless x.is_a?(Prism::LocalVariableReadNode) && x.name.to_s == name
          k = kind(y)
          if k.is_a?(Array) && %i[== !=].include?(n.name) then syms << k[1]
          elsif ARITH.include?(n.name) || CMP.key?(n.name) then ints = true
          end
        end
      end
    end
    return {'k' => 'choice', 'values' => syms.uniq, 'sym' => true} if syms.any?
    k = dflt && kind(dflt)
    return {'k' => k} if %w[int float bool str].include?(k)
    return {'k' => 'int'} if ints
    # (one the method keeps in a field: the field's type)
    each_node(d) { |n| return ivar_type(n.name.to_s) if n.is_a?(Prism::InstanceVariableWriteNode) && n.value.is_a?(Prism::LocalVariableReadNode) && n.value.name.to_s == name }
    {'k' => 'any'}
  end

  # --- methods ------------------------------------------------------------------------------------------------------
  def fn_of(fid, name, node, params, body)
    {'id' => fid, 'name' => name, 'cls' => @cls, 'p' => where(node), 'span' => [@base, node.location.start_line, node.location.end_line],
     'params' => [{'name' => 'self', 't' => {'k' => 'any'}, 'self' => true}, *params], 'ret' => {'k' => 'any'}, 'body' => body, 'decorators' => []}
  end
  def func(fid, d, nil_fields)
    params, ps = [], d.parameters
    if ps
      ps.requireds.each { |x| params << {'name' => x.name.to_s, 't' => param_type(d, x.name.to_s, nil)} }
      ps.optionals.each { |x| params << {'name' => x.name.to_s, 't' => param_type(d, x.name.to_s, x.value), 'dflt' => expr(x.value)} }
      ps.keywords.each do |x|
        dflt = x.respond_to?(:value) ? x.value : nil
        clock = @clocks.include?(x.name.to_s)
        params << {'name' => x.name.to_s, 't' => clock ? {'k' => 'opaque', 'why' => "#{x.name}, the clock (stated)"} : param_type(d, x.name.to_s, dflt), 'kw' => true,
                   **(clock ? {'dflt' => {'e' => 'opaque', 'why' => "#{x.name}, the clock (stated): read as the request's time", 'p' => where(x)}} : dflt ? {'dflt' => expr(dflt)} : {})}
      end
      params << {'name' => '*', 't' => {'k' => 'opaque', 'why' => '*args'}, 'star' => 1} if ps.rest
      params << {'name' => '**', 't' => {'k' => 'opaque', 'why' => '**kwargs'}, 'star' => 2} if ps.keyword_rest
    end
    stmts = d.body.is_a?(Prism::StatementsNode) ? d.body.body : d.body ? [d.body] : []
    # (a constructor: every field nil until it is set, as Ruby's are)
    # (synthesized statements are at line 0: no line of the code to count)
    pre = (nil_fields || []).map { |f| {'s' => 'set', 'p' => "#{@base}:0:0", 'to' => ivar(f, d), 'x' => {'e' => 'none', 'p' => where(d)}} }
    fn_of(fid, d.name.to_s, d, params, pre + block(stmts, !nil_fields))
  end

  # --- statements: the last one's value is the method's (or the branch's) result -------------------------------------
  def block(ss, tail)
    ss.each_with_index.flat_map { |s, i| stmt(s, tail && i == ss.length - 1) }.then { |out| tail && ss.empty? ? [{'s' => 'ret', 'p' => "#{@base}:0:0"}] : out }
  end
  def body_of(n) = n.is_a?(Prism::StatementsNode) ? n.body : n.is_a?(Prism::ElseNode) ? (n.statements&.body || []) : n ? [n] : []
  def stmt(s, tail)
    p = where(s)
    ret = ->(x) { tail ? [{'s' => 'ret', 'p' => p, 'x' => x}] : [{'s' => 'expr', 'p' => p, 'x' => x}] }
    case s
    when Prism::IfNode, Prism::UnlessNode
      th = block(body_of(s.statements), tail)
      el = block(body_of(s.is_a?(Prism::IfNode) ? (s.respond_to?(:subsequent) ? s.subsequent : s.consequent) : s.else_clause), tail)
      c = expr(s.predicate)
      [{'s' => 'if', 'p' => p, 'c' => s.is_a?(Prism::UnlessNode) ? {'e' => 'not', 'x' => c, 'p' => p} : c, 'then' => th, 'else' => el}]
    when Prism::CaseNode
      return [{'s' => 'no', 'p' => p, 'why' => 'case without a value'}] unless s.predicate
      subj = expr(s.predicate)
      s.conditions.reverse.reduce(block(body_of(s.else_clause), tail)) do |rest, w|
        c = {'e' => 'or', 'xs' => w.conditions.map { |x| {'e' => 'cmp', 'op' => '==', 'x' => subj, 'y' => expr(x), 'p' => where(x), 'text' => text(x)} }, 'p' => where(w)}
        # (at line 0: Ruby counts no line at a when)
        [{'s' => 'if', 'p' => "#{@base}:0:0", 'c' => c, 'then' => block(body_of(w.statements), tail), 'else' => rest}]
      end
    when Prism::ReturnNode
      a = s.arguments&.arguments || []
      [{'s' => 'ret', 'p' => p, **(a.length == 1 ? {'x' => expr(a[0])} : a.empty? ? {} : {'x' => no(s, 'a return of several values')})}]
    when Prism::LocalVariableWriteNode then [{'s' => 'set', 'p' => p, 'to' => {'e' => 'var', 'n' => s.name.to_s, 'p' => p}, 'x' => expr(s.value)}, *(tail ? ret.({'e' => 'var', 'n' => s.name.to_s, 'p' => p}) : [])]
    when Prism::InstanceVariableWriteNode then [{'s' => 'set', 'p' => p, 'to' => ivar(s.name.to_s, s), 'x' => expr(s.value)}, *(tail ? ret.(ivar(s.name.to_s, s)) : [])]
    when Prism::InstanceVariableOperatorWriteNode, Prism::LocalVariableOperatorWriteNode
      t = s.is_a?(Prism::LocalVariableOperatorWriteNode) ? {'e' => 'var', 'n' => s.name.to_s, 'p' => p} : ivar(s.name.to_s, s)
      op = s.respond_to?(:binary_operator) ? s.binary_operator : s.operator
      [{'s' => 'set', 'p' => p, 'to' => t, 'x' => binop(op, t, expr(s.value), s)}, *(tail ? ret.(t) : [])]
    when Prism::CallNode
      if s.name == :raise && !s.receiver then return [{'s' => 'fail', 'p' => p, 'why' => "raise #{text(s.arguments || s)}".sub(/raise raise/, 'raise')}] end
      if s.name == :synchronize && s.block.is_a?(Prism::BlockNode) && s.receiver
        return [{'s' => 'with', 'p' => p, 'items' => [{'x' => expr(s.receiver)}], 'body' => block(body_of(s.block.body), tail)}]
      end
      ret.(expr(s))
    when Prism::ParenthesesNode then block(body_of(s.body), tail)
    when Prism::WhileNode, Prism::UntilNode, Prism::ForNode then [{'s' => 'no', 'p' => p, 'why' => 'a loop'}]
    when Prism::BeginNode then [{'s' => 'no', 'p' => p, 'why' => 'begin/rescue (an exception caught: the subset reads one only as the step\'s failure)'}]
    when Prism::DefNode, Prism::ClassNode, Prism::ModuleNode then [{'s' => 'no', 'p' => p, 'why' => 'a definition inside a method'}]
    else ret.(expr(s))
    end
  end
  def ivar(name, n) = {'e' => 'get', 'x' => {'e' => 'var', 'n' => 'self', 'p' => where(n)}, 'f' => name, 'p' => where(n), 'text' => name}
  def binop(op, a, b, n)
    o = {:+ => '+', :- => '-', :* => '*', :/ => '//', :% => '%'}[op.to_sym]
    return no(n, "#{text(n)}: #{op} (outside the subset)") unless o
    return no(n, "#{text(n)}: a float division (the subset reads whole numbers)") if o == '//' && (a['float'] || b['float'])
    {'e' => 'bin', 'op' => o, 'x' => a, 'y' => b, 'p' => where(n), 'text' => text(n)}
  end
  def clock?(n)
    return false unless n.is_a?(Prism::CallNode)
    r = n.receiver
    (%i[current_time now].include?(n.name) && r && @clocks.include?(r.slice.delete_prefix('@').delete_prefix('self.'))) ||
      (%i[to_i to_f].include?(n.name) && r.is_a?(Prism::CallNode) && r.name == :now && r.receiver&.slice == 'Time') ||
      (n.name == :clock_gettime && r&.slice == 'Process')
  end

  # --- expressions --------------------------------------------------------------------------------------------------
  def call(f, args, n) = {'e' => 'call', 'f' => f, 'args' => args, 'kw' => [], 'p' => where(n), 'text' => text(n)}
  def self_call(name, args, n) = call({'e' => 'get', 'x' => {'e' => 'var', 'n' => 'self', 'p' => where(n)}, 'f' => name, 'p' => where(n), 'text' => name}, args, n)
  def expr(x)
    p = where(x)
    case x
    when Prism::IntegerNode then {'e' => 'int', 'v' => x.value.to_s, 'p' => p}
    when Prism::FloatNode then x.value == x.value.floor && x.value.abs < 2**53 ? {'e' => 'int', 'v' => x.value.to_i.to_s, 'float' => true, 'p' => p} : no(x, "#{text(x)}: a float that isn't whole (a binary fraction)")
    when Prism::StringNode then {'e' => 'str', 'v' => x.unescaped, 'p' => p}
    when Prism::SymbolNode then {'e' => 'str', 'v' => x.unescaped, 'p' => p}
    when Prism::TrueNode, Prism::FalseNode then {'e' => 'bool', 'v' => x.is_a?(Prism::TrueNode), 'p' => p}
    when Prism::NilNode then {'e' => 'none', 'p' => p}
    when Prism::SelfNode then {'e' => 'var', 'n' => 'self', 'p' => p}
    when Prism::LocalVariableReadNode then {'e' => 'var', 'n' => x.name.to_s, 'p' => p}
    when Prism::InstanceVariableReadNode then ivar(x.name.to_s, x)
    when Prism::ConstantReadNode, Prism::ConstantPathNode then (c = const(x, @nest)) ? c.reject { |k, _| %w[sym file].include?(k) }.merge('p' => p) : no(x, "#{text(x)}: a constant the reader can't resolve to a literal")
    when Prism::ParenthesesNode then (b = body_of(x.body)).length == 1 ? expr(b[0]) : no(x, "#{text(x)}: several statements as a value")
    when Prism::AndNode, Prism::OrNode then {'e' => x.is_a?(Prism::AndNode) ? 'and' : 'or', 'xs' => [expr(x.left), expr(x.right)], 'p' => p}
    when Prism::IfNode
      el = else_of(x)
      return no(x, "#{text(x)}: an if of several statements as a value") if (x.statements&.body || []).length > 1
      {'e' => 'ite', 'c' => expr(x.predicate), 'a' => x.statements ? expr(x.statements.body.last) : {'e' => 'none', 'p' => p}, 'b' => el ? expr(el) : {'e' => 'none', 'p' => p}, 'p' => p}
    when Prism::InterpolatedStringNode
      {'e' => 'fstr', 'parts' => x.parts.map { |q| q.is_a?(Prism::StringNode) ? q.unescaped : {'x' => q.statements&.body&.length == 1 ? expr(q.statements.body[0]) : no(q, 'an interpolation'), 'plain' => true} }, 'p' => p, 'text' => text(x)}
    when Prism::CallNode then call_expr(x)
    else no(x, "#{text(x)}: #{x.type} (outside the subset)")
    end
  end
  def call_expr(x)
    p, r, n, args = where(x), x.receiver, x.name, x.arguments&.arguments || []
    return no(x, "#{text(x)}: a block (a closure)") if x.block.is_a?(Prism::BlockNode)
    return no(x, "#{text(x)}: &. (a call on a value that may be nil)") if x.safe_navigation?
    return {'e' => 'call', 'f' => {'e' => 'lib', 'q' => 'time.time', 'p' => p}, 'args' => [], 'kw' => [], 'p' => p, 'text' => text(x)} if clock?(x)
    return self_call(n.to_s, args.map { |a| expr(a) }, x) if !r || r.is_a?(Prism::SelfNode)
    rv = r.is_a?(Prism::ArrayNode) ? nil : expr(r)
    return binop(n, rv, expr(args[0]), x) if ARITH.include?(n) && args.length == 1
    return {'e' => 'cmp', 'op' => CMP[n], 'x' => rv, 'y' => expr(args[0]), 'p' => p, 'text' => text(x)} if CMP.key?(n) && args.length == 1
    case n
    when :! then {'e' => 'not', 'x' => rv, 'p' => p}
    when :-@ then {'e' => 'neg', 'x' => rv, 'p' => p}
    when :nil? then {'e' => 'cmp', 'op' => 'is', 'x' => rv, 'y' => {'e' => 'none', 'p' => p}, 'p' => p, 'text' => text(x)}
    when :zero?, :positive?, :negative?
      {'e' => 'cmp', 'op' => {zero?: '==', positive?: '>', negative?: '<'}[n], 'x' => rv, 'y' => {'e' => 'int', 'v' => '0', 'p' => p}, 'p' => p, 'text' => text(x)}
    when :abs then call({'e' => 'builtin', 'n' => 'abs', 'p' => p}, [rv], x)
    when :to_i, :to_f, :to_int then call({'e' => 'builtin', 'n' => 'int', 'p' => p}, [rv], x)
    when :min, :max
      return call({'e' => 'builtin', 'n' => n.to_s, 'p' => p}, r.elements.map { |e| expr(e) }, x) if r.is_a?(Prism::ArrayNode) && args.empty?
      no(x, "#{text(x)}: #{n} of a collection")
    when :clamp
      return no(x, "#{text(x)}: clamp of a range") unless args.length == 2
      call({'e' => 'builtin', 'n' => 'max', 'p' => p}, [expr(args[0]), call({'e' => 'builtin', 'n' => 'min', 'p' => p}, [rv, expr(args[1])], x)], x)
    when :new
      return {'e' => 'call', 'f' => {'e' => 'lib', 'q' => 'threading.Lock', 'p' => p}, 'args' => [], 'kw' => [], 'p' => p, 'text' => text(x)} if r.slice =~ /\A(::)?(Thread::)?(Mutex|Monitor)\z/
      no(x, "#{text(x)}: an object of another class made")
    else
      return no(x, "#{text(x)}: a method of an array") if r.is_a?(Prism::ArrayNode)
      return no(x, "#{text(x)}: #{r.slice}, another class's code") if r.is_a?(Prism::ConstantReadNode) || r.is_a?(Prism::ConstantPathNode)
      call({'e' => 'get', 'x' => rv, 'f' => n.to_s, 'p' => p, 'text' => text(x)}, args.map { |a| expr(a) }, x)
    end
  end
end

req = JSON.parse(ARGV[0])
r = Reader.new(req)
cls = r.classes
out = {'lang' => 'ruby', 'file' => File.basename(req['file']), 'path' => File.expand_path(req['file']), 'module' => File.basename(req['file'], '.rb'),
       'root' => File.expand_path(req['root']), 'truth' => 'nil-false', 'entries' => []}
req['names'].each do |n|
  key = cls.key?(n) ? n : cls.keys.find { |k| k.end_with?("::#{n}") }
  out['entries'] << (key ? {'k' => 'class', 'rec' => r.rec_of(key, *cls[key])} : {'k' => 'missing', 'name' => n})
end
out['recs'] = r.instance_variable_get(:@recs)
out['funcs'] = r.instance_variable_get(:@funcs)
out['loads'] = r.loads
puts JSON.generate(out)
