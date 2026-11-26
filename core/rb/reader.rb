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
    @consts, @defined, @mods = {}, [], {}
    # (open: a constant may come from what the code requires, a gem's, or a Gemfile's bundle, or be made as it runs)
    @open = %w[Gemfile gems.rb].any? { |g| File.exist?(File.join(@root, g)) } || !Dir.glob(File.join(@root, '*.gemspec')).empty?
    ([@file] | Dir.glob(File.join(@root, '**', '*.rb'))).each { |f| index_consts(f) rescue nil }
    @recs, @funcs, @loads = {}, {}, []
    @caught = []
    @pre, @tmp = nil, 0
    @schema = load_schema
  end

  # ActiveRecord schema.rb columns (if db/schema.rb exists under @root or its ancestors up to 3 levels).
  def load_schema
    tables = {}
    dir = @root
    paths = []
    4.times do
      paths.concat(Dir.glob(File.join(dir, 'db', 'schema.rb')))
      paths.concat(Dir.glob(File.join(dir, '*', 'db', 'schema.rb')))
      parent = File.dirname(dir)
      break if parent == dir
      dir = parent
    end
    paths.uniq.each do |sf|
      tree = Prism.parse_file(sf).value rescue next
      each_node(tree) do |n|
        next unless n.is_a?(Prism::CallNode) && n.name == :create_table && n.block.is_a?(Prism::BlockNode)
        tname = str_or_sym(n.arguments&.arguments&.first)
        next unless tname
        cols = (tables[tname] ||= {})
        each_node(n.block) do |c|
          next unless c.is_a?(Prism::CallNode) && c.receiver && (cname = str_or_sym(c.arguments&.arguments&.first))
          t = ar_col_type(c.name.to_s)
          next unless t
          kw = kw_hash(c.arguments&.arguments)
          nullable = !(kw['null'].is_a?(Prism::FalseNode)) && !kw.key?('default')
          cols[cname] = {'t' => nullable ? {'k' => 'opt', 'of' => t} : t, 'dflt' => kw['default'], 'bool' => t['k'] == 'bool'}
        end
      end
    end
    tables
  end
  def str_or_sym(n)
    return n.unescaped if n.is_a?(Prism::StringNode) || n.is_a?(Prism::SymbolNode)
    nil
  end
  def kw_hash(args)
    out = {}
    (args || []).each do |a|
      next unless a.is_a?(Prism::KeywordHashNode) || a.is_a?(Prism::HashNode)
      a.elements.each do |el|
        next unless el.is_a?(Prism::AssocNode)
        k = str_or_sym(el.key)
        out[k] = el.value if k
      end
    end
    out
  end
  def ar_col_type(name)
    case name
    when 'integer', 'bigint', 'int' then {'k' => 'int'}
    when 'float', 'decimal' then {'k' => 'float'}
    when 'boolean', 'bool' then {'k' => 'bool'}
    when 'string', 'text' then {'k' => 'str'}
    end
  end
  def table_candidates(q)
    snake = ->(s) { s.gsub(/([A-Z]+)([A-Z][a-z])/, '\1_\2').gsub(/([a-z\d])([A-Z])/, '\1_\2').downcase }
    plural = ->(s) { s.end_with?('y') && !s.end_with?('ay', 'ey', 'iy', 'oy', 'uy') ? "#{s[0..-2]}ies" : s.end_with?('s', 'x', 'z', 'ch', 'sh') ? "#{s}es" : "#{s}s" }
    parts = q.split('::').map(&snake)
    short = parts.last
    [plural.(parts.join('_')), plural.(short), parts.join('_'), short].uniq
  end
  AR_MACROS = %i[attribute enum belongs_to has_one has_many validates validate alias_attribute scope before_save after_save before_validation after_create before_create].freeze
  def ar_model?(cdef)
    sup = cdef.superclass&.slice
    return true if sup && sup =~ /\A(::)?(ActiveRecord::Base|ApplicationRecord|.*::Base|.*::ApplicationRecord)\z/
    (cdef.body&.body || []).any? { |n| n.is_a?(Prism::CallNode) && !n.receiver && AR_MACROS.include?(n.name) }
  end

  # --- constants of the code: Mod::NAME = literal, from every file under the root -----------------------------------
  def index_consts(f)
    walk = lambda do |n, nest|
      case n
      when Prism::ModuleNode, Prism::ClassNode
        q = (nest + [n.constant_path.slice]).join('::')
        @defined << q
        # (its singleton methods and the names each one's body calls on it; open where its body may add others)
        md = (@mods[q] ||= {defs: {}, open: false, cls: n.is_a?(Prism::ClassNode)})
        md[:open] = true if n.is_a?(Prism::ClassNode) && n.superclass
        (n.body&.body || []).each do |m|
          if m.is_a?(Prism::DefNode) && m.receiver.is_a?(Prism::SelfNode)
            calls = []
            each_node(m) { |c| calls << c.name.to_s if c.is_a?(Prism::CallNode) && !c.receiver }
            md[:defs][m.name.to_s] = calls
          elsif m.is_a?(Prism::SingletonClassNode) || (m.is_a?(Prism::CallNode) && !%i[attr_reader attr_writer attr_accessor private public protected].include?(m.name))
            md[:open] = true
          end
        end
        n.body&.body&.each { |m| walk.(m, nest + [n.constant_path.slice]) }
      when Prism::ConstantPathWriteNode then @defined << (nest + [n.target.slice]).join('::')
      when Prism::ConstantWriteNode
        @defined << (nest + [n.name.to_s]).join('::')
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
    tree = Prism.parse_file(f).value
    tree.statements.body.each { |n| walk.(n, []) }
    each_node(tree) { |n| @open = true if !@open && n.is_a?(Prism::CallNode) && %i[require load autoload const_set const_missing eval instance_eval class_eval module_eval].include?(n.name) }
  end
  # Why Mod.m fails where it runs, a module or class under the root whose singleton methods the reader sees all of: no
  # such method, or its body calls a name nothing defines; else nil.
  def no_method(r, n, nest)
    return nil if @open
    full = r.slice.sub(/\A::/, '')
    q = nest.length.downto(0).map { |i| (nest[0, i] + [full]).join('::') }.find { |k| @mods.key?(k) }
    md = q && @mods[q]
    return nil if !md || md[:open]
    known = ->(m) { md[:defs].key?(m) || (md[:cls] ? Class.new : Module.new).respond_to?(m, true) }
    return "#{full} defines no #{n} (a NoMethodError where it runs)" unless known.(n.to_s)
    gone = md[:defs][n.to_s].reject { |m| known.(m) }
    gone.empty? ? nil : "#{full}.#{n} calls #{gone.first}, which nothing defines (a NameError where it runs)"
  end
  # Whether a constant is defined: under the root (a class, a module, a constant), by Ruby itself, or maybe by what the
  # code requires.
  def defined_const?(n, nest)
    full = n.slice.sub(/\A::/, '')
    @open || nest.length.downto(0).any? { |i| @defined.include?((nest[0, i] + [full]).join('::')) } || @defined.any? { |k| k.end_with?("::#{full}") } ||
      (Object.const_defined?(full) rescue true)
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
  # The locals a node mentions, and self where it reads the object's state.
  def mentioned(ns)
    out, q = [], ns.dup
    while (m = q.shift)
      out << m.name.to_s if m.is_a?(Prism::LocalVariableReadNode)
      out << 'self' if m.is_a?(Prism::InstanceVariableReadNode) || m.is_a?(Prism::SelfNode)
      q.concat(m.compact_child_nodes)
    end
    out.uniq
  end

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
    @ar = ar_model?(cdef)
    @ar_cols, @ar_assocs, @ar_aliases = {}, [], {}
    if @ar
      # 1) Schema columns matching this model's table name.
      table_candidates(q).each do |tn|
        if (sc = @schema[tn])
          sc.each { |cn, info| @ar_cols[cn] = info.dup }
          break
        end
      end
      # 2) Class-body ActiveRecord declarations: attribute, enum, alias_attribute, validates, associations, where(...).
      (cdef.body&.body || []).each do |n|
        next unless n.is_a?(Prism::CallNode) && !n.receiver
        as = n.arguments&.arguments || []
        case n.name
        when :belongs_to, :has_one, :has_many
          a0 = str_or_sym(as[0])
          @ar_assocs << a0 if a0
        when :attribute
          cn = str_or_sym(as[0])
          t = ar_col_type(str_or_sym(as[1]).to_s)
          if cn && t
            kw = kw_hash(as)
            @ar_cols[cn] = {'t' => t, 'dflt' => kw['default'], 'bool' => t['k'] == 'bool'}
          end
        when :enum
          if (cn = str_or_sym(as[0])) && as[1]
            vals = if as[1].is_a?(Prism::HashNode) || as[1].is_a?(Prism::KeywordHashNode)
                     as[1].elements.filter_map { |el| str_or_sym(el.key) if el.is_a?(Prism::AssocNode) }
                   elsif as[1].is_a?(Prism::ArrayNode)
                     as[1].elements.filter_map { |el| str_or_sym(el) }
                   end
            @ar_cols[cn] = {'t' => {'k' => 'choice', 'values' => vals}, 'bool' => false} if vals&.any?
          elsif as[0].is_a?(Prism::KeywordHashNode) || as[0].is_a?(Prism::HashNode)
            as[0].elements.each do |el|
              next unless el.is_a?(Prism::AssocNode) && (cn = str_or_sym(el.key))
              vals = if el.value.is_a?(Prism::HashNode) || el.value.is_a?(Prism::KeywordHashNode)
                       el.value.elements.filter_map { |e2| str_or_sym(e2.key) if e2.is_a?(Prism::AssocNode) }
                     elsif el.value.is_a?(Prism::ArrayNode)
                       el.value.elements.filter_map { |e2| str_or_sym(e2) }
                     end
              @ar_cols[cn] = {'t' => {'k' => 'choice', 'values' => vals}, 'bool' => false} if vals&.any?
            end
          end
        when :alias_attribute
          a0, a1 = str_or_sym(as[0]), str_or_sym(as[1])
          @ar_aliases[a0] = a1 if a0 && a1
        when :validates
          kw = kw_hash(as)
          as.each do |a|
            cn = str_or_sym(a)
            next unless cn && !@ar_assocs.include?(cn)
            @ar_cols[cn] ||= {'t' => nil, 'inferred' => []}
            if kw.key?('numericality')
              (@ar_cols[cn]['inferred'] ||= []) << :int
            elsif kw.key?('inclusion') && kw['inclusion'].slice =~ /true.*false|false.*true/
              @ar_cols[cn]['t'] ||= {'k' => 'bool'}
              @ar_cols[cn]['bool'] = true
            end
          end
        end
      end
      # 3) ActiveRecord write_attribute/read_attribute/self[:col]/self.col= inside instance methods, and scalar where(col: lit) in scopes.
      defs.each_value do |d|
        each_node(d) do |n|
          next unless n.is_a?(Prism::CallNode)
          as = n.arguments&.arguments || []
          if (!n.receiver || n.receiver.is_a?(Prism::SelfNode)) && n.name == :write_attribute && as.length >= 2 && (cn = str_or_sym(as[0]))
            @ar_cols[cn] ||= {'t' => nil, 'inferred' => []}
            (@ar_cols[cn]['inferred'] ||= []) << as[1]
          elsif (!n.receiver || n.receiver.is_a?(Prism::SelfNode)) && n.name == :read_attribute && as.length >= 1 && (cn = str_or_sym(as[0]))
            @ar_cols[cn] ||= {'t' => nil, 'inferred' => []}
          elsif n.receiver.is_a?(Prism::SelfNode) && n.name == :[]= && as.length == 2 && (cn = str_or_sym(as[0]))
            @ar_cols[cn] ||= {'t' => nil, 'inferred' => []}
            (@ar_cols[cn]['inferred'] ||= []) << as[1]
          elsif n.receiver.is_a?(Prism::SelfNode) && n.name == :[] && as.length == 1 && (cn = str_or_sym(as[0]))
            @ar_cols[cn] ||= {'t' => nil, 'inferred' => []}
          elsif n.receiver.is_a?(Prism::SelfNode) && n.name.to_s.end_with?('=') && as.length == 1
            cn = n.name.to_s.chomp('=')
            unless attrs[cn] || @ar_assocs.include?(cn) || @ar_aliases.key?(cn) || cn.empty? || %w[== != <= >= ===].include?(n.name.to_s)
              @ar_cols[cn] ||= {'t' => nil, 'inferred' => []}
              (@ar_cols[cn]['inferred'] ||= []) << as[0]
            end
          end
        end
      end
      (cdef.body&.body || []).each do |bn|
        next unless bn.is_a?(Prism::CallNode) && !bn.receiver && bn.name == :scope
        each_node(bn) do |n|
          next unless n.is_a?(Prism::CallNode) && n.name == :where
          as = n.arguments&.arguments || []
          next unless as.length == 1 && (as[0].is_a?(Prism::KeywordHashNode) || as[0].is_a?(Prism::HashNode))
          as[0].elements.each do |el|
            next unless el.is_a?(Prism::AssocNode) && (cn = str_or_sym(el.key)) && !@ar_assocs.include?(cn)
            next unless el.value.is_a?(Prism::TrueNode) || el.value.is_a?(Prism::FalseNode) || el.value.is_a?(Prism::IntegerNode) || el.value.is_a?(Prism::StringNode) || el.value.is_a?(Prism::SymbolNode)
            @ar_cols[cn] ||= {'t' => nil, 'inferred' => []}
            (@ar_cols[cn]['inferred'] ||= []) << el.value
          end
        end
      end
      @ar_cols.each_key do |cn|
        attrs[cn] ||= [:attr_accessor, cdef]
      end
    end
    # Every field the class assigns, and what each is: the state's types (a field read before it is set is nil).
    @ivars, @lvars = {}, {}
    @ar_cols.each do |cn, info|
      (@ivars["@#{cn}"] ||= []).concat(info['inferred'] || [])
    end
    each_node(cdef) do |n|
      case n
      when Prism::LocalVariableWriteNode, Prism::LocalVariableOrWriteNode, Prism::LocalVariableAndWriteNode then (@lvars[n.name.to_s] ||= []) << n.value
      when Prism::InstanceVariableWriteNode then (@ivars[n.name.to_s] ||= []) << n.value
      when Prism::InstanceVariableOrWriteNode, Prism::InstanceVariableAndWriteNode
        (@ivars[n.name.to_s] ||= []).push(:none, n.value)
      when Prism::InstanceVariableOperatorWriteNode then (@ivars[n.name.to_s] ||= []) << :int
      when Prism::CallNode
        w = n.name.to_s.chomp('=')
        if n.name.to_s.end_with?('=') && n.receiver.is_a?(Prism::SelfNode) && attrs[w] && n.arguments then (@ivars["@#{w}"] ||= []) << n.arguments.arguments.first end
        # (a field computed with or ordered against: a number)
        if (ARITH.include?(n.name) || %i[< <= > >=].include?(n.name)) && n.receiver && n.arguments&.arguments&.length == 1
          [n.receiver, n.arguments.arguments.first].each { |x| iv = field_read(x); (@ivars[iv] ||= []) << :int if iv }
        end
        if n.safe_navigation? && n.receiver && (iv = field_read(n.receiver))
          (@ivars[iv] ||= []) << :none
        end
      end
    end
    fields = @ivars.map do |iv, _|
      cn = iv.delete_prefix('@')
      info = @ar_cols[cn]
      t = (info && info['t']) || ivar_type(iv)
      info['bool'] = true if info && (t['k'] == 'bool' || (t['k'] == 'opt' && t['of']&.[]('k') == 'bool'))
      {'name' => iv, 't' => t}
    end
    field_types = fields.to_h { |f| [f['name'].delete_prefix('@'), f['t']] }
    methods, z = {}, "#{@base}:0:0"
    attrs.each do |name, (kind, node)|
      if kind != :attr_writer && !defs[name]
        fid = "#{q}##{name}"; methods[name] = fid
        @funcs[fid] = fn_of(fid, name, node, [], [{'s' => 'ret', 'p' => z, 'x' => ivar("@#{name}", node)}])
      end
      if @ar_cols[name]&.[]('bool') && !defs["#{name}?"]
        fid = "#{q}##{name}?"; methods["#{name}?"] = fid
        @funcs[fid] = fn_of(fid, "#{name}?", node, [], [{'s' => 'ret', 'p' => z, 'x' => {'e' => 'not', 'x' => {'e' => 'not', 'x' => ivar("@#{name}", node), 'p' => z}, 'p' => z}}])
      end
      next if kind == :attr_reader || defs["#{name}="]
      fid = "#{q}##{name}="; methods["#{name}="] = fid
      vt = @ar_cols.key?(name) ? (field_types[name] || {'k' => 'any'}) : {'k' => 'any'}
      @funcs[fid] = fn_of(fid, "#{name}=", node, [{'name' => 'v', 't' => vt}], [{'s' => 'set', 'p' => z, 'to' => ivar("@#{name}", node), 'x' => {'e' => 'var', 'n' => 'v', 'p' => where(node)}}, {'s' => 'ret', 'p' => z, 'x' => {'e' => 'var', 'n' => 'v', 'p' => where(node)}}])
    end
    @ar_aliases.each do |al, orig|
      next unless @ar_cols[orig]
      unless defs[al]
        fid = "#{q}##{al}"; methods[al] = fid
        @funcs[fid] = fn_of(fid, al, cdef, [], [{'s' => 'ret', 'p' => z, 'x' => ivar("@#{orig}", cdef)}])
      end
      unless defs["#{al}="]
        fid = "#{q}##{al}="; methods["#{al}="] = fid
        vt = field_types[orig] || {'k' => 'any'}
        @funcs[fid] = fn_of(fid, "#{al}=", cdef, [{'name' => 'v', 't' => vt}], [{'s' => 'set', 'p' => z, 'to' => ivar("@#{orig}", cdef), 'x' => {'e' => 'var', 'n' => 'v', 'p' => z}}, {'s' => 'ret', 'p' => z, 'x' => {'e' => 'var', 'n' => 'v', 'p' => z}}])
      end
    end
    defs.each do |name, d|
      key = name == 'initialize' ? '__init__' : name
      fid = "#{q}##{name}"; methods[key] = fid
      @funcs[fid] = func(fid, d, name == 'initialize' ? fields.map { |f| f['name'] } : nil)
    end
    # (no initialize: ActiveRecord initializes attributes from keyword params/defaults; plain Ruby sets every field nil)
    unless defs['initialize'] || fields.empty?
      fid = "#{q}#initialize"; methods['__init__'] = fid
      if @ar && !@ar_cols.empty?
        iparams, ibody = [], []
        fields.each do |f|
          cn = f['name'].delete_prefix('@')
          if (info = @ar_cols[cn])
            t = f['t']
            if %w[int float bool str choice].include?(t['k']) || (t['k'] == 'opt' && %w[int float bool str choice].include?(t['of']&.[]('k')))
              dflt = info['dflt'] ? expr(info['dflt']) : nil
              iparams << {'name' => cn, 't' => t, 'kw' => true, **(dflt ? {'dflt' => dflt} : {})}
              ibody << {'s' => 'set', 'p' => z, 'to' => ivar(f['name'], cdef), 'x' => {'e' => 'var', 'n' => cn, 'p' => where(cdef)}}
            else
              ibody << {'s' => 'set', 'p' => z, 'to' => ivar(f['name'], cdef), 'x' => {'e' => 'none', 'p' => where(cdef)}}
            end
          else
            ibody << {'s' => 'set', 'p' => z, 'to' => ivar(f['name'], cdef), 'x' => {'e' => 'none', 'p' => where(cdef)}}
          end
        end
        @funcs[fid] = fn_of(fid, 'initialize', cdef, iparams, ibody)
      else
        @funcs[fid] = fn_of(fid, 'initialize', cdef, [], fields.map { |f| {'s' => 'set', 'p' => z, 'to' => ivar(f['name'], cdef), 'x' => {'e' => 'none', 'p' => where(cdef)}} })
      end
    end
    @recs[q] = {'name' => q, 'short' => q.split('::').last, 'fields' => fields, 'methods' => methods, 'kinds' => @ar ? ['activerecord'] : [], 'own' => true, 'module' => q, 'p' => where(cdef)}
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
    return 'none' if v == :none
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
      k = if clock?(v) || (ARITH.include?(v.name) && v.receiver) || %i[min max abs to_i size length count].include?(v.name) then 'int'
          elsif CMP.key?(v.name) || v.name.to_s.end_with?('?') then 'bool'
          end
      k && v.safe_navigation? ? [k, 'none'] : k
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
    # (one the method keeps in a field or ActiveRecord attribute: the field's type)
    each_node(d) do |n|
      return ivar_type(n.name.to_s) if n.is_a?(Prism::InstanceVariableWriteNode) && n.value.is_a?(Prism::LocalVariableReadNode) && n.value.name.to_s == name
      if @ar && n.is_a?(Prism::CallNode) && (!n.receiver || n.receiver.is_a?(Prism::SelfNode)) && n.name == :write_attribute
        as = n.arguments&.arguments || []
        if as.length >= 2 && as[1].is_a?(Prism::LocalVariableReadNode) && as[1].name.to_s == name && (cn = str_or_sym(as[0]))
          return @ar_cols[cn]&.[]('t') || ivar_type("@#{cn}")
        end
      end
    end
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
  def collect_pre
    saved, @pre = @pre, []
    val = yield
    [@pre, val]
  ensure
    @pre = saved
  end
  def fresh_tmp = "$sn#{@tmp += 1}"
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
      pre, c = collect_pre { expr(s.predicate) }
      pre + [{'s' => 'if', 'p' => p, 'c' => s.is_a?(Prism::UnlessNode) ? {'e' => 'not', 'x' => c, 'p' => p} : c, 'then' => th, 'else' => el}]
    when Prism::CaseNode
      return [{'s' => 'no', 'p' => p, 'why' => 'case without a value'}] unless s.predicate
      pre, subj = collect_pre { expr(s.predicate) }
      pre + s.conditions.reverse.reduce(block(body_of(s.else_clause), tail)) do |rest, w|
        c = {'e' => 'or', 'xs' => w.conditions.map { |x| {'e' => 'cmp', 'op' => '==', 'x' => subj, 'y' => expr(x), 'p' => where(x), 'text' => text(x)} }, 'p' => where(w)}
        # (at line 0: Ruby counts no line at a when)
        [{'s' => 'if', 'p' => "#{@base}:0:0", 'c' => c, 'then' => block(body_of(w.statements), tail), 'else' => rest}]
      end
    when Prism::ReturnNode
      a = s.arguments&.arguments || []
      if a.length == 1 && (a[0].is_a?(Prism::InstanceVariableOrWriteNode) || a[0].is_a?(Prism::LocalVariableOrWriteNode) || a[0].is_a?(Prism::InstanceVariableAndWriteNode) || a[0].is_a?(Prism::LocalVariableAndWriteNode))
        return stmt(a[0], true)
      end
      pre, x = a.length == 1 ? collect_pre { expr(a[0]) } : [[], nil]
      pre + [{'s' => 'ret', 'p' => p, **(a.length == 1 ? {'x' => x} : a.empty? ? {} : {'x' => no(s, 'a return of several values')})}]
    when Prism::LocalVariableWriteNode
      pre, x = collect_pre { expr(s.value) }
      pre + [{'s' => 'set', 'p' => p, 'to' => {'e' => 'var', 'n' => s.name.to_s, 'p' => p}, 'x' => x}, *(tail ? ret.({'e' => 'var', 'n' => s.name.to_s, 'p' => p}) : [])]
    when Prism::InstanceVariableWriteNode
      pre, x = collect_pre { expr(s.value) }
      pre + [{'s' => 'set', 'p' => p, 'to' => ivar(s.name.to_s, s), 'x' => x}, *(tail ? ret.(ivar(s.name.to_s, s)) : [])]
    when Prism::InstanceVariableOrWriteNode, Prism::LocalVariableOrWriteNode, Prism::InstanceVariableAndWriteNode, Prism::LocalVariableAndWriteNode
      is_or = s.is_a?(Prism::InstanceVariableOrWriteNode) || s.is_a?(Prism::LocalVariableOrWriteNode)
      t = s.is_a?(Prism::LocalVariableOrWriteNode) || s.is_a?(Prism::LocalVariableAndWriteNode) ? {'e' => 'var', 'n' => s.name.to_s, 'p' => p} : ivar(s.name.to_s, s)
      c = is_or ? {'e' => 'not', 'x' => t, 'p' => p} : t
      vpre, vx = collect_pre { expr(s.value) }
      [{'s' => 'if', 'p' => p, 'c' => c, 'then' => vpre + [{'s' => 'set', 'p' => p, 'to' => t, 'x' => vx}], 'else' => []}, *(tail ? ret.(t) : [])]
    when Prism::InstanceVariableOperatorWriteNode, Prism::LocalVariableOperatorWriteNode
      t = s.is_a?(Prism::LocalVariableOperatorWriteNode) ? {'e' => 'var', 'n' => s.name.to_s, 'p' => p} : ivar(s.name.to_s, s)
      op = s.respond_to?(:binary_operator) ? s.binary_operator : s.operator
      pre, vx = collect_pre { expr(s.value) }
      pre + [{'s' => 'set', 'p' => p, 'to' => t, 'x' => binop(op, t, vx, s)}, *(tail ? ret.(t) : [])]
    when Prism::CallNode
      if s.name == :raise && !s.receiver
        # (the class raised and its bases; a bare raise, or of the exception a rescue bound, a re-raise)
        a0 = s.arguments&.arguments&.first
        a0 = a0.receiver if a0.is_a?(Prism::CallNode) && a0.name == :new && a0.receiver
        return [{'s' => 'fail', 'p' => p, 'why' => 'raise', 'reraise' => true}] if a0.nil? || (a0.is_a?(Prism::LocalVariableReadNode) && @caught.include?(a0.name.to_s))
        k = a0.is_a?(Prism::ConstantReadNode) || a0.is_a?(Prism::ConstantPathNode) ? exc_class(a0.slice) : [['RuntimeError', 'StandardError', 'Exception'], false]
        return [{'s' => 'fail', 'p' => p, 'why' => "raise #{text(s.arguments || s)}".sub(/raise raise/, 'raise'), 'cls' => k[0], **(k[1] ? {'open' => true} : {})}]
      end
      if s.name == :synchronize && s.block.is_a?(Prism::BlockNode) && s.receiver
        pre, rx = collect_pre { expr(s.receiver) }
        return pre + [{'s' => 'with', 'p' => p, 'items' => [{'x' => rx}], 'body' => block(body_of(s.block.body), tail)}]
      end
      if @ar && (!s.receiver || s.receiver.is_a?(Prism::SelfNode)) && (s.name == :write_attribute || (s.name == :[]= && s.receiver.is_a?(Prism::SelfNode)))
        as = s.arguments&.arguments || []
        if as.length == 2 && (cn = str_or_sym(as[0])) && @ar_cols.key?(cn)
          pre, vx = collect_pre { expr(as[1]) }
          iv = ivar("@#{cn}", s)
          return pre + [{'s' => 'set', 'p' => p, 'to' => iv, 'x' => vx}, *(tail ? ret.(iv) : [])]
        end
      end
      pre, x = collect_pre { expr(s) }
      pre + ret.(x)
    when Prism::ParenthesesNode then block(body_of(s.body), tail)
    when Prism::WhileNode, Prism::UntilNode, Prism::ForNode then [{'s' => 'no', 'p' => p, 'why' => 'a loop'}]
    when Prism::BeginNode
      # begin/rescue/else/ensure (a method's own rescue too): each rescue with the classes it names (none: StandardError)
      body = block(body_of(s.statements), tail && !s.else_clause)
      return body unless s.rescue_clause || s.else_clause || s.ensure_clause
      hs, rc = [], s.rescue_clause
      while rc
        again = false
        each_node(rc) { |n| again ||= n.is_a?(Prism::RetryNode) }
        return [{'s' => 'no', 'p' => p, 'why' => 'retry (a loop back into begin)'}] if again
        names = rc.exceptions.empty? ? ['StandardError'] : rc.exceptions.map(&:slice)
        ks = names.map { |n| exc_class(n) }
        as = rc.reference.respond_to?(:name) ? rc.reference.name.to_s : nil
        @caught << as
        hb = block(body_of(rc.statements), tail)
        @caught.pop
        hs << {'p' => where(rc), 'names' => ks.map { |k| k[0][0] }, 'mro' => ks[0][0], **(ks[0][1] ? {'open' => true} : {}), 'raise' => names[0], **(as ? {'as' => as} : {}), 'body' => hb}
        rc = rc.respond_to?(:subsequent) ? rc.subsequent : rc.consequent
      end
      [{'s' => 'try', 'p' => p, 'body' => body, 'handlers' => hs, 'els' => s.else_clause ? block(body_of(s.else_clause), tail) : [], 'fin' => s.ensure_clause ? block(body_of(s.ensure_clause.statements), false) : []}]
    when Prism::DefNode, Prism::ClassNode, Prism::ModuleNode then [{'s' => 'no', 'p' => p, 'why' => 'a definition inside a method'}]
    else
      pre, x = collect_pre { expr(s) }
      pre + ret.(x)
    end
  end
  # A class an exception is: its name and its bases' ([names], open: some the reader can't know), from the file's
  # classes, else Ruby's own.
  def exc_class(name, depth = 0)
    name = name.sub(/\A::/, '')
    @classes ||= classes
    hit = @classes[name] || @classes.find { |k, _| k.end_with?("::#{name}") }&.last
    if hit && depth < 8
      sup = hit[0].superclass
      return [[name], true] unless sup
      b = exc_class(sup.slice, depth + 1)
      return [[name, *b[0]], b[1]]
    end
    k = (Object.const_get(name) rescue nil)
    return [k.ancestors.grep(Class).map(&:name) - %w[Object BasicObject], false] if k.is_a?(Class) && k <= Exception
    [[name], true]
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
    when Prism::AndNode, Prism::OrNode
      lv = expr(x.left)
      rpre, rv = collect_pre { expr(x.right) }
      if rpre.empty? || !@pre
        {'e' => x.is_a?(Prism::AndNode) ? 'and' : 'or', 'xs' => [lv, rv], 'p' => p}
      else
        tv = {'e' => 'var', 'n' => fresh_tmp, 'p' => p}
        @pre << {'s' => 'set', 'p' => p, 'to' => tv, 'x' => lv}
        c = x.is_a?(Prism::AndNode) ? tv : {'e' => 'not', 'x' => tv, 'p' => p}
        @pre << {'s' => 'if', 'p' => p, 'c' => c, 'then' => rpre + [{'s' => 'set', 'p' => p, 'to' => tv, 'x' => rv}], 'else' => []}
        tv
      end
    when Prism::IfNode
      el = else_of(x)
      return no(x, "#{text(x)}: an if of several statements as a value") if (x.statements&.body || []).length > 1
      cv = expr(x.predicate)
      apre, av = collect_pre { x.statements ? expr(x.statements.body.last) : {'e' => 'none', 'p' => p} }
      bpre, bv = collect_pre { el ? expr(el) : {'e' => 'none', 'p' => p} }
      if (apre.empty? && bpre.empty?) || !@pre
        {'e' => 'ite', 'c' => cv, 'a' => av, 'b' => bv, 'p' => p}
      else
        tv = {'e' => 'var', 'n' => fresh_tmp, 'p' => p}
        @pre << {'s' => 'if', 'p' => p, 'c' => cv, 'then' => apre + [{'s' => 'set', 'p' => p, 'to' => tv, 'x' => av}], 'else' => bpre + [{'s' => 'set', 'p' => p, 'to' => tv, 'x' => bv}]}
        tv
      end
    when Prism::InterpolatedStringNode
      {'e' => 'fstr', 'parts' => x.parts.map { |q| q.is_a?(Prism::StringNode) ? q.unescaped : q.is_a?(Prism::EmbeddedVariableNode) ? {'x' => expr(q.variable), 'plain' => true} : {'x' => q.respond_to?(:statements) && q.statements&.body&.length == 1 ? expr(q.statements.body[0]) : no(q, 'an interpolation'), 'plain' => true} }, 'p' => p, 'text' => text(x)}
    when Prism::CallNode then call_expr(x)
    else no(x, "#{text(x)}: #{x.type} (outside the subset)")
    end
  end
  def simple_recv?(r)
    r.is_a?(Prism::LocalVariableReadNode) || r.is_a?(Prism::InstanceVariableReadNode) || r.is_a?(Prism::SelfNode) || r.is_a?(Prism::NilNode) ||
      r.is_a?(Prism::IntegerNode) || r.is_a?(Prism::FloatNode) || r.is_a?(Prism::StringNode) || r.is_a?(Prism::SymbolNode) ||
      r.is_a?(Prism::TrueNode) || r.is_a?(Prism::FalseNode) || r.is_a?(Prism::ConstantReadNode) || r.is_a?(Prism::ConstantPathNode)
  end
  def call_expr(x)
    p, r, n, args = where(x), x.receiver, x.name, x.arguments&.arguments || []
    return no(x, "#{text(x)}: a block (a closure)") if x.block.is_a?(Prism::BlockNode)
    return {'e' => 'call', 'f' => {'e' => 'lib', 'q' => 'time.time', 'p' => p}, 'args' => [], 'kw' => [], 'p' => p, 'text' => text(x)} if clock?(x)
    if @ar && (!r || r.is_a?(Prism::SelfNode)) && (n == :read_attribute || (n == :[] && r.is_a?(Prism::SelfNode))) && args.length == 1 && (cn = str_or_sym(args[0])) && @ar_cols.key?(cn)
      return ivar("@#{cn}", x)
    end
    if @ar && (!r || r.is_a?(Prism::SelfNode)) && (n == :write_attribute || (n == :[]= && r.is_a?(Prism::SelfNode))) && args.length == 2 && (cn = str_or_sym(args[0])) && @ar_cols.key?(cn) && @pre
      vx = expr(args[1])
      iv = ivar("@#{cn}", x)
      @pre << {'s' => 'set', 'p' => p, 'to' => iv, 'x' => vx}
      return iv
    end
    return self_call(n.to_s, args.map { |a| expr(a) }, x) if !r || r.is_a?(Prism::SelfNode)
    if x.safe_navigation?
      # Safe navigation (`r&.m(args)`): evaluate `r` once; return nil when `r` is nil without evaluating `args` or calling `m`.
      rv0 = r.is_a?(Prism::ArrayNode) ? nil : expr(r)
      return call_on(x, r, rv0, n, args, p) if r.is_a?(Prism::ArrayNode)
      if simple_recv?(r) || !@pre
        bpre, bval = collect_pre { call_on(x, r, rv0, n, args, p) }
        is_nil = {'e' => 'cmp', 'op' => 'is', 'x' => rv0, 'y' => {'e' => 'none', 'p' => p}, 'p' => p, 'text' => text(x)}
        if bpre.empty? || !@pre
          return {'e' => 'ite', 'c' => is_nil, 'a' => {'e' => 'none', 'p' => p}, 'b' => bval, 'p' => p}
        end
        res = {'e' => 'var', 'n' => fresh_tmp, 'p' => p}
        @pre << {'s' => 'if', 'p' => p, 'c' => is_nil, 'then' => [{'s' => 'set', 'p' => p, 'to' => res, 'x' => {'e' => 'none', 'p' => p}}], 'else' => bpre + [{'s' => 'set', 'p' => p, 'to' => res, 'x' => bval}]}
        return res
      end
      tv = {'e' => 'var', 'n' => fresh_tmp, 'p' => p}
      @pre << {'s' => 'set', 'p' => p, 'to' => tv, 'x' => rv0}
      is_nil = {'e' => 'cmp', 'op' => 'is', 'x' => tv, 'y' => {'e' => 'none', 'p' => p}, 'p' => p, 'text' => text(x)}
      bpre, bval = collect_pre { call_on(x, nil, tv, n, args, p) }
      if bpre.empty?
        return {'e' => 'ite', 'c' => is_nil, 'a' => {'e' => 'none', 'p' => p}, 'b' => bval, 'p' => p}
      end
      res = {'e' => 'var', 'n' => fresh_tmp, 'p' => p}
      @pre << {'s' => 'if', 'p' => p, 'c' => is_nil, 'then' => [{'s' => 'set', 'p' => p, 'to' => res, 'x' => {'e' => 'none', 'p' => p}}], 'else' => bpre + [{'s' => 'set', 'p' => p, 'to' => res, 'x' => bval}]}
      return res
    end
    rv = r.is_a?(Prism::ArrayNode) ? nil : expr(r)
    call_on(x, r, rv, n, args, p)
  end
  def call_on(x, r, rv, n, args, p)
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
      return {'e' => 'call', 'f' => {'e' => 'lib', 'q' => 'threading.Lock', 'p' => p}, 'args' => [], 'kw' => [], 'p' => p, 'text' => text(x)} if r && r.slice =~ /\A(::)?(Thread::)?(Mutex|Monitor)\z/
      no(x, "#{text(x)}: an object of another class made")
    else
      return no(x, "#{text(x)}: a method of an array") if r.is_a?(Prism::ArrayNode)
      # (another class's code: at the boundary where it is inferred, with the names its arguments mention)
      return no(x, "#{text(x)}: #{r.slice}, a constant nothing under the root defines (a NameError where it runs)").merge('raises' => true) if (r.is_a?(Prism::ConstantReadNode) || r.is_a?(Prism::ConstantPathNode)) && !defined_const?(r, @nest)
      if r.is_a?(Prism::ConstantReadNode) || r.is_a?(Prism::ConstantPathNode)
        why = no_method(r, n, @nest)
        return no(x, "#{text(x)}: #{why}").merge('raises' => true) if why
        # (its arguments evaluated, as the code does: what fails there fails the step)
        return no(x, "#{text(x)}: #{r.slice}, another class's code").merge('ext' => "#{r.slice}.#{n}", 'names' => mentioned(args), 'args' => args.map { |a| expr(a) }, 'patch' => {'mod' => r.slice, 'path' => [n.to_s]})
      end
      call({'e' => 'get', 'x' => rv, 'f' => n.to_s, 'p' => p, 'text' => text(x)}, args.map { |a| expr(a) }, x)
    end
  end
end

req = JSON.parse(ARGV[0])
r = Reader.new(req)
cls = r.classes
out = {'lang' => 'ruby', 'file' => File.basename(req['file']), 'path' => File.expand_path(req['file']), 'module' => File.basename(req['file'], '.rb'),
       'root' => File.expand_path(req['root']), 'truth' => 'nil-false', 'entries' => []}
# (no names: every class of the file, for the entry inferred)
(req['names'].empty? ? cls.keys : req['names']).each do |n|
  key = cls.key?(n) ? n : cls.keys.find { |k| k.end_with?("::#{n}") }
  out['entries'] << (key ? {'k' => 'class', 'rec' => r.rec_of(key, *cls[key])} : {'k' => 'missing', 'name' => n})
end
out['recs'] = r.instance_variable_get(:@recs)
out['funcs'] = r.instance_variable_get(:@funcs)
out['loads'] = r.loads
# The executor's own failures' bases (nil read as a number: a NoMethodError or a TypeError by the operand's side), and
# the class a stub raises for a rescue of every StandardError.
std = ->(k) { k.ancestors.grep(Class).map(&:name) - %w[Object BasicObject] }
out['kinds'] = {'KeyError' => std.(KeyError), 'ZeroDivisionError' => std.(ZeroDivisionError), 'AttributeError' => std.(NoMethodError)}
out['exc'] = {'mro' => %w[StandardError Exception], 'raise' => 'StandardError'}
puts JSON.generate(out)
