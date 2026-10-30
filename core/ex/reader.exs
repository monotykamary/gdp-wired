# The extractor's Elixir reader (core/extract-ex.ts): a module read through Elixir's own parser (Code.string_to_quoted)
# and lowered into the shared step IR (core/extract-step.ts's SModule, as JSON on stdout). Elixir's state is a value a
# function returns: a GenServer's handle_call ({:reply, r, state}) and handle_cast ({:noreply, state}), an Agent's
# update and get, or a plain function from the state to the new one. The reader lowers each to the executor's own
# shape, an object whose fields are the state's: the state a handler is given is the object, the one it returns is
# written back to its fields, field by field. Function clauses, case and cond are branches on their patterns and
# guards; a field's type is inferred from its default and what the module puts in it, an argument's from what it is
# compared with or computed into. Only nil and false are false.
#
#   elixir core/ex/reader.exs '{"file": <file>, "module": "Mod.Name"}'
Code.require_file("json.exs", __DIR__)

defmodule GdpReader do
  @arith %{+: "+", -: "-", *: "*"}
  @cmp %{<: "<", <=: "<=", >: ">", >=: ">=", ==: "==", !=: "!=", ===: "==", !==: "!="}
  @clock [{[:System], :monotonic_time}, {[:System], :system_time}, {[:System], :os_time}, {[:DateTime], :utc_now}, {:os, :system_time}, {:erlang, :system_time}, {:erlang, :monotonic_time}]

  def run(req) do
    file = req["file"]
    src = File.read!(file)
    ast = Code.string_to_quoted!(src, columns: true, file: file)
    base = Path.basename(file)
    Process.put(:base, base)
    mods = modules(ast, [])
    # (no name: the file's one module, or its one GenServer or Agent: the entry inferred)
    name = req["module"] || (case Enum.filter(mods, fn {_, b} -> length(mods) == 1 or Enum.any?(b, &match?({:use, _, [{:__aliases__, _, [k]} | _]} when k in [:GenServer, :Agent], &1)) end) do [{n, _}] -> n; _ -> "" end)
    case Enum.find(mods, fn {n, _} -> n == name end) || Enum.find(mods, fn {n, _} -> String.ends_with?(n, "." <> name) end) do
      nil -> %{"lang" => "elixir", "file" => base, "path" => Path.expand(file), "module" => name, "root" => Path.dirname(Path.expand(file)), "entries" => [%{"k" => "missing", "name" => name}], "recs" => %{}, "funcs" => %{}}
      {q, body} -> lower(q, body, file, base)
    end
  end

  defp modules({:defmodule, _, [alias, [do: body]]}, nest) do
    q = Enum.join(nest ++ [alias_name(alias)], ".")
    [{q, stmts(body)} | Enum.flat_map(stmts(body), &modules(&1, nest ++ [alias_name(alias)]))]
  end
  defp modules({:__block__, _, xs}, nest), do: Enum.flat_map(xs, &modules(&1, nest))
  defp modules(_, _), do: []
  defp alias_name({:__aliases__, _, parts}), do: Enum.map_join(parts, ".", &to_string/1)
  defp alias_name(a) when is_atom(a), do: inspect(a)
  defp stmts({:__block__, _, xs}), do: xs
  defp stmts(nil), do: []
  defp stmts(x), do: [x]

  def p(meta), do: "#{Process.get(:base)}:#{meta[:line] || 0}:#{meta[:column] || 0}"
  def text(x), do: (s = x |> Macro.to_string() |> String.split() |> Enum.join(" "); if String.length(s) <= 60, do: s, else: String.slice(s, 0, 57) <> "...")
  def meta({_, m, _}) when is_list(m), do: m
  def meta(_), do: []
  def no(x, why), do: %{"e" => "no", "why" => why, "p" => p(meta(x))}

  # --- the module: its state, its handlers ---------------------------------------------------------------------------
  defp lower(q, body, file, base) do
    defs = for {k, m, [head, [do: b]]} <- body, k in [:def, :defp] do
      {name, args, guard} = head_of(head)
      {name, length(args), %{args: args, guard: guard, body: b, meta: m, private: k == :defp}}
    end
    defs = defs ++ for {k, m, [head]} <- body, k in [:def, :defp], {name, args, _} = head_of(head), do: {name, length(args), %{args: args, guard: nil, body: nil, meta: m, bodiless: true}}
    attrs = for {:@, _, [{n, _, [v]}]} <- body, into: %{}, do: {n, v}
    Process.put(:attrs, attrs)
    Process.put(:mod, q)
    struct_kw = Enum.find_value(body, fn {:defstruct, _, [kw]} -> kw; _ -> nil end)
    groups = Enum.group_by(defs, fn {n, a, _} -> {n, a} end, fn {_, _, c} -> c end) |> Enum.map(fn {k, cs} -> {k, Enum.reject(cs, & &1[:bodiless])} end) |> Map.new()
    Process.put(:groups, groups)
    Process.put(:body, body)
    shape = cond do
      Map.has_key?(groups, {:handle_call, 3}) or Map.has_key?(groups, {:handle_cast, 2}) -> :genserver
      Enum.any?(defs, fn {_, _, c} -> agent_call(c.body) != nil end) -> :agent
      true -> :pure
    end
    {fields, init} = state_of(shape, struct_kw, groups)
    Process.put(:fields, Enum.map(fields, &elem(&1, 0)))
    Process.put(:struct, Map.new(fields))
    fns = for {{n, a}, cs} <- groups, n not in [:handle_call, :handle_cast, :init] and cs != [], into: %{}, do: {"#{q}.#{n}/#{a}", func("#{q}.#{n}/#{a}", to_string(n), a, cs, :ret)}
    {methods, msgs, mfns} = handlers(shape, q, groups)
    types = infer(fields, body)
    rec = %{"name" => q, "short" => q |> String.split(".") |> List.last(), "fields" => Enum.map(fields, fn {f, _} -> %{"name" => to_string(f), "t" => Map.get(types, f, %{"k" => "any"})} end),
            "methods" => Map.put(methods, "__init__", "#{q}.__init__"),
            "kinds" => [], "own" => true, "module" => q, "p" => "#{base}:1:1"}
    funcs = fns |> Map.merge(mfns) |> Map.put("#{q}.__init__", init.(q))
    %{"lang" => "elixir", "file" => base, "path" => Path.expand(file), "module" => q, "root" => Path.dirname(Path.expand(file)), "truth" => "nil-false", "shape" => to_string(shape), "msgs" => msgs,
      "init" => Process.get(:init_shape, %{}), "entries" => [%{"k" => "class", "rec" => q}], "recs" => %{q => rec}, "funcs" => funcs}
  end
  defp head_of({:when, _, [{n, _, args}, g]}), do: {n, args || [], g}
  defp head_of({n, _, args}), do: {n, args || [], nil}

  # The state's fields and the constructor: a GenServer's init's {:ok, %{...}}, else the struct's defaults.
  defp state_of(:genserver, kw, groups) do
    case groups[{:init, 1}] do
      [c | _] ->
        {arg_names, shape} = case c.args do
          [{:{}, _, xs}] -> {Enum.map(xs, &var_name/1), "tuple"}
          [{a, b}] -> {[var_name(a), var_name(b)], "tuple"}
          [x] -> {[var_name(x)], "one"}
        end
        Process.put(:init_shape, %{"k" => shape, "names" => Enum.map(arg_names, &to_string/1)})
        m = Enum.find_value(stmts(c.body) |> Enum.reverse(), fn {:ok, {:%{}, _, kv}} -> kv; {:ok, {:%, _, [_, {:%{}, _, kv}]}} -> kv; _ -> nil end)
        if m == nil, do: {[], fn q -> fn_of("#{q}.__init__", "init", [], [%{"s" => "no", "p" => p(c.meta), "why" => "init: a state other than a map literal returned as {:ok, %{...}}"}]) end},
        else: {Enum.map(m, fn {k, v} -> {k, v} end), fn q ->
          pre = Enum.flat_map(Enum.reverse(tl(Enum.reverse(stmts(c.body)))), &stmt(&1, :expr))
          # (an argument kept in a field: the field's type)
          ftype = fn n -> Enum.find_value(m, fn {k, {^n, _, c}} when is_atom(c) -> Map.get(spec_types(Process.get(:body)), k); _ -> nil end) end
          params = for n <- arg_names, not String.starts_with?(to_string(n), "_"), do: %{"name" => to_string(n), "t" => ftype.(n) || int_use(n)}
          fn_of("#{q}.__init__", "init", params, pre ++ Enum.map(m, fn {k, v} -> set_field(k, expr(v), c.meta) end))
        end}
      _ -> {struct_fields(kw), struct_init(kw)}
    end
  end
  defp state_of(_, kw, _), do: {struct_fields(kw), struct_init(kw)}
  defp struct_fields(nil), do: []
  defp struct_fields(kw), do: Enum.map(kw, fn {k, v} -> {k, v}; k -> {k, nil} end)
  defp struct_init(kw), do: fn q -> fn_of("#{q}.__init__", "new", [], Enum.map(struct_fields(kw), fn {k, v} -> set_field(k, expr(v), []) end)) end
  defp var_name({n, _, ctx}) when is_atom(n) and is_atom(ctx), do: n
  defp var_name(_), do: :_

  # --- the handlers: each message (or Agent function, or plain function) a method --------------------------------------
  defp handlers(:genserver, q, groups) do
    for {kind, ar} <- [{:handle_call, 3}, {:handle_cast, 2}], cs = groups[{kind, ar}] || [], cs != [], reduce: {%{}, %{}, %{}} do
      {ms, msgs, fs} ->
        by = Enum.group_by(cs, fn c -> msg_key(hd(c.args)) end)
        Enum.reduce(by, {ms, msgs, fs}, fn {{tag, n}, ccs}, {ms, msgs, fs} ->
          name = if Enum.count(by, fn {{t, _}, _} -> t == tag end) > 1 and n > 0, do: "#{tag}_#{n}", else: to_string(tag)
          fid = "#{q}.#{kind}:#{name}"
          params = arg_names(msg_args(hd(hd(ccs).args)), "m")
          # (a handler's atom replies: one choice)
          Process.put(:replies, for(c <- ccs, {:reply, r, _} <- stmts_tails(c.body), is_atom(r) and not is_boolean(r) and r != nil, uniq: true, do: Atom.to_string(r)))
          body = clauses(ccs, Enum.map(params, &var/1), fn c -> [msg_args(hd(c.args)), List.last(c.args)] end, if(kind == :handle_call, do: :reply, else: :noreply), "#{kind} #{name}")
          {Map.put(ms, name, fid), Map.put(msgs, name, %{"kind" => to_string(kind), "tag" => to_string(tag), "n" => n, "atom" => is_atom(hd(hd(ccs).args))}),
           Map.put(fs, fid, fn_of(fid, name, Enum.zip(params, arg_types(msg_args(hd(hd(ccs).args)))) |> Enum.map(fn {n2, t} -> %{"name" => n2, "t" => t} end), body))}
        end)
    end
  end
  defp handlers(:agent, q, groups) do
    for {{n, a}, [c | _] = cs} <- groups, !c.private, (ag = agent_call(c.body)) != nil, reduce: {%{}, %{}, %{}} do
      {ms, msgs, fs} ->
        {op, fun} = ag
        {:fn, _, [{:->, _, [[sv], fb]}]} = fun
        [pid | rest] = c.args
        # (an argument that defaults to nil, of no type the code states: its default, the harness giving none)
        {given, nils} = Enum.split_with(rest, fn {:\\, _, [_, nil]} -> false; _ -> true end)
        params = Enum.map(given, fn {:\\, _, [v, _]} -> var_name(v); v -> var_name(v) end)
        pre = Enum.map(nils, fn {:\\, _, [v, _]} -> %{"s" => "set", "p" => "#{Process.get(:base)}:0:0", "to" => var(to_string(var_name(v))), "x" => %{"e" => "none", "p" => p(c.meta)}} end)
        bind = %{"s" => "set", "p" => "#{Process.get(:base)}:0:0", "to" => var(to_string(var_name(sv))), "x" => var("self")}
        _ = {pid, cs}
        body = pre ++ [bind] ++ block(stmts(fb), if(op == :update, do: :state, else: :ret))
        fid = "#{q}.#{n}/#{a}"
        {Map.put(ms, to_string(n), fid), Map.put(msgs, to_string(n), %{"kind" => "agent", "fun" => to_string(n), "n" => length(params)}),
         Map.put(fs, fid, fn_of(fid, to_string(n), Enum.map(params, &%{"name" => to_string(&1), "t" => param_type(to_string(&1), fb)}), body))}
    end
  end
  defp handlers(:pure, q, groups) do
    for {{n, a}, [c | _] = cs} <- groups, !c.private, a >= 1, reduce: {%{}, %{}, %{}} do
      {ms, msgs, fs} ->
        params = tl(arg_names({:{}, [], c.args}, "a"))
        fid = "#{q}.#{n}/#{a}"
        body = clauses(cs, [var("self") | Enum.map(params, &var/1)], & &1.args, :pure, "#{n}/#{a}")
        {Map.put(ms, to_string(n), fid), Map.put(msgs, to_string(n), %{"kind" => "pure", "fun" => to_string(n), "n" => a - 1}),
         Map.put(fs, fid, fn_of(fid, to_string(n), Enum.zip(params, tl(arg_types({:{}, [], c.args}))) |> Enum.map(fn {n2, t} -> %{"name" => n2, "t" => t} end), body))}
    end
  end
  # The names of a clause's arguments: its variables', else a#i.
  defp arg_names({:{}, _, xs}, pre), do: xs |> Enum.with_index(1) |> Enum.map(fn {x, i} -> nm = to_string(var_name(x)); if String.starts_with?(nm, "_"), do: "#{pre}#{i}", else: nm end)
  # The tails a body may end in (through if, case and cond).
  defp stmts_tails(b) do
    case stmts(b) |> List.last() do
      {:if, _, [_, kw]} -> stmts_tails(kw[:do]) ++ stmts_tails(kw[:else])
      {:case, _, [_, [do: cs]]} -> Enum.flat_map(cs, fn {:->, _, [_, x]} -> stmts_tails(x) end)
      {:cond, _, [[do: cs]]} -> Enum.flat_map(cs, fn {:->, _, [_, x]} -> stmts_tails(x) end)
      {:{}, _, [:reply, r, st]} -> [{:reply, r, st}]
      x -> [x]
    end
  end
  # The types of a clause's arguments: each variable's by its name's use in the module (a literal: none needed).
  defp arg_types({:{}, _, xs}), do: Enum.map(xs, fn x -> case var_name(x) do :_ -> %{"k" => "any"}; n -> int_use(n) end end)
  defp agent_call(b) do
    case stmts(b) |> List.last() do
      {{:., _, [{:__aliases__, _, [:Agent]}, op]}, _, [_, {:fn, _, _} = f]} when op in [:update, :get] -> {op, f}
      _ -> nil
    end
  end
  defp msg_key(a) when is_atom(a), do: {a, 0}
  defp msg_key({a, _}) when is_atom(a), do: {a, 1}
  defp msg_key({:{}, _, [a | r]}) when is_atom(a), do: {a, length(r)}
  defp msg_key(_), do: {:other, 0}
  defp msg_args(a) when is_atom(a), do: {:{}, [], []}
  defp msg_args({_, x}), do: {:{}, [], [x]}
  defp msg_args({:{}, m, [_ | r]}), do: {:{}, m, r}

  # Clauses: each one's patterns matched (bindings, then its conditions and guard), the first that matches taken.
  defp clauses(cs, subjects, pats_of, sink, what) do
    Enum.reduce(Enum.reverse(cs), [%{"s" => "fail", "p" => "#{Process.get(:base)}:0:0", "why" => "no clause of #{what} matches (a FunctionClauseError)"}], fn c, rest ->
      pats = pats_of.(c)
      pats = case pats do [{:{}, _, xs}, st] -> Enum.zip(xs, subjects) ++ [{st, var("self")}]; _ -> Enum.zip(pats, subjects) end
      {binds, conds} = Enum.reduce(pats, {[], []}, fn {pat, sub}, {b, k} -> {b2, k2} = match(pat, sub); {b ++ b2, k ++ k2} end)
      conds = conds ++ if(c.guard, do: [expr(c.guard)], else: [])
      body = block(stmts(c.body), sink)
      binds ++ if(conds == [], do: body, else: [%{"s" => "if", "p" => "#{Process.get(:base)}:0:0", "c" => %{"e" => "and", "xs" => conds, "p" => p(c.meta)}, "then" => body, "else" => rest}])
    end)
  end
  # A pattern against a value: the names it binds and the conditions it tests.
  defp match({:_, _, _}, _), do: {[], []}
  defp match({:=, _, [a, b]}, s) do
    {b1, k1} = match(a, s)
    {b2, k2} = match(b, s)
    {b1 ++ b2, k1 ++ k2}
  end
  defp match({:^, _, [v]}, s), do: {[], [%{"e" => "cmp", "op" => "==", "x" => s, "y" => expr(v), "p" => p(meta(v)), "text" => text(v)}]}
  defp match({n, m, ctx} = v, s) when is_atom(n) and is_atom(ctx) do
    _ = v
    if String.starts_with?(to_string(n), "_"), do: {[], []}, else: {[%{"s" => "set", "p" => p(m), "to" => var(to_string(n)), "x" => s}], []}
  end
  defp match({:%{}, _, kv}, s), do: match_kv(kv, s)
  defp match({:%, _, [_, {:%{}, _, kv}]}, s), do: match_kv(kv, s)
  defp match(lit, s) when is_integer(lit) or is_atom(lit) or is_binary(lit) do
    {[], [if(lit == nil, do: %{"e" => "cmp", "op" => "is", "x" => s, "y" => %{"e" => "none", "p" => s["p"]}, "p" => s["p"], "text" => inspect(lit)}, else: %{"e" => "cmp", "op" => "==", "x" => s, "y" => expr(lit), "p" => s["p"], "text" => inspect(lit)})]}
  end
  defp match(pat, s), do: {[], [no(pat, "#{text(pat)}: a pattern outside the subset") |> Map.put("p", s["p"])]}
  defp match_kv(kv, s), do: Enum.reduce(kv, {[], []}, fn {k, pat}, {b, c} -> {b2, c2} = match(pat, get(s, k, [])); {b ++ b2, c ++ c2} end)

  # --- statements: the last expression's value goes to the sink ------------------------------------------------------
  # :ret (a function's result), :reply ({:reply, r, state}: the state written, r the result), :noreply, :state (an
  # Agent's update: the new state), :pure (a plain function's: the new state, {:ok, state} too; {:error, _} fails).
  def block([], sink), do: tail(nil, sink, [])
  def block(xs, sink) do
    {init, [last]} = Enum.split(xs, -1)
    Enum.flat_map(init, &stmt(&1, :expr)) ++ stmt(last, sink)
  end
  def stmt({:=, m, [pat, v]}, sink) do
    {binds, conds} = match(pat, expr(v))
    tmp = if(conds == [], do: [], else: [%{"s" => "if", "p" => p(m), "c" => %{"e" => "and", "xs" => conds, "p" => p(m)}, "then" => [], "else" => [%{"s" => "fail", "p" => p(m), "why" => "#{text(pat)} doesn't match (a MatchError)"}]}])
    binds ++ tmp ++ if(sink == :expr, do: [], else: tail(pat, sink, m))
  end
  def stmt({:if, m, [c, kw]}, sink) when sink != :expr or true do
    [%{"s" => "if", "p" => p(m), "c" => expr(c), "then" => block(stmts(kw[:do]), sink), "else" => block(stmts(kw[:else]), sink)}]
  end
  def stmt({:unless, m, [c, kw]}, sink), do: stmt({:if, m, [{:!, m, [c]}, kw]}, sink)
  def stmt({:cond, m, [[do: cs]]}, sink) do
    Enum.reduce(Enum.reverse(cs), [%{"s" => "fail", "p" => p(m), "why" => "no cond clause is true (a CondClauseError)"}], fn {:->, cm, [[c], b]}, rest ->
      if c == true, do: block(stmts(b), sink), else: [%{"s" => "if", "p" => p(cm), "c" => expr(c), "then" => block(stmts(b), sink), "else" => rest}]
    end)
  end
  def stmt({:case, m, [x, [do: cs]]}, sink) do
    tmp = "$case#{m[:line]}_#{m[:column]}"
    [%{"s" => "set", "p" => p(m), "to" => var(tmp), "x" => expr(x)}] ++
      Enum.reduce(Enum.reverse(cs), [%{"s" => "fail", "p" => p(m), "why" => "no case clause matches (a CaseClauseError)"}], fn {:->, cm, [[pat], b]}, rest ->
        {pat, guard} = case pat do {:when, _, [pt, g]} -> {pt, g}; pt -> {pt, nil} end
        {binds, conds} = match(pat, var(tmp))
        conds = conds ++ if(guard, do: [expr(guard)], else: [])
        binds ++ if(conds == [], do: block(stmts(b), sink), else: [%{"s" => "if", "p" => p(cm), "c" => %{"e" => "and", "xs" => conds, "p" => p(cm)}, "then" => block(stmts(b), sink), "else" => rest}])
      end)
  end
  def stmt({:raise, m, _} = x, _), do: [%{"s" => "fail", "p" => p(m), "why" => text(x)}]
  def stmt({:__block__, _, xs}, sink), do: block(xs, sink)
  def stmt(x, :expr), do: [%{"s" => "expr", "p" => p(meta(x)), "x" => expr(x)}]
  def stmt(x, sink), do: tail(x, sink, meta(x))
  # The value at the end of a handler, to its sink.
  def tail(_, :expr, _), do: []
  def tail(x, :ret, m), do: [%{"s" => "ret", "p" => p(m), "x" => if(x == nil, do: %{"e" => "none", "p" => p(m)}, else: expr(x))}]
  # (the reply evaluated before the state is written back: it reads the state the handler was given)
  def tail({:reply, r, st}, :reply, m), do: [%{"s" => "set", "p" => p(m), "to" => var("$reply"), "x" => reply(r)} | write_state(st, m)] ++ [%{"s" => "ret", "p" => p(m), "x" => var("$reply")}]
  def tail({:{}, _, [:reply, r, st]}, :reply, m), do: tail({:reply, r, st}, :reply, m)
  defp reply(r) do
    rs = Process.get(:replies) || []
    if is_atom(r) and length(rs) > 1 and Atom.to_string(r) in rs, do: %{"e" => "variant", "v" => Atom.to_string(r), "values" => rs, "p" => "#{Process.get(:base)}:0:0"}, else: expr(r)
  end
  def tail({:noreply, st}, sink, m) when sink in [:reply, :noreply], do: write_state(st, m) ++ [%{"s" => "ret", "p" => p(m)}]
  def tail({:ok, st}, :pure, m), do: write_state(st, m) ++ [%{"s" => "ret", "p" => p(m)}]
  def tail({:error, e}, :pure, m), do: [%{"s" => "fail", "p" => p(m), "why" => "{:error, #{text(e)}} returned"}]
  def tail(st, sink, m) when sink in [:state, :pure], do: write_state(st, m) ++ [%{"s" => "ret", "p" => p(m)}]
  def tail(x, sink, m) when sink in [:reply, :noreply] do
    # (a handler's tuple made elsewhere, by a function of the module: taken apart where it returns)
    tmp = "$tail#{m[:line]}_#{m[:column]}"
    ks = if sink == :reply, do: ["$tag", "$r", tmp], else: ["$tag", tmp]
    [%{"s" => "set", "p" => p(m), "to" => %{"e" => "tuple", "xs" => Enum.map(ks, &var/1), "p" => p(m)}, "x" => expr(x)}] ++ write_state({String.to_atom(tmp), [], nil}, m) ++
      [Map.merge(%{"s" => "ret", "p" => p(m)}, if(sink == :reply, do: %{"x" => var("$r")}, else: %{}))]
  end
  defp write_state(st, m) do
    v = "$state#{m[:line]}_#{m[:column]}"
    [%{"s" => "set", "p" => p(m), "to" => var(v), "x" => expr(st)} | Enum.map(Process.get(:fields), fn f -> set_field(f, get(var(v), f, m), m) end)]
  end
  defp set_field(f, x, m), do: %{"s" => "set", "p" => (if m == [], do: "#{Process.get(:base)}:0:0", else: p(m)), "to" => get(var("self"), f, m), "x" => x}
  def var(n), do: %{"e" => "var", "n" => n, "p" => "#{Process.get(:base)}:0:0"}
  def get(x, f, m), do: %{"e" => "get", "x" => x, "f" => to_string(f), "p" => p(m), "text" => to_string(f)}
  def fn_of(fid, name, params, body), do: %{"id" => fid, "name" => name, "cls" => Process.get(:mod), "p" => "#{Process.get(:base)}:1:1", "span" => [Process.get(:base), 1, 1], "params" => [%{"name" => "self", "t" => %{"k" => "any"}, "self" => true} | params], "ret" => %{"k" => "any"}, "body" => body, "decorators" => []}
  # A function of the module, its clauses on its arguments.
  defp func(fid, name, a, cs, sink) do
    params = for i <- 1..a//1, do: "a#{i}"
    f = fn_of(fid, name, Enum.map(params, &%{"name" => &1, "t" => %{"k" => "any"}}), clauses(cs, Enum.map(params, &var/1), & &1.args, sink, "#{name}/#{a}"))
    Map.put(f, "params", tl(f["params"])) |> Map.put("static", true)
  end

  # --- expressions --------------------------------------------------------------------------------------------------
  def expr(x) when is_integer(x), do: %{"e" => "int", "v" => Integer.to_string(x), "p" => "#{Process.get(:base)}:0:0"}
  def expr(x) when is_float(x), do: (if x == Float.floor(x), do: %{"e" => "int", "v" => Integer.to_string(trunc(x)), "float" => true, "p" => "#{Process.get(:base)}:0:0"}, else: %{"e" => "no", "why" => "#{x}: a float that isn't whole", "p" => "#{Process.get(:base)}:0:0"})
  def expr(x) when is_boolean(x), do: %{"e" => "bool", "v" => x, "p" => "#{Process.get(:base)}:0:0"}
  def expr(nil), do: %{"e" => "none", "p" => "#{Process.get(:base)}:0:0"}
  def expr(x) when is_atom(x), do: %{"e" => "str", "v" => Atom.to_string(x), "p" => "#{Process.get(:base)}:0:0"}
  def expr(x) when is_binary(x), do: %{"e" => "str", "v" => x, "p" => "#{Process.get(:base)}:0:0"}
  def expr({a, b}), do: %{"e" => "tuple", "xs" => [expr(a), expr(b)], "p" => "#{Process.get(:base)}:0:0"}
  def expr({:{}, m, xs}), do: %{"e" => "tuple", "xs" => Enum.map(xs, &expr/1), "p" => p(m)}
  def expr({:__block__, _, [x]}), do: expr(x)
  def expr({:@, m, [{n, _, nil}]}), do: (case Process.get(:attrs)[n] do nil -> %{"e" => "no", "why" => "@#{n}: an attribute the reader can't read", "p" => p(m)}; v -> expr(v) end)
  def expr({:__MODULE__, m, _}), do: %{"e" => "no", "why" => "__MODULE__ as a value", "p" => p(m)}
  def expr({n, m, ctx}) when is_atom(n) and is_atom(ctx), do: %{"e" => "var", "n" => to_string(n), "p" => p(m)}
  def expr({:|>, m, [a, {f, fm, args}]}), do: expr({f, fm, [a | args || []]}) |> Map.put("p", p(m))
  def expr({op, m, [a, b]}) when is_map_key(@arith, op), do: %{"e" => "bin", "op" => @arith[op], "x" => expr(a), "y" => expr(b), "p" => p(m), "text" => text({op, m, [a, b]})}
  def expr({op, m, [a, b]} = x) when is_map_key(@cmp, op), do: %{"e" => "cmp", "op" => @cmp[op], "x" => expr(a), "y" => expr(b), "p" => p(m), "text" => text(x)}
  def expr({op, m, [a, b]}) when op in [:and, :&&], do: %{"e" => "and", "xs" => [expr(a), expr(b)], "p" => p(m)}
  def expr({op, m, [a, b]}) when op in [:or, :||], do: %{"e" => "or", "xs" => [expr(a), expr(b)], "p" => p(m)}
  def expr({op, m, [a]}) when op in [:not, :!], do: %{"e" => "not", "x" => expr(a), "p" => p(m)}
  def expr({:-, m, [a]}), do: %{"e" => "neg", "x" => expr(a), "p" => p(m)}
  def expr({:/, m, _} = x), do: %{"e" => "no", "why" => "#{text(x)}: a float division (the subset reads trunc(a / k), div and rem)", "p" => p(m)}
  def expr({:if, m, [c, kw]}), do: %{"e" => "ite", "c" => expr(c), "a" => expr(single(kw[:do], m)), "b" => expr(single(kw[:else], m)), "p" => p(m)}
  def expr({:%{}, m, [{:|, _, [s, kv]}]}), do: upd(expr(s), kv, m)
  def expr({:%, m, [_, {:%{}, _, kv}]}), do: struct_new(kv, m)
  def expr({:%{}, m, _} = x), do: %{"e" => "no", "why" => "#{text(x)}: a map literal (a state is updated: %{s | f: v})", "p" => p(m)}
  def expr({{:., m, [v, f]}, km, []}) when is_atom(f) and not is_tuple(elem(v, 0)) and is_list(km), do: (if km[:no_parens], do: get(expr(v), f, m), else: call_expr(v, f, [], m))
  def expr({{:., m, [mod, f]}, _, args}), do: call_expr(mod, f, args, m)
  def expr({:fn, m, _}), do: %{"e" => "no", "why" => "an anonymous function (a closure)", "p" => p(m)}
  def expr({f, m, args} = x) when is_atom(f) and is_list(args) do
    a = length(args)
    cond do
      f in [:div, :rem] and a == 2 -> %{"e" => "bin", "op" => (if f == :div, do: "/", else: "%"), "ovf" => "wrap", "x" => expr(Enum.at(args, 0)), "y" => expr(Enum.at(args, 1)), "p" => p(m), "text" => text(x)}
      f == :trunc and a == 1 and match?({:/, _, [_, _]}, hd(args)) -> (fn {:/, dm, [p1, p2]} -> %{"e" => "bin", "op" => "/", "ovf" => "wrap", "x" => expr(p1), "y" => expr(p2), "p" => p(dm), "text" => text(x)} end).(hd(args))
      f in [:min, :max, :abs] -> %{"e" => "call", "f" => %{"e" => "builtin", "n" => to_string(f), "p" => p(m)}, "args" => Enum.map(args, &expr/1), "kw" => [], "p" => p(m), "text" => text(x)}
      f in [:raise, :throw, :exit] -> %{"e" => "no", "why" => "#{text(x)} as a value", "p" => p(m)}
      Map.has_key?(Process.get(:groups), {f, a}) -> %{"e" => "call", "f" => %{"e" => "fn", "id" => "#{Process.get(:mod)}.#{f}/#{a}", "p" => p(m)}, "args" => Enum.map(args, &expr/1), "kw" => [], "p" => p(m), "text" => text(x)}
      true -> %{"e" => "no", "why" => "#{text(x)}: #{f}/#{a}, a function the module doesn't define", "p" => p(m)}
    end
  end
  def expr(x), do: no(x, "#{text(x)}: outside the subset")
  defp single(nil, m), do: {:__block__, m, [nil]}
  defp single(b, m), do: (case stmts(b) do [x] -> x; _ -> {:__block__, m, [{:raise, m, ["several statements as a value"]}]} end)
  defp upd(s, kv, m), do: %{"e" => "upd", "x" => s, "fields" => Enum.map(kv, fn {k, v} -> [to_string(k), expr(v)] end), "p" => p(m), "text" => "%{... | ...}"}
  defp struct_new(kv, m) do
    defaults = Process.get(:struct)
    fs = Enum.map(Process.get(:fields), fn f -> [to_string(f), expr(Keyword.get(kv, f, defaults[f]))] end)
    %{"e" => "new", "rec" => Process.get(:mod), "fields" => fs, "p" => p(m), "text" => "%struct{}"}
  end
  defp call_expr(mod, f, args, m) do
    key = case mod do {:__aliases__, _, parts} -> parts; a when is_atom(a) -> a; _ -> nil end
    x = {{:., m, [mod, f]}, m, args}
    cond do
      {key, f} in @clock -> %{"e" => "call", "f" => %{"e" => "lib", "q" => "time.time", "p" => p(m)}, "args" => [], "kw" => [], "p" => p(m), "text" => text(x)}
      key == [:DateTime] and f == :diff and (length(args) == 2 or Enum.at(args, 2) == :second) -> %{"e" => "bin", "op" => "-", "x" => expr(Enum.at(args, 0)), "y" => expr(Enum.at(args, 1)), "p" => p(m), "text" => text(x)}
      key == [:Map] and f == :put and match?([_, k, _] when is_atom(k), args) -> upd(expr(Enum.at(args, 0)), [{Enum.at(args, 1), Enum.at(args, 2)}], m)
      key == [:Map] and f == :merge and match?([_, {:%{}, _, _}], args) -> upd(expr(Enum.at(args, 0)), elem(Enum.at(args, 1), 2), m)
      key == [:Map] and f == :get and match?([_, k] when is_atom(k), args) -> get(expr(Enum.at(args, 0)), Enum.at(args, 1), m)
      # (another module's code: at the boundary where it is inferred; its arguments are values, which it can't change)
      is_atom(mod) or is_tuple(mod) and elem(mod, 0) == :__aliases__ -> %{"e" => "no", "why" => "#{text(x)}: another module's code", "p" => p(m), "ext" => "#{text(mod)}.#{f}", "names" => [], "patch" => %{"mod" => text(mod), "path" => [to_string(f)]}}
      true -> %{"e" => "no", "why" => "#{text(x)}: a call outside the subset", "p" => p(m)}
    end
  end

  # --- types, inferred from the defaults and what the module puts in each field --------------------------------------
  defp infer(fields, body) do
    puts = collect(body, %{})
    spec = spec_types(body)
    Map.new(fields, fn {f, dflt} -> {f, spec[f] || case type_of([dflt | Map.get(puts, f, [])]) do %{"k" => "any"} -> int_use(f); t -> t end} end)
  end
  # The types the code states: a @type (or @typep) of a map or a struct with the state's fields, field by field.
  defp spec_types(body) do
    fields = Process.get(:fields) || []
    Enum.find_value(body, %{}, fn
      {:@, _, [{k, _, [{:"::", _, [_, t]}]}]} when k in [:type, :typep] ->
        kv = case t do {:%{}, _, kv} -> kv; {:%, _, [_, {:%{}, _, kv}]} -> kv; _ -> [] end
        if kv != [] and Enum.all?(fields, &Keyword.has_key?(kv, &1)), do: spec_kv(kv)
      _ -> nil
    end)
  end
  defp spec_kv(kv), do: for({k, t} <- kv, is_atom(k), (st = spec_t(t)) != nil, into: %{}, do: {k, st})
  defp spec_t({:|, _, [a, b]}) do
    ts = [a, b] |> Enum.flat_map(fn {:|, _, xs} -> xs; x -> [x] end)
    {nils, rest} = Enum.split_with(ts, &(&1 == nil))
    atoms = Enum.filter(rest, &(is_atom(&1) and not is_boolean(&1)))
    t = cond do
      atoms != [] and length(atoms) == length(rest) -> %{"k" => "choice", "values" => Enum.map(atoms, &Atom.to_string/1), "sym" => true}
      length(rest) == 1 -> spec_t(hd(rest))
      true -> nil
    end
    if t && nils != [], do: %{"k" => "opt", "of" => t}, else: t
  end
  # (written bare, a type parses as a variable)
  defp spec_t({n, _, a}) when n in [:integer, :non_neg_integer, :pos_integer, :neg_integer, :timeout] and (a == [] or is_atom(a)), do: %{"k" => "int"}
  defp spec_t({n, _, a}) when n in [:boolean] and (a == [] or is_atom(a)), do: %{"k" => "bool"}
  defp spec_t({{:., _, [{:__aliases__, _, [:DateTime]}, :t]}, _, []}), do: %{"k" => "int", "dt" => true}
  defp spec_t(_), do: nil
  defp collect(ast, acc) do
    {_, acc} = Macro.prewalk(ast, acc, fn
      {:%{}, _, [{:|, _, [_, kv]}]} = n, a -> {n, add_kv(kv, a)}
      {:%, _, [_, {:%{}, _, kv}]} = n, a -> {n, add_kv(kv, a)}
      {{:., _, [{:__aliases__, _, [:Map]}, :merge]}, _, [_, {:%{}, _, kv}]} = n, a -> {n, add_kv(kv, a)}
      {{:., _, [{:__aliases__, _, [:Map]}, :put]}, _, [_, k, v]} = n, a when is_atom(k) -> {n, add_kv([{k, v}], a)}
      {:ok, {:%{}, _, kv}} = n, a -> {n, add_kv(kv, a)}
      {:=, _, [{v, _, ctx}, val]} = n, a when is_atom(v) and is_atom(ctx) -> {n, Map.update(a, {:local, v}, [val], &[val | &1])}
      n, a -> {n, a}
    end)
    acc |> Enum.map(fn {k, vs} -> {k, Enum.flat_map(vs, fn v -> resolve(v, acc, 0) end)} end) |> Map.new()
  end
  defp add_kv(kv, a), do: Enum.reduce(kv, a, fn {k, v}, a2 when is_atom(k) -> Map.update(a2, k, [v], &[v | &1]); _, a2 -> a2 end)
  defp resolve({v, _, ctx}, acc, d) when is_atom(v) and is_atom(ctx) and d < 4, do: Enum.flat_map(Map.get(acc, {:local, v}, []), &resolve(&1, acc, d + 1))
  defp resolve({:if, _, [_, kw]}, acc, d), do: resolve(single(kw[:do], []), acc, d) ++ resolve(single(kw[:else], []), acc, d)
  defp resolve(x, _, _), do: [x]
  defp kind(x) when is_integer(x), do: "int"
  defp kind(x) when is_float(x), do: "float"
  defp kind(x) when is_boolean(x), do: "bool"
  defp kind(nil), do: "none"
  defp kind(x) when is_atom(x), do: {:sym, Atom.to_string(x)}
  defp kind(x) when is_binary(x), do: "str"
  defp kind({op, _, [_, _]}) when is_map_key(@arith, op) or op in [:div, :rem], do: "int"
  defp kind({op, _, [_, _]}) when is_map_key(@cmp, op) or op in [:and, :or, :&&, :||], do: "bool"
  defp kind({op, _, [_]}) when op in [:not, :!], do: "bool"
  defp kind({f, _, [_ | _]}) when f in [:min, :max, :abs, :div, :rem, :trunc], do: "int"
  defp kind({{:., _, [mod, f]}, _, _}) do
    key = case mod do {:__aliases__, _, parts} -> parts; a -> a end
    cond do
      key == [:DateTime] and f == :utc_now -> "dt"
      {key, f} in @clock or (key == [:DateTime] and f == :diff) -> "int"
      true -> nil
    end
  end
  defp kind(_), do: nil
  defp type_of(vs) do
    ks = vs |> Enum.map(&kind/1) |> Enum.reject(&is_nil/1) |> Enum.uniq()
    {syms, rest} = Enum.split_with(ks, &is_tuple/1)
    # (a DateTime from the clock: a number of seconds, the harness converting)
    dt = "dt" in rest
    rest = Enum.uniq(Enum.map(rest, fn "dt" -> "int"; k -> k end))
    none = "none" in rest
    rest = rest -- ["none"]
    t = cond do
      syms != [] and rest == [] -> %{"k" => "choice", "values" => Enum.map(syms, &elem(&1, 1)), "sym" => true}
      syms == [] and length(rest) == 1 -> Map.merge(%{"k" => hd(rest)}, if(dt, do: %{"dt" => true}, else: %{}))
      syms == [] and Enum.sort(rest) == ["float", "int"] -> %{"k" => "float"}
      true -> nil
    end
    cond do t == nil -> %{"k" => "any"}; none -> %{"k" => "opt", "of" => t}; true -> t end
  end
  # A name the module computes with or orders anywhere (as a field's, an argument's or a pattern's variable): a number.
  defp int_use(n) do
    {_, k} = Macro.prewalk(Process.get(:body), false, fn
      {op, _, [a, b]} = x, acc when op in [:+, :-, :*, :<, :<=, :>, :>=, :div, :rem] -> {x, acc or Enum.any?([a, b], &named?(&1, n))}
      {f, _, [a, b]} = x, acc when f in [:div, :rem] -> {x, acc or Enum.any?([a, b], &named?(&1, n))}
      x, acc -> {x, acc}
    end)
    if k, do: %{"k" => "int"}, else: %{"k" => "any"}
  end
  defp named?({m, _, ctx}, n) when is_atom(m) and is_atom(ctx), do: m == n
  defp named?({{:., _, [_, f]}, km, []}, n) when is_list(km), do: f == n
  defp named?(_, _), do: false
  # An argument's type: what its function compares it with or computes it into.
  defp param_type(name, body) do
    n = String.to_atom(name)
    {_, k} = Macro.prewalk(body, nil, fn
      {op, _, [a, b]} = x, acc when is_map_key(@cmp, op) or is_map_key(@arith, op) -> {x, acc || (if match?({^n, _, c} when is_atom(c), a) or match?({^n, _, c} when is_atom(c), b), do: %{"k" => "int"})}
      x, acc -> {x, acc}
    end)
    k || %{"k" => "any"}
  end
end

[arg] = System.argv()
IO.puts(GdpJson.encode(GdpReader.run(GdpJson.decode(arg))))
