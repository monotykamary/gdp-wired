# The Elixir side of the extractor's check (core/extract-step.ts's checkStep): the module compiled from its file as it
# ships (its clock calls read the request's time: System.monotonic_time, system_time, os_time, DateTime.utc_now,
# :os.system_time, :erlang.system_time), its state made the way the module makes it (a GenServer started with its
# init's argument, an Agent with its start_link), set and read through :sys, each request a call of the module's own,
# one JSON line a request over two named pipes.
#
#   elixir core/ex/harness.exs <in-fifo> <out-fifo>
Code.require_file("json.exs", __DIR__)
import Bitwise

# Immutable BEAM values have structural equality, not JS identity. Fresh wire IDs
# never unify equal maps. Container equality must be refused by native-law;
# this transport supports scalar/property laws only (nativeEquality: scalar).
defmodule GdpNative do
  @table :gdp_native_observations
  def init, do: :ets.new(@table, [:named_table, :public, :set])
  def begin_call(mod, fun) do
    :ets.delete_all_objects(@table)
    invocation = Process.get(:gdp_native_invocation, 0) + 1
    if invocation > 9007199254740991, do: raise(ArgumentError, "native invocation exceeds exact integer range")
    Process.put(:gdp_native_invocation, invocation)
    :ets.insert(@table, [{:target, {mod, fun, invocation}}, {:invocation, invocation}])
  end
  defp error(message) do
    if active?(), do: :ets.insert_new(@table, {{:error, Process.get(:gdp_native_active)}, message})
  end
  def capture(mod, fun, bindings, names) do
    invocation = case :ets.lookup(@table, :target) do [{:target, {^mod, ^fun, id}}] -> id; _ -> nil end
    if is_integer(invocation) and :ets.insert_new(@table, {{:entered, invocation}, true}) do
      result = try do
        actual = Map.take(Map.new(bindings), names) |> Map.new(fn {k, v} -> {Atom.to_string(k), v} end)
        %{"snapshot" => snapshot(actual, :object)}
      rescue e -> %{"error" => Exception.message(e)} end
      :ets.insert(@table, {{:bindings, invocation}, result})
      previous = Process.get(:gdp_native_active)
      Process.put(:gdp_native_active, invocation)
      {invocation, previous}
    end
  end
  def leave(nil), do: :ok
  def leave({invocation, previous}) do
    if Process.get(:gdp_native_active) == invocation do
      if is_nil(previous), do: Process.delete(:gdp_native_active), else: Process.put(:gdp_native_active, previous)
    end
    :ok
  end
  defp active? do
    invocation = Process.get(:gdp_native_active)
    is_integer(invocation) and :ets.lookup(@table, :invocation) == [{:invocation, invocation}] and :ets.member(@table, :target)
  end
  # Instrument the original function head, not the reader's argument labels.
  # The first instruction runs after pattern matching, guards and defaults.
  def instrument(ast) do
    Macro.prewalk(ast, fn
      {kind, meta, [head, body]} = node when kind in [:def, :defp] and is_list(body) ->
        plain = case head do {:when, _, [h | _]} -> h; h -> h end
        case plain do
          {name, _, args} when is_list(args) ->
            request = if name in [:handle_call, :handle_cast], do: Enum.take(args, 1), else: Enum.drop(args, 1)
            names = Enum.flat_map(request, &parameter_names/1) |> Enum.uniq()
            body = Keyword.update!(body, :do, fn original ->
              quote do
                native_entry = GdpNative.capture(__MODULE__, unquote(name), binding(), unquote(names))
                try do
                  unquote(original)
                after
                  GdpNative.leave(native_entry)
                end
              end
            end)
            {kind, meta, [head, body]}
          _ -> node
        end
      node -> node
    end)
  end
  defp parameter_names({:\\, _, [pattern, _default]}), do: parameter_names(pattern)
  defp parameter_names(pattern) do
    {_, names} = Macro.prewalk(pattern, [], fn
      {name, _, context} = node, acc when is_atom(name) and (is_atom(context) or is_nil(context)) ->
        {node, if(String.starts_with?(Atom.to_string(name), "_"), do: acc, else: [name | acc])}
      node, acc -> {node, acc}
    end)
    names
  end
  defp scalar(value) when is_nil(value) or is_boolean(value), do: value
  defp scalar(value) when is_atom(value), do: Atom.to_string(value)
  defp scalar(value) when is_binary(value) do
    if not String.valid?(value) or Regex.match?(~r/[\x00-\x08\x0b\x0c\x0e-\x1f]/, value), do: raise(ArgumentError, "unsupported native binary")
    value
  end
  defp scalar(value) when is_integer(value) and abs(value) <= 9007199254740991, do: value
  defp scalar(value) when is_float(value) and abs(value) <= 9007199254740991 and trunc(value) == value, do: trunc(value)
  defp scalar(_), do: raise(ArgumentError, "unsupported native scalar observation")
  def snapshot(value, root_kind \\ :value) do
    {root, _} = encode(value, root_kind, 0)
    %{"version" => 1, "root" => root}
  end
  defp encode(_, _, count) when count >= 10000, do: raise(ArgumentError, "native snapshot exceeds node bound")
  defp encode(value, kind, count) when is_map(value) do
    if Map.get(value, :__struct__) in [Date, Time, DateTime, NaiveDateTime, MapSet, Range, Regex], do: raise(ArgumentError, "unsupported native snapshot struct")
    fields = if is_struct(value), do: Map.from_struct(value), else: value
    object = kind in [:object, :records] or is_struct(value)
    {items, count} = Enum.map_reduce(fields, count + 1, fn {k, v}, n ->
      key = if object and is_atom(k), do: Atom.to_string(k), else: k
      if not (is_binary(key) or (not object and is_integer(key))), do: raise(ArgumentError, "unsupported native map key")
      {key, n} = encode(key, :value, n)
      {v, n} = encode(v, if(kind == :records, do: :records, else: :value), n)
      {[key, v], n}
    end)
    {%{"id" => Integer.to_string(:erlang.unique_integer([:positive, :monotonic])), "kind" => if(object, do: "object", else: "map"), "items" => items}, count}
  end
  defp encode(value, _, count) when is_list(value) do
    {items, count} = Enum.map_reduce(value, count + 1, &encode(&1, :value, &2))
    {%{"id" => Integer.to_string(:erlang.unique_integer([:positive, :monotonic])), "kind" => "array", "items" => items}, count}
  end
  defp encode(value, _, count), do: {scalar(value), count + 1}
  defp record(key, outcome) do
    if active?() do
      slot = {:call, Process.get(:gdp_native_active), key}
      inserted = :ets.insert_new(@table, {slot, outcome})
      if not inserted and :ets.lookup(@table, slot) != [{slot, outcome}], do: error("inconsistent native call #{key}")
    end
    :ok
  end
  def answered(key, call) do
    try do
      value = call.()
      if active?() do
        try do record(key, %{"kind" => "returned", "value" => scalar(value)}) rescue e -> error(Exception.message(e)) end
      end
      value
    rescue e ->
      if active?(), do: record(key, %{"kind" => "raised", "raised" => inspect(e.__struct__)})
      reraise e, __STACKTRACE__
    catch kind, reason ->
      error("unsupported native call outcome #{kind}")
      :erlang.raise(kind, reason, __STACKTRACE__)
    end
  end
  def clock(value) do
    if active?() do
      try do
        actual = scalar(value)
        slot = {:clock, Process.get(:gdp_native_active)}
        if not :ets.insert_new(@table, {slot, actual}) and :ets.lookup(@table, slot) != [{slot, actual}], do: error("inconsistent native clock reads")
      rescue e -> error(Exception.message(e)) end
    end
    :ok
  end
  def finish_call do
    [{:invocation, invocation}] = :ets.lookup(@table, :invocation)
    bindings = case :ets.lookup(@table, {:bindings, invocation}) do [{_, b}] -> b; _ -> %{"error" => "native function entry was not observed"} end
    observed = case :ets.lookup(@table, {:error, invocation}) do
      [{_, message}] -> %{"error" => message}
      [] ->
        calls = Map.new(for {{:call, ^invocation, key}, outcome} <- :ets.tab2list(@table), do: {key, outcome})
        base = %{"invocation" => invocation, "calls" => calls}
        frame = case :ets.lookup(@table, {:clock, invocation}) do [{_, clock}] -> Map.put(base, "clock", clock); [] -> base end
        %{"snapshot" => snapshot(frame, :records)}
    end
    :ets.delete(@table, :target)
    %{"nativeBindings" => bindings, "nativeObservations" => observed}
  end
end

defmodule GdpClock do
  def now do
    value = :persistent_term.get(:gdp_now, 0)
    GdpNative.clock(value)
    value
  end
  def int(_ \\ nil), do: now()
  def utc_now(_ \\ nil), do: DateTime.from_unix!(now())
end

# An answered call's value: the request's input for it, None (nil) where it says so; every process reads it.
defmodule GdpAnswer do
  def a(key), do: GdpNative.answered(key, fn -> case Map.get(:persistent_term.get(:gdp_ans, %{}), key) do nil -> nil; %{"none" => true} -> nil; spec -> GdpHarness.arg(spec) end end)
end

defmodule GdpHarness do
  @clock %{{[:System], :monotonic_time} => :int, {[:System], :system_time} => :int, {[:System], :os_time} => :int, {[:DateTime], :utc_now} => :utc_now,
           {:os, :system_time} => :int, {:erlang, :system_time} => :int, {:erlang, :monotonic_time} => :int}
  def hello(req) do
    ast = Code.string_to_quoted!(File.read!(req["path"]), file: req["path"])
    # (an answered call of another module's function: the call made the stub's, by the module's and function's names)
    ans = Map.new(for a <- req["answers"] || [], a["patch"]["mod"], do: {{a["patch"]["mod"], List.last(a["patch"]["path"])}, a["key"]})
    ast = Macro.prewalk(ast, fn
      {{:., m, [mod, f]}, m2, args} = x ->
        key = case mod do {:__aliases__, _, parts} -> parts; a -> a end
        name = case mod do {:__aliases__, _, parts} -> Enum.map_join(parts, ".", &to_string/1); a -> inspect(a) end
        case {ans[{name, to_string(f)}], @clock[{key, f}]} do
          {k, _} when is_binary(k) -> {{:., m, [{:__aliases__, m, [:GdpAnswer]}, :a]}, m2, [k]}
          {_, nil} -> x
          {_, g} -> {{:., m, [{:__aliases__, m, [:GdpClock]}, g]}, m2, args}
        end
      x -> x
    end)
    GdpNative.init()
    Code.compile_quoted(GdpNative.instrument(ast), req["path"])
    Process.put(:s, req |> Map.put("mod", Module.concat([req["module"]])))
    %{"ok" => true, "nativeSnapshot" => 1, "nativeBindings" => 1, "nativeObservations" => 1, "nativeEquality" => "scalar"}
  end
  def s(k), do: Process.get(:s)[k]
  def leaf_t(l), do: (case l["t"] do %{"k" => "opt", "of" => o} -> o; t -> t || %{} end)
  def enc(v) when is_integer(v), do: Integer.to_string(v)
  def enc(v) when is_float(v), do: (if v == Float.floor(v), do: Integer.to_string(trunc(v)), else: "f:#{v}")
  def enc(%DateTime{} = d), do: Integer.to_string(DateTime.to_unix(d))
  def enc(v), do: "?:#{inspect(v)}"
  def tag(v) when is_boolean(v) or is_nil(v), do: v
  def tag(v) when is_number(v), do: %{"n" => enc(v)}
  def tag(v) when is_atom(v) or is_binary(v), do: %{"s" => to_string(v)}
  def tag(v), do: %{"o" => inspect(v) |> String.slice(0, 40)}
  def arg(%{"in" => v} = a) do
    cond do
      a["sym"] && is_binary(v) -> String.to_atom(v)
      a["float"] -> v * 1.0
      is_binary(v) and Regex.match?(~r/^-?\d+$/, v) -> String.to_integer(v)
      true -> v
    end
  end
  def arg(%{"none" => true}), do: nil
  # (a value the rule never reads: any value, nil)
  def arg(%{"inert" => true}), do: nil
  def state_of(st) do
    for l <- s("leaves"), l["kind"] not in ["frame", "map"], into: %{} do
      v = Map.get(st, String.to_atom(hd(l["path"])))
      {l["name"], case l["kind"] do
        "none" -> v == nil
        "num" -> if v == nil, do: "0", else: enc(v)
        k when k in ["str", "choice"] -> if v == nil, do: "", else: to_string(v)
        "bool" -> v == true
      end}
    end
  end
  def put(st, state) do
    st = Enum.reduce(s("leaves"), st, fn l, acc ->
      f = String.to_atom(hd(l["path"])); v = state[l["name"]]; t = leaf_t(l)
      case l["kind"] do
        "num" -> n = String.to_integer(v); Map.put(acc, f, if(t["dt"], do: DateTime.from_unix!(n), else: if(t["k"] == "float", do: n * 1.0, else: n)))
        k when k in ["str", "choice"] -> Map.put(acc, f, if(t["sym"], do: String.to_atom(v), else: v))
        "bool" -> Map.put(acc, f, v)
        _ -> acc
      end
    end)
    Enum.reduce(s("leaves"), st, fn l, acc -> if l["kind"] == "none" and state[l["name"]] == true, do: Map.put(acc, String.to_atom(hd(l["path"])), nil), else: acc end)
  end
  # The object: the module's own process (a GenServer, an Agent) or the state itself (plain functions).
  def make(a) do
    Process.put(:last_make, a)
    mod = s("mod"); args = Enum.map(a, fn [_, spec] -> arg(spec) end)
    case s("shape") do
      "genserver" ->
        init = if s("init")["k"] == "tuple", do: List.to_tuple(Enum.map(s("init")["names"], fn n -> Enum.find_value(a, fn [k, spec] -> k == n && arg(spec) end) end)), else: hd(args ++ [nil])
        {:ok, pid} = GenServer.start(mod, init); {:pid, pid}
      "agent" ->
        {:ok, pid} = if function_exported?(mod, :start_link, 1), do: (Process.flag(:trap_exit, true); mod.start_link([])), else: Agent.start(fn -> struct(mod) end)
        {:pid, pid}
      _ -> {:val, if(function_exported?(mod, :new, 0), do: mod.new(), else: struct(mod))}
    end
  end
  def get({:pid, pid}), do: :sys.get_state(pid)
  def get({:val, v}), do: v
  def set({:pid, pid} = o, st), do: (:sys.replace_state(pid, fn x -> put(x, st) end); o)
  def set({:val, v}, st), do: {:val, put(v, st)}
  # A call; where it fails (a raise, a crash of the process), the object as it was before it (a fresh process given
  # the state it had: the step refused leaves it so).
  def call(o, m, a) do
    before = get(o)
    case call1(o, m, a) do
      {_, {:err, _}} = r -> {elem(r, 0) |> revive(before), elem(r, 1)}
      r -> r
    end
  end
  defp revive({:pid, pid} = o, st) do
    if Process.alive?(pid), do: (:sys.replace_state(pid, fn _ -> st end); o), else: (case make_fresh() do {:pid, p2} -> :sys.replace_state(p2, fn _ -> st end); {:pid, p2}; v -> v end)
  end
  defp revive(o, _), do: o
  defp make_fresh, do: Process.get(:last_make) |> make()
  def call1(o, m, a) do
    msg = s("msgs")[m]; args = Enum.map(a, fn [_, spec] -> arg(spec) end); mod = s("mod")
    try do
      case {msg["kind"], o} do
        {"handle_call", {:pid, pid}} -> {o, GenServer.call(pid, mk(msg, args))}
        {"handle_cast", {:pid, pid}} -> GenServer.cast(pid, mk(msg, args)); :sys.get_state(pid); {o, nil}
        {"agent", {:pid, pid}} -> {o, apply(mod, String.to_atom(msg["fun"]), [pid | args])}
        {"pure", {:val, v}} ->
          case apply(mod, String.to_atom(msg["fun"]), [v | args]) do
            {:error, e} -> {o, {:err, inspect(e)}}
            {:ok, %{} = n} -> {{:val, n}, nil}
            %{} = n -> {{:val, n}, nil}
            r -> {o, r}
          end
      end
    rescue e -> {o, {:err, Exception.message(e) |> String.slice(0, 300)}}
    catch :exit, r -> {o, {:err, "exit: #{inspect(r) |> String.slice(0, 300)}"}}
    end
  end
  defp mk(%{"n" => 0, "atom" => true, "tag" => t}, _), do: String.to_atom(t)
  defp mk(%{"tag" => t}, args), do: List.to_tuple([String.to_atom(t) | args])
end

[fin, fout] = System.argv()
# (the input first, then the output: the order the check opens them in)
# (a port reading the pipe line by line: Erlang's own file reads of a pipe wait for a full buffer)
port = Port.open({:spawn_executable, System.find_executable("cat")}, [:binary, {:line, 1 <<< 24}, {:args, [fin]}, :eof])
{:ok, out} = File.open(fout, [:write, :binary])
objs = :ets.new(:objs, [:set, :public])
lines = Stream.resource(fn -> "" end, fn acc ->
  receive do
    {^port, {:data, {:eol, l}}} -> {[acc <> l], ""}
    {^port, {:data, {:noeol, l}}} -> {[], acc <> l}
    {^port, :eof} -> {:halt, acc}
  end
end, fn _ -> :ok end)
lines |> Enum.each(fn line ->
  req = GdpJson.decode(line)
  if req["now"], do: :persistent_term.put(:gdp_now, (if is_binary(req["now"]), do: String.to_integer(req["now"]), else: req["now"]))
  res = try do
    case req["op"] do
      "hello" -> GdpHarness.hello(req)
      "new" -> (try do o = GdpHarness.make(req["a"]); i = :ets.info(objs, :size) + 1; :ets.insert(objs, {i, o}); %{"id" => i} rescue e -> %{"err" => Exception.message(e)} catch :exit, r -> %{"err" => inspect(r)} end)
      "at" ->
        (try do o = GdpHarness.make(req["a"]) |> GdpHarness.set(req["state"]); i = :ets.info(objs, :size) + 1; :ets.insert(objs, {i, o}); %{"id" => i} rescue e -> %{"bad" => Exception.message(e)} catch :exit, r -> %{"bad" => inspect(r)} end)
      "get" -> [{_, o}] = :ets.lookup(objs, req["id"]); %{"state" => GdpHarness.state_of(GdpHarness.get(o))}
      "native" -> [{_, o}] = :ets.lookup(objs, req["id"]); %{"snapshot" => GdpNative.snapshot(GdpHarness.get(o), :object)}
      "call" ->
        :persistent_term.put(:gdp_ans, req["answers"] || %{})
        [{_, o}] = :ets.lookup(objs, req["id"])
        msg = GdpHarness.s("msgs")[req["m"]]
        fun = case msg["kind"] do "handle_call" -> :handle_call; "handle_cast" -> :handle_cast; _ -> String.to_atom(msg["fun"]) end
        GdpNative.begin_call(GdpHarness.s("mod"), fun)
        {o2, r} = GdpHarness.call(o, req["m"], req["a"])
        :ets.insert(objs, {req["id"], o2})
        result = case r do {:err, e} -> %{"out" => nil, "err" => e}; v -> %{"out" => GdpHarness.tag(v)} end
        Map.merge(result, GdpNative.finish_call())
      "coverage" -> %{"hit" => []}
      op -> %{"error" => "no op #{op}"}
    end
  rescue e -> %{"error" => Exception.message(e) |> String.slice(0, 500)}
  catch :exit, r -> %{"error" => "exit: #{inspect(r) |> String.slice(0, 500)}"}
  end
  IO.binwrite(out, GdpJson.encode(res) <> "\n")
end)
