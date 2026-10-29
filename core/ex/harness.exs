# The Elixir side of the extractor's check (core/extract-step.ts's checkStep): the module compiled from its file as it
# ships (its clock calls read the request's time: System.monotonic_time, system_time, os_time, DateTime.utc_now,
# :os.system_time, :erlang.system_time), its state made the way the module makes it (a GenServer started with its
# init's argument, an Agent with its start_link), set and read through :sys, each request a call of the module's own,
# one JSON line a request over two named pipes.
#
#   elixir core/ex/harness.exs <in-fifo> <out-fifo>
Code.require_file("json.exs", __DIR__)
import Bitwise

defmodule GdpClock do
  def now, do: :persistent_term.get(:gdp_now, 0)
  def int(_ \\ nil), do: now()
  def utc_now(_ \\ nil), do: DateTime.from_unix!(now())
end

defmodule GdpHarness do
  @clock %{{[:System], :monotonic_time} => :int, {[:System], :system_time} => :int, {[:System], :os_time} => :int, {[:DateTime], :utc_now} => :utc_now,
           {:os, :system_time} => :int, {:erlang, :system_time} => :int, {:erlang, :monotonic_time} => :int}
  def hello(req) do
    ast = Code.string_to_quoted!(File.read!(req["path"]), file: req["path"])
    ast = Macro.prewalk(ast, fn
      {{:., m, [mod, f]}, m2, args} = x ->
        key = case mod do {:__aliases__, _, parts} -> parts; a -> a end
        case @clock[{key, f}] do nil -> x; g -> {{:., m, [{:__aliases__, m, [:GdpClock]}, g]}, m2, args} end
      x -> x
    end)
    Code.compile_quoted(ast, req["path"])
    Process.put(:s, req |> Map.put("mod", Module.concat([req["module"]])))
    %{"ok" => true}
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
      "call" ->
        [{_, o}] = :ets.lookup(objs, req["id"])
        {o2, r} = GdpHarness.call(o, req["m"], req["a"])
        :ets.insert(objs, {req["id"], o2})
        case r do {:err, e} -> %{"out" => nil, "err" => e}; v -> %{"out" => GdpHarness.tag(v)} end
      "coverage" -> %{"hit" => []}
      op -> %{"error" => "no op #{op}"}
    end
  rescue e -> %{"error" => Exception.message(e) |> String.slice(0, 500)}
  catch :exit, r -> %{"error" => "exit: #{inspect(r) |> String.slice(0, 500)}"}
  end
  IO.binwrite(out, GdpJson.encode(res) <> "\n")
end)
