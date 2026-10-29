# A small JSON codec for the Elixir reader and harness (an Elixir older than 1.18 has none built in).
defmodule GdpJson do
  def encode(nil), do: "null"
  def encode(true), do: "true"
  def encode(false), do: "false"
  def encode(x) when is_integer(x), do: Integer.to_string(x)
  def encode(x) when is_float(x), do: :erlang.float_to_binary(x, [:short])
  def encode(x) when is_atom(x), do: encode(Atom.to_string(x))
  def encode(x) when is_binary(x), do: "\"" <> esc(x) <> "\""
  def encode(x) when is_list(x), do: "[" <> Enum.map_join(x, ",", &encode/1) <> "]"
  def encode(%{} = m), do: "{" <> Enum.map_join(m, ",", fn {k, v} -> encode(to_string(k)) <> ":" <> encode(v) end) <> "}"
  def encode(x) when is_tuple(x), do: encode(Tuple.to_list(x))
  defp esc(s), do: s |> String.replace("\\", "\\\\") |> String.replace("\"", "\\\"") |> String.replace("\n", "\\n") |> String.replace("\t", "\\t") |> String.replace("\r", "\\r")

  def decode(s), do: (s |> String.trim() |> value() |> elem(0))
  defp ws(s), do: String.trim_leading(s)
  defp value("{" <> r), do: obj(ws(r), %{})
  defp value("[" <> r), do: arr(ws(r), [])
  defp value("\"" <> r), do: str(r, "")
  defp value("true" <> r), do: {true, r}
  defp value("false" <> r), do: {false, r}
  defp value("null" <> r), do: {nil, r}
  defp value(r) do
    [n] = Regex.run(~r/^-?\d+(\.\d+)?([eE][-+]?\d+)?/, r)
    {if(String.contains?(n, [".", "e", "E"]), do: String.to_float(n), else: String.to_integer(n)), binary_part(r, byte_size(n), byte_size(r) - byte_size(n))}
  end
  defp obj("}" <> r, m), do: {m, r}
  defp obj(r, m) do
    {k, r} = value(ws(r)); ":" <> r = ws(r); {v, r} = value(ws(r))
    case ws(r) do "," <> r -> obj(ws(r), Map.put(m, k, v)); "}" <> r -> {Map.put(m, k, v), r} end
  end
  defp arr("]" <> r, l), do: {Enum.reverse(l), r}
  defp arr(r, l) do
    {v, r} = value(ws(r))
    case ws(r) do "," <> r -> arr(ws(r), [v | l]); "]" <> r -> {Enum.reverse([v | l]), r} end
  end
  defp str("\"" <> r, acc), do: {acc, r}
  defp str("\\" <> <<c, r::binary>>, acc) do
    case c do
      ?n -> str(r, acc <> "\n"); ?t -> str(r, acc <> "\t"); ?r -> str(r, acc <> "\r")
      ?u -> <<h::binary-size(4), r2::binary>> = r; str(r2, acc <> <<String.to_integer(h, 16)::utf8>>)
      _ -> str(r, acc <> <<c>>)
    end
  end
  defp str(<<c::utf8, r::binary>>, acc), do: str(r, acc <> <<c::utf8>>)
end
