# Elixir for the Elixir front end's jobs (core/extract-ex.ts): the image's elixir, else Debian's (Erlang with it), once
# per container. Source it (`. research/langs/elixir/elixir-setup.sh`).
if ! command -v elixir >/dev/null 2>&1; then
  timeout -s KILL 400 sh -c 'apt-get update -qq >/dev/null 2>&1 && apt-get install -y -qq elixir >/dev/null 2>&1' || echo "elixir-setup: the install failed"
fi
elixir -e 'IO.puts("elixir #{System.version()}, otp #{System.otp_release()}")'
