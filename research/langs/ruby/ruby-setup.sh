# Ruby for the Ruby front end's jobs (core/extract-rb.ts): the image's ruby where it has Prism, else Debian's ruby and
# the prism gem, once per container. Source it (`. research/langs/ruby/ruby-setup.sh`).
if ! ruby -e 'require "prism"' >/dev/null 2>&1; then
  if ! command -v ruby >/dev/null 2>&1; then
    timeout -s KILL 300 sh -c 'apt-get update -qq >/dev/null 2>&1 && apt-get install -y -qq ruby >/dev/null 2>&1' || echo "ruby-setup: the install failed"
  fi
  timeout -s KILL 300 gem install -q --no-document prism >/dev/null 2>&1 || echo "ruby-setup: prism failed"
fi
ruby -e 'require "prism"; puts "ruby #{RUBY_VERSION}, prism #{Prism::VERSION}"'
