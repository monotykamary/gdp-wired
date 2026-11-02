#!/bin/bash
# scan.sh <owner/repo> : clone at HEAD (depth 1), run the CLI on candidate files, print one line per file
set -u
repo=$1; root=$(pwd); work=/tmp/scan-$$; mkdir -p $work
git clone -q --depth 1 https://github.com/$repo $work/r 2>&1 | tail -2
cd $work/r; echo "COMMIT $repo $(git rev-parse HEAD)"; echo "LICENSE $(head -c 300 LICENSE* 2>/dev/null | tr '\n' ' ' | cut -c1-120)"
find . -type f \( -name '*.py' -o -name '*.ts' -o -name '*.js' -o -name '*.go' -o -name '*.java' -o -name '*.kt' -o -name '*.rb' \) \
  -not -path '*/node_modules/*' -not -path '*/test*' -not -path '*/spec/*' -not -path '*/dist/*' -not -path '*/build/*' -not -path '*/migrations/*' -not -path '*/vendor/*' -not -path '*/mock*' -not -path '*/e2e/*' -not -path '*/examples/*' -not -path '*/docs/*' \
  -not -name '*_test.go' -not -name '*.test.*' -not -name '*.spec.*' -not -name '*.d.ts' -not -name 'test_*' -not -name '*Test.java' -not -name '*.min.js' \
  | grep -iE 'consent|access|permission|expir|retention|audit|deadline|due|privacy|polic|scope|session|token|lock|grant|revok|breach|request|claim|auth|limit|throttl|sla|schedule|elig|opt' \
  | while read f; do n=$(wc -l < "$f"); [ "$n" -gt 700 ] && continue; [ "$n" -lt 15 ] && continue
    out=$(cd $(dirname "$f") && perl -e 'alarm 90; exec @ARGV' bun $root/core/cli.ts check $(basename "$f") --json --no-propose --ms 2000 2>/dev/null | python3 -c "
import json,sys
try:
  d=json.load(sys.stdin)
  for r in d['rules']: print(('OK ' if r['ok'] else 'NO ') + str(r.get('entry')) + ' ' + ('' if r['ok'] else json.dumps(r['refusals'][:1])[:220]) + (' | ' + ', '.join(n['code'] for n in r['names'][:14]) if r['ok'] else ''))
except Exception as e: print('ERR', str(e)[:80])
" | head -3)
    echo "$out" | sed "s|^|FILE $n $f :: |"
  done
rm -rf $work
