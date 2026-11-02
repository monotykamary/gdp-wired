#!/bin/bash
# scan-functions.sh <owner/repo> : every top-level Python function of candidate files read as a decision (--entry fn)
set -u
repo=$1; root=$(pwd); work=/tmp/scan2-$$; mkdir -p $work
git clone -q --depth 1 https://github.com/$repo $work/r 2>&1 | tail -2
cd $work/r; echo "COMMIT $repo $(git rev-parse HEAD)"
[ -f requirements.txt ] && pip install -q -r requirements.txt > /dev/null 2>&1
n=0
find . -type f -name '*.py' -not -path '*/test*' -not -path '*/migrations/*' -not -name 'test_*' -not -name 'conftest.py' -not -path '*/docs/*' \
  | grep -iE 'consent|access|permission|expir|retention|audit|deadline|due|privacy|polic|scope|session|token|lock|grant|revok|breach|request|claim|auth|limit|throttl|sla|elig|opt|util|deid|scrub|mask|filter' \
  | while read f; do
    for fn in $(grep -oE '^def [A-Za-z_][A-Za-z0-9_]*' "$f" | awk '{print $2}' | head -15); do
      out=$(cd $(dirname "$f") && perl -e 'alarm 60; exec @ARGV' bun $root/core/cli.ts check $(basename "$f") --entry $fn --json --no-propose --ms 1000 2>/dev/null | python3 -c "
import json,sys
try:
  d=json.load(sys.stdin)
  for r in d['rules']: print(('OK ' if r['ok'] else 'NO ') + str(r.get('entry')) + ' ' + ('' if r['ok'] else json.dumps(r['refusals'][:1])[:200]) + (' | ' + ', '.join(n['code']+':'+n['role'] for n in r['names'][:12]) if r['ok'] else ''))
except Exception as e: print('ERR', str(e)[:80])
" | head -1)
      echo "FN $f $fn :: $out"
    done
  done
rm -rf $work
