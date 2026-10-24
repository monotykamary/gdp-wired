"""Every document against interchange/schema.json (JSON Schema 2020-12), with the jsonschema package:
    python3 validate.py <schema.json> <file.json>...
Prints one JSON line: how many were valid, and the first few errors."""
import json
import sys

from jsonschema import Draft202012Validator

schema = json.load(open(sys.argv[1]))
Draft202012Validator.check_schema(schema)
v = Draft202012Validator(schema)
ok, bad, first = 0, 0, []
for f in sys.argv[2:]:
    errs = list(v.iter_errors(json.load(open(f))))
    if errs:
        bad += 1
        if len(first) < 5:
            e = min(errs, key=lambda e: len(list(e.absolute_path)))
            first.append(f"{f}: {'/'.join(map(str, e.absolute_path))}: {e.message[:200]}")
    else:
        ok += 1
print(json.dumps({"valid": ok, "invalid": bad, "first": first}))
