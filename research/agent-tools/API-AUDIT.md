# Existing API audit

Read-only source review by the API-audit worker; no tests or native admissions
were performed by that review. Runtime evidence is separate in `RESULTS.md`.

- `kernel/prove.ts:274–337,374–433`: synchronous explicit `withBudget` uses counted
  work and suppresses inherited real-wall stops in the reviewed scalar paths.
  `core/trace-clock.ts:1–13` suppresses wall-clock telemetry under that profile.
- `core/work-admission.ts:100–160`: wrap the API body with the existing sticky
  `withCapacityRefusalBoundary` **inside** `withBudget`. Otherwise broad internal
  catches can swallow a genuine admission refusal. This does not create another
  budget or reset counters.
- `core/work-admission.ts:17–23,172–178,233–255,324–328`: snapshot before/after and
  report exact rational actual-work/counter deltas. Root metadata is restored on
  exit, so save the baseline. `core/work-profile.ts:1–29` remains provisional, not
  a universal CPU/RAM guarantee.
- `core/infer.ts:679–714,789–790,919–978,1306`: untimed inference inside the root
  uses counted heuristic stops. `runs`, `ms` and `maxCandidates` are engine hints,
  not independent exact grants or total-candidate caps. The outer work/API limits
  remain authoritative.
- `core/infer.ts:3425–3499`: helpers may be mutually inductive. Check requested
  laws plus the returned helper support jointly. There is no rejected-candidate
  API: caller-supplied near misses can be checked by the existing search.
- `core/machine.ts:1372–1424`: interpreter-checked search is length-first in its
  finite domain. Explicit scalar upper bounds up to15 can override the default
  range. Do not claim global minimality or infer truth from no bounded trace.
- `core/compose.ts:99–142`: `refinement` + `agree` builds directional obligations.
  Check both invariant laws and request-admissibility step laws. The relation is
  implementation → specification under the implementation precondition.
- `core/machine.ts:383–413`: existing interpreter checks reject numeric overflow.
  Preserve these as typed refusal/unknown, never as fabricated negative evidence.
- `core/sample-step.ts:12–15` → `core/machine.ts:1082–1125`: the existing engine may
  JIT validated generated AST. Client source strings remain forbidden, but this
  is not a literal no-eval/CSP guarantee.

The adapter deliberately does not implement alternate proof/search/refinement
logic, native-evidence validation, source equivalence or a new cost model.
