# Go / Ruby / Elixir fixture migration — source only, native acceptance BLOCKED

## Operational scope / evidence

- Published base `ae631359ebeff39d115edfbe7329647c7510714c`; exact pins verified locally: gdp-ts `0b6ebeeec827b05210f3acfa4149a70dda9a0de5`, handwired `d47141cce2caf5b86b0c2c0c372a5174f424bc15`.
- Clean fast-forward to Main-requested `d1fc81507` before edits. No history rewrite/push/tag/version or failure-policy change.
- Own three test files plus specifically approved `core/rb/harness.rb`, `core/ex/harness.exs`, isolated `research/bapa/0503-fixtures-go-rb-ex/` diagnostics/docs. No edits to shared checker/parser/finalizer/CLI/DSL/infer/kernel files.
- **No snapshot, test, build, lint, proof, benchmark or native admission launched. Admission hold respected.** Only source inspection/editing and `git diff --check` (whitespace) performed. No native PASS claimed; no owned jobs, batches, tasks, waiters or leases pending.
- Jobs `extract-go`, `extract-rb`, `extract-ex`: **BLOCKED / NOT CLOSED**, not new known-failure allowances. The original full246 receipts under `/tmp/bapa-release-0502-final-ae631359e/runs/admission-1/full-246/{extract-go,extract-rb,extract-ex}.files/` remain untouched. No fresh native logs, placement or custody exist because no admission is authorized.
- First source commit: `eefcaaca1` (`test(extract): pair Go Ruby and Elixir laws with native observations`); T3-approved nil-Grow and reflection followup recorded in final control handoff. This document is not a successful release-gate receipt.

## Exact public assertion contract

All **37** original callback claims (Go25, Ruby7, Elixir5) retain their exact callback body and guard. **36** have paired native companions (Go24, Ruby7, Elixir5); **Grow has explicit T3-approved panic-only disposition**: original checked mathematical callback + exact unregistered-law source refusal, registered nil-Grow exact no-observation refusal, concrete original-source nil-panic replay, and a deliberately separate initialized native-positive companion. No original-source public-positive requirement is left falsely claimed. Every original callback now requires `kernelProven:true`, `proven:false`, `checked:false`, `translation:'unchecked'` and exact reason `source translation unchecked: a source proof contains a law with no native interpretation`. `kernelProven` preserves incoming proven AND checked mathematical evidence. A callback is not independently native-interpretable. EVERY paired callback also has the same-property registered `buildLaw` companion, requiring public `proven:true`, `checked:true`, `translation:'sampled'` and `translationChecks>0`. A missing/unavailable/failing companion fails the test; no generic positive substitutes. No callback is retired solely on an unknown/refusal.

All existing extraction/native replay checks (`ok`, requests>0, no mismatch, arm coverage), independent Go clock replay, overflow, nil, aliasing, atomic/defer, constructor, panic/error/discard, broken-model, compiler-failure and adversarial assertions remain in place. Original skip conditions unchanged; no new failure allowance.

## Go: old mathematical claim -> original-source expression/binding

Every row is SOURCE-DRAFTED, RUNTIME-UNVERIFIED, blocked on shared actual Go observation adapter and targeted admission.

| Original callback claim | Equivalent registered expression | Binding / distinction |
|---|---|---|
| onRequest at 2^32−1 wraps to0 | `old(Requests)==4294967295 implies Requests==0` | onRequest, uint32 unchanged |
| onRequest below 2^32−1 adds1 | `old(Requests)<4294967295 implies Requests==old(Requests)+1` | onRequest |
| validRequests_result<=Requests invariant | `result<=Requests` | validRequests; exact reset argument below, NOT retained output history |
| int8 127+1==-128 | `old(A)==127 implies A==-128` | IncA |
| uint16 0−1==65535 | `old(B)==0 and d==1 implies B==65535` | SubB_d -> actual d, SubB |
| int32 2^30*2==-2^31 | `old(C)==1073741824 implies C==-2147483648` | Twice |
| Take never N<0 | `N>=0` | Take, uint64 underflow refusal retained |
| Net_nil or Net==Credit−Debit | `Net==nil or Net==Credit-Debit` | explicit numeric-value projection of *big.Int arithmetic; nil->null; NOT pointer equality |
| copied pointer sets N=5 | `N==5` | ViaPointer |
| copied struct leaves N, sets M=7 | `N==old(N) and M==7` | ViaCopy |
| interior pointer increments Sub_X | `old(Sub.X)<1000 implies Sub.X==old(Sub.X)+1` | Sub_X -> original Sub.X, ViaInterior |
| selected pointer sets M, leaves N | `c implies M==1 and N==old(N)` | ViaChoice_c -> actual c, ViaChoice |
| Bump on nil Seen is refused | `old(Seen)==nil implies false` | Bump; statement over admitted calls, original panic check preserved |
| Check negative v is refused | `v<0 implies false` | Check_v -> actual v, Check |
| Grow nil X is refused | `old(X)==nil implies false` | **T3-approved honest native refusal**: X always nil; exact `no native observation of Grow` + checked kernel evidence. Concrete original P replay must panic. Separate Initialized.Init/Grow companion requires registered `X!=nil` proven+checked/checks>0; tamper and disabled controls. Not presented as same fixture. |
| Move preserves nonnegative N | `old(N)>=0 implies N>=0` | Move, original post-write error/discard controls retained |
| Used<=Limit or Used==0 invariant | `Used<=Limit or Used==0` | all states/methods; no narrowing to Take; real source context params may honestly block observation |
| refused Take leaves N | `not o.Allow implies N==old(N)` | Take_o_Allow -> actual original argument o.Allow, Take |
| −7/2==-3 | `old(N)==-7 implies N==-3` | Half |
| −7%3==-1 | `old(N)==-7 implies N==-1` | Rem |
| int8(200)==−56 | `v==200 implies B==-56` | Narrow_v -> v, Narrow |
| uint8(−1)==255 | `v==-1 implies U==255` | Unsigned_v -> v, Unsigned |
| Hit increments Counts_Requests under original bounds | `old(Counts.Requests)<100 and old(Age)<100 implies Counts.Requests==old(Counts.Requests)+1` | original nested field Counts.Requests, Hit |
| Copy leaves Counts_Requests | `Counts.Requests==old(Counts.Requests)` | Copy |
| Used<=Cap preserved | `old(Used)<=old(Cap) implies Used<=Cap` | ALL methods including Left, no method narrowing |

### validRequests equivalence argument (static, not a native proof receipt)

`core/extract-go.ts:717` describes results as their default at other steps. The actual output-write loop at **769–775** sets `init[o]=0` for numeric results, starts `acc=init[o]`, and each selected method uses its output only if it owns o; otherwise `init[o]`; then `writes[o]=acc`. Thus initial and every non-validRequests state have `validRequests_result=0`. Requests is uint32 (nonnegative even after wrap), so the original invariant there is `0<=Requests`. After validRequests, the model output is precisely that method's actual return, so its original invariant is exactly `result<=Requests`. These exhaustive cases justify the mapped native method law while preserving the original checked invariant. We initially suspected retained history, found contrary source evidence, and did NOT silently assume equivalence. If output-reset semantics change, this argument and companion must be revisited.

*big.Int fields project the numeric values used by original Add/Sub/Cmp code and mathematical callbacks. A source pointer==pointer property is unsupported; the number transport is not pointer identity. Existing big.Int aliasing controls remain refused.*

## Ruby: old math -> original-source expression/binding

Every row SOURCE-DRAFTED/RUNTIME-UNVERIFIED. All require the shared observed-answer bridge/raises alias review and targeted native admission.

| Original callback claim | Equivalent registered expression | Original binding |
|---|---|---|
| admitted hit increments count | `old(limit)>old(count) implies count==old(count)+1` | hit; count/limit actual instance vars |
| seen_p_result iff !last_none | `result==(old(last)!=nil)` | seen? result, actual @last read (uninitialized Ruby ivar genuinely reads nil) |
| half+half+rest==split_k | `half+half+rest==k` | split_k -> actual entry k, split |
| !failed implies cache_hits[user.id].value<=cap_ | `not failed implies cache["hits:"+user]<=cap` | actual cache Hash at original key, actual user string/cap field; no symbolic id stamped as key |
| errors increases only on ping_raises StandardError | `errors>old(errors) implies Remote.ping.raises=="StandardError"` | hit, genuine raised runtime class; dotted alias Main-owned |
| n increases only if cap_>old n | `n>old(n) implies old(cap)>old(n)` | all methods, cap_ -> actual cap field |
| soft errors increase only on soft_ping_raises | `errors>old(errors) implies Remote.ping.raises` | soft, method-aware alias must select its own boolean symbolic variable; actual raised class truthy / returned null false; comparing this nonoptional bool with nil would be unsupported |

Ruby observation type/class/identity/string-copy/container-reader intrinsics are bound before source load, so source methods named nil?, instance_of? or class do not impersonate observations; controls cover these shadows. Ruby TracePoint(:call) matches real receiver, bound owner and original method name; reads real method entry locals after defaults/keywords are bound, before body mutation. Binding snapshots are encoded immediately; mutable strings copied. Actual object instance variables supply state (source roots absent before first assignment are read through Ruby's actual instance_variable_get nil semantics). Injected store exposes its actual executed Hash, including actual keys, not modeled cells. References are strongly retained with identity Hash; cycles/aliases get refs. Unsafe/nonintegral numbers, opaque native objects, unsupported map keys/defaults/bounds refuse rather than substitute values. Enum Symbols cross as labels, never DSL indexes. Container equality is structural in Ruby, so `nativeEquality:'scalar'` is mandatory; preserved transport identity alone does not authorize container ==.

## Elixir: old math -> original-source expression/binding

Every row SOURCE-DRAFTED/RUNTIME-UNVERIFIED, blocked on shared equality/observation plumbing review and targeted admission.

| Original callback claim | Equivalent registered expression | Original binding |
|---|---|---|
| open counter below limit increments | `old(mode)==:open and old(limit)>old(count) implies count==old(count)+1` | hit |
| closed counter unchanged | `old(mode)==:closed implies count==old(count)` | hit |
| reset reopens | `mode==:open` | reset |
| half+half+rest==split_k | `half+half+rest==k` | split, actual k from original source function head |
| used<=cap preserved | `old(used)<=old(cap) implies used<=cap` | all methods, original guard retained |

Elixir state is read directly from the actual struct/GenServer/Agent state, not model Snap. Original AST function-head variables determine captured request names; injected first-body instruction sees real pattern-bound/defaulted values. Shared ETS records binding frames from the GenServer process; main protocol labels are not substituted. Pids/functions/refs/tuples, unsafe/nonintegral numbers, unsupported keys/binaries/native structs/bounds refuse. Immutable values get fresh occurrence IDs, never identity invented by value equality. `nativeEquality:'scalar'` MUST be propagated by Main and reject container equality/key-membership claims; no JS identity proof of BEAM structural equality is claimed.

## Shared source review / remaining blockers

Main integration `5a20b9d8b` read directly (no dirty-tree cherry-pick). Central `extract-step.ts` capability gate, invocation validator and frozen observation rows align with this agreed wire. Dotted raise names and C/JVM method-aware answer resolution now source-integrated, not runtime-verified. Go actual nested state/reflect typed parameter captures reviewed for original `Sub.X`, `Counts.Requests`, `o.Allow`, nil maps and numeric big.Int values. No source adapter edits here.

- **Grow approved panic-only classification**: T3 reviewed test intent/history (explicit panic/nil big.Int/refusal). Original P source is unchanged; its exact callback still requires checked kernel proof and exact source refusal, its registered law requires exact `no native observation of Grow`. A genuine independent `go run` of original P.Grow on nil must exit1 with nil-pointer panic and math/big.Add stack; test exports source/stdout/stderr/COMMAND-RESULT under `nil-grow-replay/`, distinct expected-negative custody. Separate Initialized source first has Init set X to big.NewInt(0), then Add Grow can succeed. Registered `X!=nil` on Grow must publicly prove+check with sampled native checks>0; false-lowered `X==nil` must translation-error with Grow native witness; disabled replay must exact-refuse. No unrelated Check observation and no fabricated successful nil Grow. Runtime still unverified.
- **Bump nil map**: Main nil-presence-only native equality exception and C/JVM `e57e49a78` map Name.none lowering reported source-fixed in correct old/current env. No structural map equality or type alias workaround. Await assembled source review and native receipt.
- **Shared consumer mandatory**: both foreign harnesses advertise scalar-only container equality; Main must propagate and enforce this before acceptance. Dotted raises and observed actual call map must be integrated; old d1fc baseline alone will not run all drafted positives.
- **Admission hold**: all three jobs remain NOT CLOSED; no source-only report is native evidence.

## Agreed actual observations wire

Both harnesses advertise `nativeSnapshot:1`, `nativeBindings:1`, `nativeObservations:1`, `nativeEquality:'scalar'`. Actual calls return `nativeObservations:{snapshot:<native-wire-v1>}` or `{error:string}`. Frame is `{invocation:<positive increasing safe integer>, calls:{[actual canonical external key]:{kind:'returned',value:<actual scalar>}|{kind:'raised',raised:<actual runtime class string>}}, clock?:<actual read integer>}`. Per-invocation reset; uncaptured keys stay absent; conflicting repeated values/outcomes/clock reads mark an error. Returns are captured at occurrence and unsupported values refuse. No CUR/request/proof envelopes copied as observations. Ruby actual subclass names stay subclasses (Full is never relabelled StandardError); inheritance-based claims need explicit ancestry semantics, not handler mapping. Elixir nonexception throw/exit outcomes explicitly refuse observation.

Main owns `source-check.ts`, `native-law.ts`, `extract-check.ts`, `extract-step.ts`: observation consumption/invocation validation/deep freezing, scalar equality fence, `Name.native` metadata, clean `Remote.ping.raises` alias. C/JVM lane owns Go checker/generated harness and capability bridge, goNames list/result aliases, fixed-list law lowering, answer method resolution. No edits to these shared files here. Consumer integration is REQUIRED before considering these native-positive tests accepted.

## New adversarial/native controls (source drafted, never run)

- Each Ruby/Elixir real-source credit law requires public proven+checked/nonzero native checks; corrupted symbolic lowering requires translation:error, checked:false, kernelProven:true with actual n/state native witness. Disabled replay requires exact existing unchecked reason and kernel evidence.
- Ruby direct real-harness omitted-array-default test checks historical pre-call [0]/[1], actual post-state [1]/[2], same real alias identity across frames; tests use existing native decoder/freezing, not manufactured observations.
- Ruby direct opaque Time state requires exact transport refusal; actual external subclass Full retained; following calls distinguish returned nil and unreached/absent; repeated same key returning different values requires exact conflict error.
- Elixir real harness captures genuine omitted n=7 and n=3 even when protocol input label is forged_name; reads actual totals7/10; verifies invocation1/2. Actual answered request numeric string '3' is captured only after conversion as3; unreachable next-call key stays absent despite requested999.
- Existing Ruby rescue fixture now pairs same dotted alias across hit/soft; correct selection is a shared method-resolution dependency, not a guessed model value.

## Held diagnostic/collection plan

`research/bapa/0503-fixtures-go-rb-ex/diagnostic.jobs.json` preserves exact original extract-go/rb/ex commands plus owned-file type-aware lint. Wrappers export native.log, command.txt, COMMAND-RESULT.json through SUPERCOMPUTER_OUTPUT_DIR, require actual output/result capability. No job submitted. Before any admission, Main must authorize recovery, integrate/review dependencies, record effective root and shipped bytes/blob count, keep trees small and required data packed, and choose a targeted interactive job (not full246/strict gate). Collect exact native result codes, manifests, placement and custody, and clean every launched job. Only verified503 scheduler-handoff NOT_STARTED can be resubmitted; LOST is never general retry permission.

## Remaining gaps / honest disposition

1. ALL three jobs remain BLOCKED, not fixed/passed: admission hold prevents native execution, syntax/type/lint/proof/runtime status unverified.
2. Shared Main consumer/raises alias/equality fence + Go owner adapter must integrate. Some unsupported genuine context/state/argument types may retain exact refusal, requiring per-case review rather than generic positive replacement.
3. No native-checked claim can be inferred from a source diff or these planned controls. Known-failure policy remains unchanged. No owned native jobs left pending.
