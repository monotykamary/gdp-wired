# jev-fabric's laws in gdp-wired

[jev-fabric](https://github.com/fabric-runtime/jev-fabric) is written in Bend, and its four proof roots
(`native/tests/proofs.bend`, `policy-proofs.bend`, `time-proofs.bend`, `decision-proofs.bend`) prove **59** laws about
its policy core: budgets, timeouts, monitors, job queues, the store marker, spool reads, decision profiles. This example
ports that core to gdp-wired's builders and states the same 59 laws over it. **All 59 are proven automatically**, each
proof accepted by the kernel and exported to Lean; none needed an added invariant, relation or fact. Each has a
deliberately broken variant that the kernel refuses and a real run or draw breaks. Fourteen more laws, over runs, which
the Bend proofs don't state, are proven too.

```sh
bun examples/jev-fabric/run.ts           # prove all 73; random runs; every broken variant refused and broken (5 s)
bun examples/jev-fabric/run.ts --lean    # every law as a Lean theorem, to compile in lean-kernel/
```

| File | What |
| --- | --- |
| `policy.ts` | The port. Each pure Bend function is a `fun` (its laws are decisions about the terms it returns, and `run` is those terms compiled); seven `rule`s are machines over runs; the broken variants are `bug` arguments |
| `laws.ts` | The 59 Bend laws, each with its broken variant, and the 14 extras |
| `run.ts` | Proves each, times it, and runs `examples/harness.ts`'s triple check: the kernel accepts the proof; the interpreter and the compiled JavaScript agree on random runs and keep the law; the broken variant is refused and broken |

## What the port takes

No law needs induction once ported. The induction in the Bend proofs is either over naturals, which gdp-wired has built
in (`Spool.minus` is a recursive ∸, `Spool.from` a recursive max, `Nat.is_ge` a comparison), or over strings and lists
that the laws only pass through. What is left is the encoding:

- Nat is a natural, U32 a natural at most 2^32 − 1, Bool a bit, a Bend enum a `oneOf`, Maybe a `maybe`.
- A string the law treats as a value (a label, a key, a URL, a profile name) is a name interned to a natural, assumed
  injective; a possibly empty string is `maybe(name)`, "" being none.
- A string or list computation the law does not read (trim and contains, JSON parsing, the UTF-8 hold-back, the HTTP
  status parse) is the runtime's answer, an input, as gdp-wired takes a history's query.
- A JSON object is a map from interned key to value id.

These encoding facts are not proven here. The port was compared with the real Bend functions, called through Bend's bun
loader, on 70,058 sampled outcomes across 43 functions, and all agreed; that comparison needs both checkouts and is not
part of this repository.

## Counts

| | Laws |
| --- | --- |
| In the four proof roots |
| Proven automatically, as stated (or stronger) | **59** |
| Broken variant refused by the kernel | 59 / 59 |
| Broken variant broken by a run or draw | 55 by random runs and draws, 4 at a given witness (12, 46, 56, 57: values past 2^32, a 1024-line state, maps holding values) |

By shape: 52 decisions about a function (`law`), 1 decision about two calls (55, `relate`), 2 step laws (16, 42), 1
two-step law (41), 3 laws over maps of names (54, 56, 57). By encoding: 27 exact (numbers, enums, bits), 19 with
strings interned as names, 13 with a string or list computation taken as the runtime's answer.

Some are stated more generally than in Bend: 16 at any cap and batch size, 41 and 42 over any run of the queue, 54 for
any request with a provider and no profile (Bend: the one-member request), 56 and 57 at every key, whatever else the
objects hold. Three have a stronger form among the extras: 7 and 8 at any spent tokens (Bend fixes 0 and 1), and 36 as
`= left` (Bend states `min(left, left)`, which it cannot reduce without a lemma).

**Extras**: 14 laws over runs, all proven; 10 automatically, 3 with an added invariant (each an implication, flag ⇒
bound), 1 with an added function fact. Among them, the aggregate monitor bound: over any sequence of pushes a channel
emits at most total_max lines.

## Every law

Encoding: **exact**: numbers, enums (oneOf), bits and Maybe only; **interned**: strings as names (injective), "" as a
maybe-name's none, fixed messages as their index; **abstracted**: a string or list computation the law does not read is
the runtime's answer (an input), as gdp-wired takes a history's query.

| # | Law | What it says | Bend functions | In gdp-wired | Encoding |
| --- | --- | --- | --- | --- | --- |
| 1 | `exhausted_never_reserves` (proofs) | a budget with no evaluations left reserves nothing | Core.reserve | decide | exact |
| 2 | `cancelled_is_terminal` (proofs) | settle(Cancelled, result) = Cancelled: a Cancelled job ignores later results | Core.settle | decide | exact |
| 3 | `completed_is_terminal` (proofs) | settle(Completed, result) = Completed: a Completed job ignores later results | Core.settle | decide | exact |
| 4 | `unknown_requires_inspection` (proofs) | an Unknown receipt asks for inspection | Core.after | decide | exact |
| 5 | `dispatch_requires_verification` (proofs) | an Executed receipt asks for verification | Core.after | decide | exact |
| 6 | `denied_reservation_has_no_budget` (policy-proofs) | reserve_if(..., False) is None | Core.reserve_if | decide | exact |
| 7 | `reservation_consumes_one` (policy-proofs) | with one evaluation and token limit 1 at 0 spent, a reservation uses exactly one evaluation | Core.reserve | decide | exact |
| 8 | `zero_token_budget_blocks` (policy-proofs) | token limit 0 blocks a reservation | Core.reserve | decide | exact |
| 9 | `accounting_never_refunds_a_call` (policy-proofs) | account adds the reported tokens and leaves the rest | Core.account | decide | exact |
| 10 | `failure_is_terminal` (policy-proofs) | settle(Failed, result) = Failed: a Failed job ignores later results | Core.settle | decide | exact |
| 11 | `timeout_is_terminal` (policy-proofs) | settle(TimedOut, result) = TimedOut: a TimedOut job ignores later results | Core.settle | decide | exact |
| 12 | `terminal_monitor_never_polls` (policy-proofs) | a terminal watch stops as finished | MonitorCore.terminal_decision | decide | interned: Stop{"finished", True}: the reason string is one of three, a oneOf |
| 13 | `limited_monitor_never_polls` (policy-proofs) | an output-limited watch stops | MonitorCore.limit_decision | decide | interned |
| 14 | `expired_monitor_never_polls` (policy-proofs) | an expired watch stops | MonitorCore.deadline_decision | decide | interned |
| 15 | `disabled_filter_emits_nothing` (policy-proofs) | a disabled filter emits nothing, whatever the text | MonitorCore.limited_match, Core.monitor | decide | abstracted: Core.monitor (trim, contains, equality on strings) is the runtime's answer `hit`; the law does not read it |
| 16 | `full_channel_cannot_emit` (policy-proofs) | a push to a channel at its 1024-line cap changes nothing and emits nothing | MonitorCore.push, accepted, finish_push, flush | step law | abstracted: push is the step of a channel machine (total = total_max() as a param, 1024 in jev-fabric); line strings interned, the string tests the runtime's answer; pending lines kept as their count |
| 17 | `encoding_without_fuel_fails` (policy-proofs) | encoding any JSON value with zero fuel fails with code 22 | JSON.write_with_fuel, JSON.encode.go | decide | abstracted: the JSON value is a name; one expansion step (string work) the runtime's answer |
| 18 | `rejected_http_has_no_request` (policy-proofs) | rejected HTTP configuration makes no request plan | HttpCore.request_allowed | decide | interned |
| 19 | `rejected_credential_exposes_no_key` (policy-proofs) | a rejected credential is a fixed error that carries no key | CredentialCore.checked | decide | interned |
| 20 | `failed_transport_rejects_bytes` (policy-proofs) | failed or truncated transport rejects its bytes | HttpCore.capture_ok | decide | abstracted: the bytes are a name; the status parse the runtime's answer |
| 21 | `reported_overshoot_disables_calls` (policy-proofs) | an oversized usage report zeroes the evaluations and saturates the tokens at limit + 1 | JevCore.add_usage | decide | interned |
| 22 | `invalid_typed_reply_stays_failed` (policy-proofs) | an invalid typed reply leaves the client as it was and fails | JevCore.response_ready | decide | abstracted |
| 23 | `receipt_finishes_follow` (policy-proofs) | a terminal receipt finishes a follow, ceiling or not | JobsCore.follow_decision | decide | exact |
| 24 | `expired_follow_without_receipt_times_out` (policy-proofs) | a follow past its ceiling without a receipt expires | JobsCore.follow_decision | decide | exact |
| 25 | `followed_event_is_never_repeated` (policy-proofs) | an event at or before the cursor prints nothing and keeps the cursor | JobsCore.fresh | decide | interned |
| 26 | `newer_store_is_refused` (policy-proofs) | a home of store format 2 or more is refused with newer(shown) | StoreCore.versioned | decide | interned |
| 27 | `current_store_is_accepted` (policy-proofs) | a home of store format 1 is accepted | StoreCore.versioned | decide | interned |
| 28 | `writer_adopts_unmarked_home` (policy-proofs) | a writing verb adopts an unmarked home | StoreCore.missing | decide | exact |
| 29 | `reader_leaves_old_home_unmarked` (policy-proofs) | a read-only verb leaves an old unmarked home unmarked | StoreCore.missing | decide | exact |
| 30 | `minus_self` (policy-proofs) | Spool.minus(n, n) = 0 (by induction in Bend) | SpoolCore.minus, less | decide | exact: minus is ∸ here; that SpoolCore.less is ∸ is a fact of the encoding (an induction), held by the differential test |
| 31 | `read_from_start_discloses_loss` (policy-proofs) | a read from offset 0 discloses every byte below the window as omitted | SpoolCore.span, from, minus | decide | exact |
| 32 | `nothing_lost_nothing_omitted` (policy-proofs) | with nothing lost a read omits nothing, at every offset | SpoolCore.span, from, minus | decide | exact |
| 33 | `ended_stream_holds_nothing_back` (policy-proofs) | an ended stream returns every byte | SpoolCore.kept | decide | abstracted: kept returns a prefix (List.take); the bytes as their length, the UTF-8 hold-back (a walk over the list) the runtime's answer |
| 34 | `long_poll_answers_at_its_ceiling` (policy-proofs) | a long poll past its ceiling answers | SpoolCore.answer_now | decide | exact |
| 35 | `session_child_is_cut_to_its_connection` (policy-proofs) | a session child lives min(requested, left) | ServeCore.child_lifetime | decide | exact |
| 36 | `session_child_defaults_to_its_connection` (policy-proofs) | with no request a child lives min(left, left) | ServeCore.child_lifetime | decide | exact |
| 37 | `closed_queue_refuses_writes` (policy-proofs) | ended input refuses every write | JobsCore.admit | decide | exact |
| 38 | `queue_admits_up_to_its_bound` (policy-proofs) | a queue filled exactly to its bound is admitted | JobsCore.admit, Nat.ge_refl | decide | exact |
| 39 | `past_bound_is_not_within` (policy-proofs) | Nat.is_ge(max, max + 1 + over) is false (by induction in Bend) | Nat.is_ge | decide | exact: for every max, over ⇔ for every a, b ≥ a + 1 |
| 40 | `queue_refuses_past_its_bound` (policy-proofs) | one byte past the bound is refused | JobsCore.admit | decide | exact |
| 41 | `queue_keeps_arrival_order` (policy-proofs) | drained(push(push(empty, a), b)) = a ++ b | JobsCore.push, drained, empty_queue | k-step law | abstracted: a queue is a list of chunks (each write interned as a name); a 2-step law from an empty queue: position 0 holds the first write, 1 the second. String concatenation of the chunks is the encoding |
| 42 | `draining_empties_the_queue` (policy-proofs) | drained(emptied(q)) = "" | JobsCore.drained, emptied | step law | abstracted: a drain is a step of the queue machine: no chunk and no byte left after it |
| 43 | `denied_timeout_never_becomes_a_limit` (time-proofs) | checked(ms, False) is the fixed timeout error | TimeCore.checked | decide | interned |
| 44 | `omitted_configuration_uses_default` (time-proofs) | config("", fallback, max) is Done{fallback} | TimeCore.config | decide | abstracted: the raw string: empty or not; parse(raw, max) the runtime's answer |
| 45 | `elapsed_time_is_subtracted_not_renewed` (time-proofs) | remaining(Budget{start, duration}, now) = duration ∸ (now ∸ start) | TimeCore.remaining | decide | exact |
| 46 | `local_cap_is_applied_before_narrowing` (time-proofs) | cap(left, local) = U32.from_nat(min(left, local)) | TimeCore.cap, U32.from_nat | decide | exact: U32.from_nat is x mod 2^32 (modBy), known by its facts |
| 47 | `duplicate_timeout_is_rejected` (time-proofs) | a second timeout is rejected | Cli.unique | decide | interned |
| 48 | `rejected_label_is_never_stored` (time-proofs) | a rejected label is the fixed error, never stored | Cli.label_allowed | decide | interned |
| 49 | `serve_connection_may_last_a_day` (time-proofs) | Cli.max("serve") = 86400000 | Cli.max | decide | interned: the command string as a oneOf of the four literals and "other" |
| 50 | `explicit_profile_wins` (decision-proofs) | a nonempty explicit profile is chosen | DecisionProfiles.choose_profile, DecisionConfig.fallback | decide | interned: strings as maybe(name): "" is none, so SCon{head, tail} is some |
| 51 | `explicit_provider_suppresses_profiles` (decision-proofs) | an explicit provider without an explicit profile chooses none | DecisionProfiles.choose_profile | decide | interned |
| 52 | `ambient_profile_wins_over_default` (decision-proofs) | an ambient profile beats the document default | DecisionProfiles.choose_profile | decide | interned |
| 53 | `absent_selectors_use_document_default` (decision-proofs) | with no selectors the document default is chosen | DecisionProfiles.choose_profile | decide | interned |
| 54 | `explicit_provider_bypasses_document` (decision-proofs) | an explicit-provider request bypasses every document entry | DecisionProfiles.apply_document, selector, choose_profile, selected, remove | list/set | abstracted: the request as a map from key to value; stated for every request with a provider and no profile member (Bend: the one-member request); a list search and name checks are the runtime's answers |
| 55 | `explicit_provider_discards_ambient_target` (decision-proofs) | with an explicit provider, changing both ambient values changes nothing | DecisionConfig.configure_explicit | relate | abstracted: noninterference, a decision about two calls: any two ambient pairs give configure the same arguments (configure itself, string validation, is a function of them) |
| 56 | `provider_options_replaced_whole` (decision-proofs) | merging {providerOptions: new} over {providerOptions: old} gives {providerOptions: new} | DecisionProfiles.merge, missing | list/set | abstracted: objects as maps from key to value id; stated at every key where the base is absent, and at providerOptions, whatever else the objects hold |
| 57 | `shadowed_provider_options_are_irrelevant` (decision-proofs) | the shadowed providerOptions subtree does not affect the merge, with any other fields | DecisionProfiles.merge, missing | list/set | abstracted: two merges side by side (Base, BaseB); at every key where the bases agree, and at providerOptions, the merges agree. Member order (equal on both sides, a function of the keys) is left to the encoding |
| 58 | `canonical_idempotent_branch` (decision-proofs) | given canonical(p) = pick(matched, "vercel", p) (twice), canonical is idempotent at p | DecisionConfig.canonical | decide | interned: a helper of the Bend proof (a case split on String.eq); here one decision |
| 59 | `canonical_provider_is_idempotent` (decision-proofs) | canonical(canonical(p)) = canonical(p) | DecisionConfig.canonical | decide | interned: "vercel-ai-gateway" and "vercel" interned at fixed distinct names |

### Extras

| Extra | Bend functions | In gdp-wired | How |
| --- | --- | --- | --- |
| reservation consumes one, at any spent tokens below the limit: the general form of reservation_consumes_one (deliberately not stated in Bend) | Core.reserve | decide | automatic |
| any spent budget blocks a reservation: the general form of zero_token_budget_blocks | Core.reserve | decide | automatic |
| Jev client budget over a run: reserve before a call, report after it: evaluations never pass the cap, nothing is granted after an overshoot, spent tokens never go down | Core.reserve, JevCore.account, add_usage | step law | added invariant (needs "a call in flight was reserved under the token limit" and "after an overshoot ..." as laws; without the reserve-before-report protocol the saturating add_usage lowers the spent count) |
| monitor channel over a run: over any pushes: at most total_max lines emitted (the aggregate bound jev-fabric's docs/safe-bend.md lists as missing), fewer pending than a batch, the previous line never repeated next | MonitorCore.push | step law | automatic |
| follow over a run: the printed sequence numbers strictly increase: no event is printed twice, at any distance | JobsCore.sequenced, fresh | list/set | added invariant (with "every printed number is at most the cursor" as a law) |
| interactive input queue over a run: the queue never holds more than its bound, ended input stays ended and admits nothing, writes keep arrival order, a drain empties it | JobsCore.admit, push, seal, drained, emptied (as Host applies them) | list/set | automatic |
| a read-only verb never adopts a home it did not create: StoreCore.decide whole: whatever the marker says | StoreCore.decide, marked, missing, parsed | decide | automatic |
| a newer home is refused whatever the verb and whoever created it: StoreCore.decide whole | StoreCore.decide, versioned | decide | automatic |
| a read starts in the window, at or past its offset, and returns at most max bytes, none past count: SpoolCore.span in general | SpoolCore.span | decide | automatic |
| spool reader over a run: every byte below the reader's offset was delivered or disclosed as lost; the reader never passes what was written | SpoolCore.span, oldest (Spool.bend's read loop) | law | automatic |
| a child with no request lives exactly what is left (not just min(left, left)): the form Bend could not reduce without a lemma | ServeCore.child_lifetime | decide | automatic |
| a child never outlives its connection: child_lifetime(r, left) ≤ left for every r | ServeCore.child_lifetime | decide | automatic |
| capping loses nothing to narrowing: cap(left, local) = min(left, local): U32 narrowing never bites | TimeCore.cap, U32.from_nat | decide | added fact (needs the fact x < 2^32 ⇒ x mod 2^32 = x, Lean's Nat.mod_eq_of_lt, which the decision assumes where it reads the function) |
| scope budget over time: as the clock advances, the time left never grows: an elapsed budget is never renewed | TimeCore.remaining (Scope.bend samples it) | step law | added invariant (with "what is left is the duration less the time elapsed" as a law) |

