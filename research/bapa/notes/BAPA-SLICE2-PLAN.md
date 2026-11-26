# BAPA slice 2: one uncapped port, separate from fa1748be9

Selected SECTION-63 row 3: `lock_server`, currently fixed at 64 clients and 64 servers, using `client * 64 + server`. Original law: `clientlocks[c1] ∩ clientlocks[c2] != empty => c1 = c2`.

The new opt-in port lives under `research/bapa/`, leaving the canonical registry and slice 1 unchanged. Give it immutable symbolic `clients` and `servers` parameters, use `sizedSort(...).has` for input and law domains, and replace radix packing with the existing native `Link : Client × Server` relation. This port has no quantified transition guard; its sized-sort use is membership, not an artificial unused finite enumeration. Positive multi-sort laws remain ordinary universal laws with explicit domain guards, as in slice 1's conservative elaboration.

Prove the original uniqueness law together with the ordinary inductive helper `Link(c,s) => not Semaphore(s)`, at arbitrary symbolic sizes, with the uncounted `proveLaws`/`checkLaws` path (ordinary trees, using the existing fallback when the fast memo cannot be reused). No counts, no fixed-domain instance, no raw-work increase disguised as a proof. Export actual ordinary machine certificates to Lean. Mutant: connect without semaphore; concrete double-acquisition counterexample and old proof rejected on the mutant.

Validate all 9 reachable states and all 8 requests per state against the original 2×2 port through an explicit radix/native tuple projection. Also run zero-size exclusion and clients/servers above 64. Finite examples establish runtime correspondence only; the symbolic checked proof establishes the law.

Fable review (SECTION-75.5): label the helper **given, not found**; run a separate no-given-helper search and report it honestly; also prove the unguarded stronger uniqueness law. This port does not exercise finite quantifier enumeration. It demonstrates that existing native tuple keys remove the cap where the source never reads a sort whole. A first-coordinate quantified guard in another port would be the actual finite-enumeration test, not claimed here.

Next needed SECTION-64 piece is tuple-keyed state relations. Reuse the existing injective native tuple semantics and Lean correspondence; do not add another packing convention or invent a rigid-symbol rule when this port does not need one. Record any actual missing API or proof support before changing trusted code. Ask Fable to review selection/scope; D reviews any trusted change (none planned).

Keep fa1748be9 reviewable. This migration and evidence will be new commits. Continue slice-1 canonical packet work after D's static review and a fresh packet authorization; never reuse the consumed section71 packet/group/GO.
