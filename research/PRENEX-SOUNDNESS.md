# Nested universal prenexing: DSL encoding soundness

## Reproducer and affected versions

A valid rule starts with map `M` defaulting to zero and handles `{k, v}` by setting `M[k] = v`. After `{k: 0, v: 1}`, `M[0] = 1` and `M[1] = 0`.

The user's law `everyKey(a => everyKey(b => M.at(a).atMost(M.at(b))))` is false at `a=0,b=1`. On the frozen `c08bb385b`, current main `f95f306d0`, and 0.50.1 candidate `ddc82e9a0`, `proveRule` nevertheless reports `{proven:true, checked:true}`. Native probes also reproduce this on 0.46.0 `2df09b1af`, 0.47.0 `40693c7a2`, and 0.49.0 `9983eada4`. Main identified introduction commit `005b72c75`, first released in 0.3.0. No further release bracketing is required.

## Exact encoding error

`prenex()` previously substituted *each* positive universal's binder with the same generated law key. The two independent variables therefore became:

```json
{"name":"nested-map-false","forall":"key$1","holds":{"op":"<=","a":{"op":"get","map":"M","key":{"op":"var","name":"key$1"}},"b":{"op":"get","map":"M","key":{"op":"var","name":"key$1"}}}}
```

This is `forall k, M[k] <= M[k]`. The kernel correctly checks that tautology, **not the user's statement**. The correct explicit two-key form, `forall((a,b) => M.at(a).atMost(M.at(b)))`, is refuted with a real one-request run.

Raw nested `all` in a Machine or a Law is rejected by existing kernel scope admission. That rejection did not protect the DSL's earlier lossy prenexing.

## Lean evidence

On unchanged `c08bb385b`, `toLean(...,{native:false,cyclic:false})` emits:

```lean
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat)
  (h : SReach nested_probe_machine ρ μ) :
  ∀ k : Nat, (μ «M» k) ≤ (μ «M» k) := ...
```

Lean 4.34.0 accepts it. In the same file Lean also proves that `forall a b, explicitCounterMap a <= explicitCounterMap b` is false, where the map is 1 at 0 and 0 elsewhere. Exported `nested_probe_laws` uses only `propext`, `Classical.choice`, and `Quot.sound`; the counterexample uses `propext`. There is no native-decide or added axiom.

Receipt: batch `20261116-125200-jyk5uq`, fetched at sibling worktree `gdp-wired-rulefirst/runs/rule-first/soundness-lean-fetched/`; source, `lean.log`, and `law-verdict.json` are retained. This is a DSL encoding bug, not evidence of a false-certificate acceptance by the kernel or Lean.

## Conservative fix

- Refuse a positive universal nested on the same path under another positive universal. Direct users to `forall((i, j) => ...)`.
- Apply that rule to invariants, step laws, and multi-step laws, including an outer explicit `forall`.
- Preserve sibling universals under conjunction; sharing their binder is sound.
- Replace JSON-text binder substitution with lexical AST substitution, respecting inner shadowing and refusing capture by an inner binder.
- Refuse a generated law key that would capture a free user variable anywhere in the original condition.
- Export `QuantifierAdmissionError` with stable `nested-universal` and `binder-capture` codes.

No kernel, Lean checker, axiom, reader, or emitter changes are included in this fix branch. Nested-universal support is deferred rather than approximated.

Regression tests: `core/prenex-admission.test.ts`. Source audit: `research/prenex-audit.ts` (syntactic candidates, not automatic vulnerability classifications).

The source audit inspected 633 TypeScript files and returned 35 candidate call nestings. No pre-existing nested-positive-universal law call site was found. `core/quantifiers.test.ts` contains an operational nested flag and an expected flag refusal; `core/pairs.test.ts` has another expected flag refusal; `core/sized-sort.test.ts` explicitly refuses finite nesting. `examples/lists.ts` has a legitimate `forall`/`someKey` existential step law, not two positive universal binders. Remaining pre-existing hits are JavaScript Array.every nesting. All 21 example modules import under the conservative fix. New regression cases intentionally exercise the refused law forms.
