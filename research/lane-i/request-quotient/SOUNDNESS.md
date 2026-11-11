# Request-space quotient: soundness and scope

## Contract

This is an **untrusted sampler optimization**, enabled only by
`GDP_REQUEST_QUOTIENT=1`. It does not assert a law or bypass a checker.
`core/exists.ts::smallWithin` retains its original request array, order,
logical `work` decrement, BFS order, state cap and random-walk code. It may skip
a BFS trial only after a member of the same class has successfully returned a
state **at that same source state**. A refusal or evaluation exception never
covers a class. Budget cancellation is rethrown, not treated as a refusal.

The domain is the sampler's finite Cartesian product of natural scalar inputs
and native finite carried maps, for an admitted, pure `Machine`. Params and the
source state are fixed when a class is reused. No model names, operation names,
proof verdicts or wall measurements participate in class construction.

## Read projection

Choose at most one scalar selector syntactically compared with at least two
constants in the step. The choice is deterministic: most distinct tags, then
input declaration order. For **every value present in the request domain**,
including values not named by a tag, substitute the selector's value and fold
only exact, safe-natural arithmetic and Boolean constants. This is not a
switch-exhaustiveness assumption: an absent tag's remaining/default branch is
analyzed too. If there is no selector, analyze one unspecialized slice.

For slice `a`, let `R_a` be the union of the input names needed by all scalar
updates and map updates after this specialization. A class is the pair

    (selector value, ordered projection onto R_a).

A read of a carried map retains the entire finite map, including its keys and
zero entries. Its token is sorted by numeric key and serialized exactly; it is
not a hash whose collisions can conflate requests. Class IDs are assigned in
first-occurrence order. A selector value is kept even for a no-op slice.

### Structural dependency argument

For fixed params/state and same selector value, induction on expressions and
conditions establishes that requests agreeing on `R_a` produce equal values
where both evaluations return:

1. A literal, param or old-state observation has no request dependency. A free
   scalar input contributes its name. An input hidden by a bound key does not.
2. An arithmetic operation, tuple constructor or projection contributes the
   union of its operand dependencies. Equal operand values give equal results.
   Constant folding is performed only when the result is an exact safe natural;
   otherwise dependencies are retained.
3. A map read contributes its key's dependencies and, for a carried map, the
   map's name. Equal keys and equal maps give equal cells (including zero outside
   support). A fixed old-state map contributes only key dependencies.
4. A conditional with a known guard contributes only its selected arm. Otherwise
   it contributes guard and both arms. Boolean short-circuit constants are valid
   erasures of output dependencies; they are **not** an assertion that evaluating
   a different request will avoid an exception.
5. A flag is expanded in its definition's scope, not in a caller's bound-key
   scope. Only already-defined, acyclic flags are supported. Bound keys mask
   scalar inputs only within their actual expression/condition body.
6. A count contributes the dependencies of its argument, its bound, and its body.
   The count's row parameters bind its bound; its iteration key additionally
   binds its body. Equal bounds/row arguments and pointwise equal summands give
   equal finite sums. Flag-dependent count definitions are rejected here.
7. A quantifier contributes its body's dependencies with its key(s) bound. For
   a plain key, the key can occur only as a direct map index, never as an exposed
   scalar. Any key past the support of every map therefore returns the same
   defaults at those bound-key reads. Structural induction gives the same value
   at any two such fresh keys; enlarging an unread map's support may change the
   chosen fresh key but cannot change the result. This also justifies the default
   of a plain-key bulk write. Cross-key quantifiers conservatively retain all
   carried maps. A count-map read under a binder is rejected: its memoized keys
   are not a proof of complete support. Opaque functions are rejected too.
8. A scalar write contributes its value. A one-cell map write contributes key and
   value. A bulk write contributes its bound-body dependencies. Unwritten state
   components are the same given components. Thus every returned output component
   is equal for two successful members of the class.

The standalone `ReadSet.lean` checks the generic congruence induction for literals,
scalar inputs, map cells, pure operators, conditionals, bound arguments, finite
sums and unbounded quantified conditions, and lifts it pointwise to all output
coordinates. Its branch-erasure lemmas justify fixed-selector branches. It has
no `sorry`, custom axiom or trusted-kernel edit. **It is a dependency-calculus
proof, not a mechanically verified translation of the TypeScript analyzer.**
The correspondence above, source review and differential tests are separate
obligations; the proof must not be reported as a formal verification of the
sampler or JavaScript compiler.

Opaque functions, history, sums/least-key lowering, ambiguous namespaces,
non-topological flags, reserved flag/binder spellings and the count cases above
fall back to the untouched sampler. Returning `undefined` is always safe: it
means no quotient is used, not an empty request domain.

## Why a class cannot hide a distinct reachable behavior

Let `T_s(r)` be the successful successor, if any, at fixed state `s`. The read
argument gives:

    class(r) = class(q) and both calls return
        => T_s(r) = T_s(q).

It deliberately does not infer that all members have the same refusal status.
Assumptions, eagerly evaluated unused flags, numeric range checks, or runtime
support construction can reject one member and allow another.

Induct on the **original request index** at a BFS state. Before any successful
member, all trials in a class are executed normally. When its first successful
member returns `t`, normal duplicate detection has already recorded or found
`t`; then the class is marked covered. At every later member:

* a failed original call would add nothing;
* a successful original call returns that same `t`, already seen, so would add
  nothing and cannot change the first-success witness.

Skipping it therefore preserves the ordered new-state sequence. Classes covered
at one source state are discarded before the next source state. Induction over
BFS removals preserves the queue and sample sequence for every logical trial
prefix, subject to the existing interpreter/compiled-step agreement. The
`work--` still occurs at every original index. This matters when the logical
budget ends inside a request array: iterating just representatives would move
the boundary to a different BFS state. Random walks use the original request
array and seeded recurrence without quotienting, so they do not acquire a new
sampling distribution. First-witness provenance is not replaced by a later
representative.

The state comparison/hashing and runtime are unchanged. Differential tests must
check their concrete behavior, including scalar/map states, default values,
refused-first classes, finite prefixes and compiled/interpreted transitions.
The 28-original candidate/verdict census is an additional acceptance gate, not a
substitute for the read argument. The audit-only `audit-skipped.ts` executes
skipped requests with the interpreter in a disposable source copy; it accepts
only a refusal or the same canonical successor (including defaults).
`edge-cases.ts` also checks arithmetic inside selector conditions, and plain,
conditional-key and shifted-key bulk defaults with enlarged unread support.

## Work and determinism

Class construction charges existing `ticks` and checks the current endpoint every
256 such visits and at completion. It neither reprices counters nor changes the
budget API. The default provisional tick price is 1; any claim about the existing
1,024-unit slack still requires the complete 15M census on the final source.
No calibrated wall guarantee follows from these provisional units.

For the same admitted machine, params, request domain, work allowance and fixed
weights, selector choice, constant folding, field order, map tokens and class IDs
are deterministic. No elapsed-time observation is made by the quotient. A
counted endpoint may interrupt the cheaper execution at a different original
index; it returns through the existing distinct budget outcome, not a fake
refutation. Completed generation must retain its candidate family and existing
proved/checked verdicts; interrupted generation is reported separately.

All wall timing is external research instrumentation. Sample/class controls use
a separate 1e12 work allowance. Full-generation controls use the full counted
clock without a whole-run work budget, pass 1e12 as the search-time allowance,
retain local proposal cutoffs, and stop at the candidate boundary (with a 600s
external process timeout). They are not evidence of completion within 15M. The
earlier explicit-budget generation control is preserved as a failed receipt: a
local finite-law deadline threw BudgetExpired before its huge global endpoint.
