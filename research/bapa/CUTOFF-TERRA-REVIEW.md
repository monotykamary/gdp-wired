# Independent feasibility review

Reviewer: `openai/gpt-6.1-terra`; run `e4b2e15a5c134a3690f7a7cf671317ce`.

## Verdict

**No sound blanket lift is established for the 29 families / 67 declarations.** The EPR small-countermodel theorem is a possible ingredient for a restricted subset, not a justification for lifting the actual fixed-radix numeric encodings wholesale. I did not complete a per-declaration inventory or verify retained certificate coverage, so which families qualify remains unknown.

The repository top-level matched the requested path exactly. This was read-only inspection and mathematical analysis; no searches for proofs, tests, Lean builds, edits, or commits were performed.

## Principal obstructions

- **The theorem must apply to the negated verification obligation.** For an obligation \(H\Rightarrow G\), the relevant satisfiability problem is \(H\land\neg G\), including all invariant, transition, flag, and postcondition quantifiers. A function-free EPR *countermodel* must have an effectively reducible \(\exists^*\forall^*\) form, with no positive-arity function symbols and with its background constraints covered by the theorem. Merely seeing universal laws or an EPR-looking source protocol is insufficient.
- **Functions are not free relational abstractions.** Replacing a total function by a graph requires functionality and totality. Totality introduces \(\forall x\,\exists y\), generally outside EPR, and restricting to witness elements can fail closure under function values. This matters for function-valued maps such as `idn` in `research/protocols/models.ts`.
- **The port is numeric, not an abstract many-sorted EPR model.** `research/protocols/ic3syn/common.ts` defines `pk(a,b) = 64a+b` and `pk3` with radix 64. Without the relevant component bounds, collisions occur: `pk(0,64) = pk(1,0)`. Changing the size or radix changes the numeric machine; a relational small model is not automatically a model of the emitted Lean obligation, or conversely. `research/protocols/models.ts:8–16` also identifies natural-number order and successor as encoding choices.
- **Counts and order need separate arguments.** `majority` uses exact counts and `size < 2*members`; shrinking a domain need not preserve that arithmetic. `lean-kernel/CountMachine.lean:962–973,2305–2306` states soundness for numeric maps and count-constrained reachability, not arbitrary abstract EPR structures. Natural order, successor, numeric constants, and arithmetic similarly cannot simply be treated as uninterpreted relations while retaining their intended semantics.
- **Fixed 64 is not “all sizes ≤64.”** For example, a fixed-domain sentence saying “there are at least 64 distinct elements” holds at exactly 64 and fails at 63. Padding a smaller countermodel to 64 can change universal, existential, order, function, and count constraints. A particular `size ≤ 64` parameterized certificate could cover smaller sizes if its actual theorem says so; that must be checked individually, not inferred from fixed-64 coverage. See `research/bapa/CUTOFF.md`.

## Cutoff counterexample and the safe distinction

There is **no general variables-plus-constants countermodel cutoff for validity of arbitrary function-free first-order sentences**. Let \(T\) assert that a binary relation \(R\) is irreflexive, transitive, and has no maximal element:

\[
\forall x\,\neg R(x,x),\quad
\forall x\,y\,z\,(R(x,y)\land R(y,z)\to R(x,z)),\quad
\forall x\,\exists y\,R(x,y).
\]

Every finite structure falsifies \(T\), but \((\mathbb N,<)\) satisfies it. Thus the function-free sentence \(\neg T\) is valid on **every finite size** and invalid in an infinite structure. Its negation has \(\forall\exists\) alternation, not EPR.

This does **not** refute the smaller, sound statement for a genuinely universal sentence \(\forall\bar x\,\phi(\bar x)\) with quantifier-free, function-free \(\phi\): any countermodel restricts to the witnesses and named constants, with a nonempty-domain adjustment. The crucial distinction is the syntax of the **negation of the whole obligation**, not a count of variables in an arbitrary validity formula.

## Sound reuse route

1. Inventory each emitted init, step, and post obligation and the exact existing artifact and size assumptions; distinguish fixed-size from genuinely bounded-size claims.
2. For each candidate, prove in Lean that its **negated** obligation translates to a supported small-model fragment, including equality, constants and all quantifiers. Restrict functions, arithmetic, counts, and order unless independently justified.
3. Prove both needed semantic bridges between source sorts and numeric Lean maps, including radix injectivity, bounds, updates, quantifier domains, and any preserved order/count properties.
4. Establish that the existing certificates actually cover every required size—or prove a valid padding/transport theorem for that specific fragment—and re-check translated certificates without a fresh search.

Until those steps succeed, the appropriate status is **unknown**, not “all sizes proved.” `research/protocols/epr/DESIGN.md:110–151` describes an EPR-shaped decision approach; it is not by itself a checked cutoff theorem for these exported machines.
