# Accepted unrestricted Paxos proof capsule

Final gate: `Bapa.PaxosEprLiteral.family_checked` proves the complete, unchanged
`checkCMachine` result for all 25 entries / 50 obligations.
`Bapa.PaxosEprLiteral.original_source_safety` proves the original atomic-source
public law for every counted reachable state, including zero size.

The proof does not assume a bound of 64. No source/target/kernel premise was
removed. Literal certificates are untrusted data checked by CountMachine.
Large steps7/10/20 reuse separately checked proof objects only after source,
object and shared dependency hashes match; `PaxosEprLiteralLinks.lean` proves
full goal/declaration/certificate equality in the kernel before using them.
The complete family theorem is composed from every actual checker conjunct.

Accepted batch: 20261116-085542-58n6uh.
Evidence is adjacent in `../p2-paxos-accepted-results/`.
`SHA256SUMS` binds this capsule's sources and original source JSON.
The preserved kernel sources are from the retained producer's Lean project,
not an edited kernel. Toolchain is pinned in `lean-toolchain`.

This is a self-contained Lean SOURCE proof capsule, not a native data-only
lift CLI capsule. A clean rebuild is `lake build` with the pinned toolchain;
the reported acceptance is the hash-verified cached-dependency check and
final standard-kernel theorem recorded in the adjacent receipts.

Release scope: Paxos alone for0.50.1; MLDR is not part of this acceptance.
Historical tree-lane cleanup exception is retained separately in
`../paxos-trees-results/cleanup-note.json`; this final batch cleanup completed.
