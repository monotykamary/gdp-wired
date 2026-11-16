# Lift a retained capsule to its source

The product entry point is:

```sh
gdp-wired lift ./capsule ./source.json --out ./lifted
```

`source.json` is data, not a JavaScript or TypeScript module:

```json
{
  "schema": "gdp-lift-source/v1",
  "id": "my_protocol",
  "machine": "<the exact Machine object>",
  "laws": ["<the ordered public Law objects>"]
}
```

Optional naming-only metadata can preserve a historical theorem interface:

```json
"theorems": {"family": "Legacy.Checked.family", "source": ["legacy_source"]}
```

These validated Lean identifiers generate aliases to the already selected proof; they cannot select a strategy, change a law, or supply proof code. The source-name array must cover every public law exactly once. Existing generated aliases must pass a Lean equality check before reuse.

The strings above stand for the actual JSON objects. The identifier is a Lean-safe output label, not a protocol registry key. The supported source representation must preserve the complete machine, public law bodies and metadata; functions, accessors, cycles and unrepresentable values are refused rather than silently serialized away.

The command validates capsule integrity, chooses a transport from its shape and the provided source, and emits a fresh Lean project. It does not invoke invariant discovery or proof search. The default command then runs `lake build` and the emitted root through Lean, audits exact theorem coverage and axioms, and checks that the emitted files did not change. A successful check writes `LIFT-CHECKED.json` with status `SOURCE_CHECKED`. This is a claim about the provided source machine and laws, not an independent verification of their correspondence with an external program or TLA+ specification.

```sh
# Emit obligations without claiming that Lean accepted them.
gdp-wired lift ./capsule ./source.json --out ./candidate --emit-only

# Pin the input capsule independently and print a machine-readable result.
gdp-wired lift ./capsule ./source.json --out ./checked --sha256 <CAPTURE.json-sha256> --json
```

An existing output directory is never overwritten. Failed or incomplete output is retained for inspection and is not a source acceptance. `EMITTED_NOT_CHECKED` is deliberately distinct from `SOURCE_CHECKED`. Release checks disallow `sorry`, custom axioms and compiler-backed `native_decide` assumptions; the standard allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Implementation and regression scope

The unified pipeline covers ordinary/alpha, counted-source, witness, generalized bound-inclusion, typed substitution, and radix/invariant-restricted simulation. All 27 retained regression cases passed native Lean checks from one committed implementation, preserving the historical family/source theorem names and exact axiom sets. These are checks of the supplied encoded source models, not independent proofs of correspondence with an external specification. Strategy selection is structural: no protocol-name dispatch or handwritten per-protocol Lean is loaded into the product. Unsupported or ambiguous shapes fail explicitly.
