# Closure phase census v1

Diagnostic-only measurements of candidate 50109a36 and main 6a3874d3.
All timing processes ran sequentially on bx_3kjzmmhv, exclusive, 8/8 vCPUs.

- `census.json`: compact per-process/per-law measurements.
- `verification.json`: exact control comparisons and proof-replay manifest.
- `candidate-focused-profiled-Inv2973.json`: admitted/offered IDs, per-round
  walls, and the four attempted numeric leaves.
- `candidate-focused-profiled-Invstar.json`: admitted/offered/cited IDs,
  per-round walls, and all seventeen attempted numeric leaves.
- `candidate-focused-profiled-Invstar-proofs.json`: twelve numeric proofs,
  their goals/paths, hypothesis-to-cut-ID mappings, and cited-ID expectations.
- `phase-census.log`: full raw job output, including controls and hashed
  instrumentation/restoration manifests.
- `preflight-1.log`: preserved failed lint preflight; not success evidence.
- `placement.json`: hardware and exclusive placement receipt.
- `validation/verify-census.log`: independent fresh-process replay and checks.

The three actually referenced cut IDs are closure-1/cut-17,
closure-2/cut-17, closure-3/cut-17 in the Inv* run. No cut ID is referenced
by an Inv2973 numeric proof/core. Offered hypotheses are not minimal
proof dependencies. See ../../REPORT.md and the diagnostic methodology in
research/track-m/PHASE-CENSUS.md for comparison limits and definitions.
