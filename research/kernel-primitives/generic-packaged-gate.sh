#!/usr/bin/env bash
# Actual public toLean and the unchanged prior 21-claim gate, from shipped
# leanProject sources only. Never regenerate the library inside this gate.
set -euo pipefail
: "${SUPERCOMPUTER_OUTPUT_DIR:?set the durable result directory}"
ROOT="$SUPERCOMPUTER_OUTPUT_DIR"
mkdir -p "$ROOT/generic" "$ROOT/prior21"
export GDP_LEAN_NATIVE=0 GDP_CERT=usual
bun scripts/gen-lean-library.ts --check > "$ROOT/library.log" 2>&1
bun test lean-kernel/generic-word-export.test.ts > "$ROOT/source-tests.log" 2>&1
bun research/kernel-primitives/generic-lean-gate.ts "$ROOT/generic/Proofs.lean" > "$ROOT/generic/generation.json" 2>&1
SUPERCOMPUTER_OUTPUT_DIR="$ROOT/generic" bun research/kernel-primitives/packaged-lean-gate.ts "$ROOT/generic/Proofs.lean" > "$ROOT/generic/package.json" 2>&1
bun research/kernel-primitives/generic-lean-gate.ts --audit "$ROOT/generic/Proofs.lean" "$ROOT/generic/lean.log" > "$ROOT/generic/audit.json" 2>&1
bun research/kernel-primitives/lean-machine-gate.ts "$ROOT/prior21/Proofs.lean" > "$ROOT/prior21/generation.json" 2>&1
SUPERCOMPUTER_OUTPUT_DIR="$ROOT/prior21" bun research/kernel-primitives/packaged-lean-gate.ts "$ROOT/prior21/Proofs.lean" > "$ROOT/prior21/package.json" 2>&1
bun research/kernel-primitives/lean-machine-gate.ts --audit "$ROOT/prior21/Proofs.lean" "$ROOT/prior21/lean.log" > "$ROOT/prior21/audit.json" 2>&1
