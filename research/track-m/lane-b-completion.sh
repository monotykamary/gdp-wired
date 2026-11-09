#!/usr/bin/env bash
set -euo pipefail
LAB_DISPOSABLE=1 bun research/track-m/lane-b-completion-variant.ts "$1"
FAMILY_JSON=replays/family.json bash research/track-m/lane-b-parallel.sh cost after "$2"
