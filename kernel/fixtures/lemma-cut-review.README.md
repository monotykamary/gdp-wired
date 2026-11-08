# Frozen conditional-cut review fixtures

`lemma-cut-review.json` was generated once on boat by the independent reviewer's unmodified `review-edgecases.ts --make`, against the unmodified `df6f409e` kernel (SHA256 `6984ace7dea563b38aa93827558cfe209dd4978fb9ab994d92e4c2f8b9966433`). The capture is `runs/track-k-review-freeze-v1/`; the source is preserved verbatim under `research/track-k/review-source/`.

Tests load these fixed goals, trees, slices and input indices. They must not regenerate their leaves with `lemmaPath`, `leafConstraints`, or any checker helper under test. The frozen `expect: false` on `zero_coefficient_condition` records the old false rejection: F1 deliberately changes that one expectation to true. `ReviewEdges.lean` is the accompanying independent Lean transport, including the reviewer's directly written zero-row example.
