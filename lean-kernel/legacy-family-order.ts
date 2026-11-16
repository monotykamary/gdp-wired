// Frozen cut-free project ABI (41ffd98b). Keep this order independent of new
// current-family modules; frame-export.test.ts binds every entry by SHA-256.
export const legacyFamilyOrder = [
  "Cert.lean",
  "Kernel.lean",
  "Cyclic.lean",
  "Progress.lean",
  "StepLaw.lean",
  "Steps.lean",
  "History.lean",
  "Sets.lean",
  "Live.lean",
  "NonTerm.lean",
  "Ghost.lean",
  "Sums.lean",
  "Refine.lean",
  "Bridge.lean",
  "BridgeRules.lean",
  "Data.lean",
  "Rationals.lean",
  "KInd.lean",
  "Count.lean",
  "CountMachine.lean",
  "GhostMap.lean",
  "QAlpha.lean"
] as const
