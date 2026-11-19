// Topological order. Build and the staged replay use these exact packaged sources.
const machine = ['../Cert.lean', '../Kernel.lean', '../Progress.lean', '../StepLaw.lean',
  '../Steps.lean', '../Sets.lean', '../Live.lean', '../Ghost.lean']
export const leanLibraries = {
  'finite-fold': [...machine, '../Count.lean', './FiniteFold.lean'],
  'weighted': [...machine, '../GhostMap.lean', '../Sums.lean', './GroupedTransport.lean'],
} as const
export type AggregateMechanism = keyof typeof leanLibraries
