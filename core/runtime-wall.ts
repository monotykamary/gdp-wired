// Dependency-free bridge for cooperative runtime cancellation. The wall module
// installs its checker; the interpreter stays usable without importing the
// proof engine (which itself imports the machine constructors).
export const runtimeWall: {check?: (phase: string) => void} = {}
