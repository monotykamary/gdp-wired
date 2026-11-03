// Research-only snapshot equality check; not package integrity or lifecycle attestation.
export type ConsumerTypeScript = Readonly<{path: string, version: string}>

export function assertConsumerTypeScript(actual: ConsumerTypeScript, expected: ConsumerTypeScript): void {
  if (actual.path !== expected.path) throw Error('owned TypeScript path mismatch')
  if (actual.version !== expected.version) throw Error('owned TypeScript version mismatch')
}
