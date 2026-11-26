// Shared zero-dependency Node CLI primitives reused by `core/cli.ts` and `core/emit-cli.ts`.

export type CliFS = {
  existsSync: (p: string) => boolean
  readFileSync: (p: string, e: string) => string
  readdirSync: (p: string) => string[]
  statSync: (p: string) => {isDirectory: () => boolean}
  mkdirSync: (p: string, o: {recursive: boolean}) => unknown
  writeFileSync: (p: string, s: string) => void
  rmSync: (p: string, o: {force: boolean}) => void
}

export type CliPath = {
  resolve: (...p: string[]) => string
  dirname: (p: string) => string
  join: (...p: string[]) => string
  basename: (p: string) => string
  extname: (p: string) => string
  relative: (a: string, b: string) => string
}

export type CliProc = {
  argv: string[]
  pid: number
  exitCode?: number
  cwd: () => string
  env: Record<string, string | undefined>
  stdout: {write: (s: string) => void, isTTY?: boolean}
  stderr?: {write: (s: string) => void}
  getBuiltinModule: (id: string) => unknown
  on?: (ev: string, fn: () => void) => void
  exit?: (code?: number) => never
}

export const cliProc = (globalThis as unknown as {process: CliProc}).process
export const cliFs = cliProc.getBuiltinModule('node:fs') as CliFS
export const cliPath = cliProc.getBuiltinModule('node:path') as CliPath
export const cliUrl = cliProc.getBuiltinModule('node:url') as {pathToFileURL: (p: string) => {href: string}}
export const cliOs = cliProc.getBuiltinModule('node:os') as {tmpdir: () => string}

export const cliOut = (s = '') => cliProc.stdout.write(`${s}\n`)
export const cliErr = (s: string) => (cliProc.stderr ?? cliProc.stdout).write(`${s}\n`)

// The nearest directory from `d` up where `ok` holds.
export function up(d: string, ok: (d: string) => boolean): string | undefined {
  for (let x = d; ; x = cliPath.dirname(x)) {
    if (ok(x)) return x
    if (cliPath.dirname(x) === x) return undefined
  }
}

// Load a local module by path (optional cache-busting query string for re-importing mutated files).
export async function loadFileModule(filePath: string, query?: string): Promise<Record<string, unknown>> {
  const base = cliUrl.pathToFileURL(cliPath.resolve(filePath)).href
  return await import(query ? `${base}?${query}` : base) as Record<string, unknown>
}

// Parse CLI flags (`--flag`, `--key value`, `--key=value`) and positional args.
export function parseCliFlags(
  argv: string[],
  boolFlags: ReadonlySet<string>,
  allowEmpty = false,
): {positionals: string[], flags: Record<string, string | boolean>, missingValue?: string} {
  const positionals: string[] = []
  const flags: Record<string, string | boolean> = {}
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]!
    if (boolFlags.has(a)) {
      const key = a.slice(2).replace(/-(\w)/g, (_, c: string) => c.toUpperCase())
      flags[key] = true
    } else if (a.startsWith('--')) {
      const eq = a.indexOf('=')
      const k = eq >= 0 ? a.slice(2, eq) : a.slice(2)
      const v = eq >= 0 ? a.slice(eq + 1) : (argv[++i] ?? '')
      if (!v && !allowEmpty) return {positionals, flags, missingValue: k}
      const key = k.replace(/-(\w)/g, (_, c: string) => c.toUpperCase())
      flags[key] = v
    } else {
      positionals.push(a)
    }
  }
  return {positionals, flags}
}
