// Laptop-wide quick-bar admission. Kernel-owned locks, not check-then-unlink PID
// files: two stale cleaners must never remove a newly acquired owner's lock.
import {closeSync, ftruncateSync, mkdirSync, openSync, readFileSync, writeSync} from 'node:fs'
import {homedir} from 'node:os'
import {join} from 'node:path'
import {dlopen, FFIType, read} from 'bun:ffi'

export const BAR_SLOT_COUNT = 2
export const BAR_SLOT_DIR = join(homedir(), '.local', 'share', 'gdp-wired', 'bar-slots')
const LOCK_EX_NB = 2 | 4

function loadLocks() {
  if (process.platform !== 'darwin' && process.platform !== 'linux') throw Error('bar slots require macOS or Linux flock')
  const path = process.platform === 'darwin' ? '/usr/lib/libSystem.B.dylib' : 'libc.so.6'
  const locks = dlopen(path, {flock: {args: [FFIType.i32, FFIType.i32], returns: FFIType.i32}})
  const errors = (() => {
    if (process.platform === 'darwin') {
      const owner = dlopen(path, {__error: {args: [], returns: FFIType.ptr}})
      return {owner, get: owner.symbols.__error}
    }
    const owner = dlopen(path, {__errno_location: {args: [], returns: FFIType.ptr}})
    return {owner, get: owner.symbols.__errno_location}
  })()
  return {locks, errors}
}
let native: ReturnType<typeof loadLocks> | undefined
export type BarSlot = {slot: number, stalePid?: number, release: () => void}

export function tryBarSlot(dir = BAR_SLOT_DIR): BarSlot | undefined {
  const n = native ??= loadLocks()
  mkdirSync(dir, {recursive: true, mode: 0o700})
  for (let slot = 0; slot < BAR_SLOT_COUNT; slot++) {
    const fd = openSync(join(dir, `${slot}.lock`), 'a+', 0o600)
    let held = false
    try {
      if (n.locks.symbols.flock(fd, LOCK_EX_NB) !== 0) {
        const ptr = n.errors.get(), errno = ptr ? read.i32(ptr) : -1
        if (![4, 11, 35].includes(errno)) throw Error(`bar slot flock failed (errno ${errno})`)
        continue
      }
      let stalePid: number | undefined
      // A crash may leave metadata, but never a kernel lock. PID reuse cannot
      // strand a slot: metadata is diagnostic only, read AFTER exclusive lock.
      try {
        const old: unknown = JSON.parse(readFileSync(fd, 'utf8'))
        if (typeof old === 'object' && old !== null && 'pid' in old && typeof old.pid === 'number') stalePid = old.pid
      } catch { /* empty or interrupted metadata: the kernel lock is authoritative */ }
      ftruncateSync(fd, 0)
      writeSync(fd, JSON.stringify({pid: process.pid, cwd: process.cwd(), acquired: new Date().toISOString()}) + '\n')
      held = true
      let released = false
      return {slot, stalePid, release: () => {
        if (released) return
        released = true
        // Never unlink a slot: another process may already have its inode open.
        try { ftruncateSync(fd, 0) } finally { closeSync(fd) }
      }}
    } finally { if (!held) closeSync(fd) }
  }
  return undefined
}

export async function acquireBarSlot(opts: {dir?: string, pollMs?: number, signal?: AbortSignal, log?: (message: string) => void} = {}): Promise<BarSlot> {
  const dir = opts.dir ?? BAR_SLOT_DIR, pollMs = opts.pollMs ?? 120_000
  if (!Number.isFinite(pollMs) || pollMs <= 0) throw Error('bar slot polling interval must be positive')
  for (;;) {
    opts.signal?.throwIfAborted()
    const slot = tryBarSlot(dir)
    if (slot) {
      try { opts.log?.(`acquired quick-bar slot ${slot.slot + 1}/${BAR_SLOT_COUNT}${slot.stalePid === undefined ? '' : ` (cleared stale PID ${slot.stalePid})`}`) }
      catch (e) { slot.release(); throw e }
      return slot
    }
    opts.log?.(`waiting for one of ${BAR_SLOT_COUNT} quick-bar slots in ${dir}; retry in ${pollMs / 1000}s`)
    await new Promise<void>((resolve, reject) => {
      const done = () => { opts.signal?.removeEventListener('abort', abort); resolve() }
      const timer = setTimeout(done, pollMs)
      const abort = () => { clearTimeout(timer); opts.signal?.removeEventListener('abort', abort); reject(opts.signal?.reason ?? Error('bar slot wait aborted')) }
      opts.signal?.addEventListener('abort', abort, {once: true})
      if (opts.signal?.aborted) abort()
    })
  }
}
