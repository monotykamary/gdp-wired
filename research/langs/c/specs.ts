// Real C projects' stateful structs, read by gdp-wired's C front end (core/extract-c.ts): what each item reads, and the
// laws, written against the extracted rule's names. `run.ts` fetches each project at its pinned version, extracts it
// (checked against the project's own file, compiled beside a generated harness with the undefined-behavior sanitizer
// trapping), and proves the laws; research/realworld/items/c-projects.ts scores the rules extracted at the pins.
import {type Cond, type StepLaw, all, any, when} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import type {COptions} from '../../../core/extract-c.ts'
import type {Domain} from '../../realworld/lib.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type X = any
type R = {stepLaw: (name: string, then: (b: X, a: X) => Cond, when?: (b: X) => Cond) => StepLaw, law: (name: string, f: (s: X) => Cond) => Law}
export type CLaw = {name: string, kind: 'step' | 'access' | 'safety', intent: 'docs' | 'tests' | 'inferred', why: string, law: (r: R) => StepLaw | Law}
export type CSpec = {id: string, domain: Domain, project: string, version: string, licence: string, author: string, repo: string,
  // The source at the pin: a tarball (its first directory stripped), and the files of it that are read.
  tarball: string, file: string, flags: string[], reads: string, summary: string, opts: Omit<COptions, 'flags' | 'clang' | 'root' | 'compileCommands'>, laws: CLaw[]}

const AK = '8b93e1bf16c15c7870124e3807e939effe595479'
// (an index's next, masked by 127: the wrap by cases)
const next = (i: X) => when(i.eq(127), 0, i.plus(1))
export const SPECS: CSpec[] = [
  {id: 'queue/Ring-Buffer/ring_buffer_t', domain: 'queue', project: 'Ring-Buffer', version: AK.slice(0, 7), licence: 'MIT', author: 'Anders Kalør', repo: 'AndersKaloer/Ring-Buffer',
    tarball: `https://github.com/AndersKaloer/Ring-Buffer/archive/${AK}.tar.gz`, file: 'ringbuffer.c', flags: [],
    reads: 'ringbuffer.c and ringbuffer.h: ring_buffer_init, ring_buffer_queue, ring_buffer_dequeue, ring_buffer_peek, ring_buffer_is_empty, ring_buffer_is_full, ring_buffer_num_items',
    summary: 'A ring buffer of 128 chars in a fixed array, its head and tail indices masked by 127: a queue on a full buffer overwrites the oldest byte, a dequeue and a peek give a byte through an out-parameter (returning 0 where there is none: the step\'s failure, stated), the predicates read the indices.',
    opts: {entry: 'ring_buffer_t', functions: ['ring_buffer_init', 'ring_buffer_queue', 'ring_buffer_dequeue', 'ring_buffer_peek', 'ring_buffer_is_empty', 'ring_buffer_is_full', 'ring_buffer_num_items'],
      fails: {ring_buffer_dequeue: '== 0', ring_buffer_peek: '== 0'}, onError: 'discard'},
    laws: [
      {name: 'the indices stay within the buffer', kind: 'safety', intent: 'inferred', why: 'every write of head_index and tail_index is masked by RING_BUFFER_MASK (ringbuffer.c), init sets both 0',
        law: r => r.law('the indices stay within the buffer', s => all(s.head_index.lt(128), s.tail_index.lt(128)))},
      {name: 'only RING_BUFFER_SIZE-1 items are held', kind: 'step', intent: 'docs', why: 'ringbuffer.h: "Due to the design only RING_BUFFER_SIZE-1 items can be contained in the buffer"',
        law: r => r.stepLaw('only RING_BUFFER_SIZE-1 items are held', (_b, a) => a.ring_buffer_num_items_result.atMost(127), b => b.method.is('ring_buffer_num_items'))},
      {name: 'a queue on a full buffer overwrites the oldest byte', kind: 'step', intent: 'docs', why: 'ringbuffer.c: "Is going to overwrite the oldest byte / Increase tail index"',
        law: r => r.stepLaw('a queue on a full buffer overwrites the oldest byte', (b, a) => all(a.tail_index.eq(next(b.tail_index)), a.head_index.eq(next(b.head_index))),
          b => all(b.method.is('ring_buffer_queue'), b.head_index.lt(128), b.tail_index.lt(128), any(all(b.head_index.eq(127), b.tail_index.eq(0)), all(b.head_index.lt(127), b.tail_index.eq(b.head_index.plus(1))))))},
      {name: 'a queue puts its byte at the head', kind: 'step', intent: 'docs', why: 'ringbuffer.c: "Place data in buffer: buffer->buffer[buffer->head_index] = data"',
        law: r => r.stepLaw('a queue puts its byte at the head', (b, a) => a.buffer.at(b.head_index).eq(b.ring_buffer_queue_data), b => all(b.method.is('ring_buffer_queue'), b.head_index.lt(128), b.tail_index.lt(128)))},
      {name: 'a dequeue gives the oldest byte and frees it', kind: 'step', intent: 'docs', why: 'ringbuffer.h: dequeue "Returns the oldest byte in a ring buffer" (through data)',
        law: r => r.stepLaw('a dequeue gives the oldest byte and frees it', (b, a) => all(a.ring_buffer_dequeue_data.eq(b.buffer.at(b.tail_index)), a.tail_index.eq(next(b.tail_index)), a.head_index.eq(b.head_index)),
          b => all(b.method.is('ring_buffer_dequeue'), b.tail_index.lt(128)))},
      {name: 'is_empty is whether head and tail meet', kind: 'step', intent: 'docs', why: 'ringbuffer.h: is_empty "Returns 1 if empty; 0 otherwise" (head_index == tail_index)',
        law: r => r.stepLaw('is_empty is whether head and tail meet', (b, a) => a.ring_buffer_is_empty_result.eq(1).iff(b.head_index.eq(b.tail_index)), b => b.method.is('ring_buffer_is_empty'))},
    ]},
  {id: 'rate limit/nghttp2/nghttp2_ratelim', domain: 'rate limit', project: 'nghttp2', version: '1.70.0', licence: 'MIT', author: 'nghttp2 contributors', repo: 'nghttp2/nghttp2',
    tarball: 'https://github.com/nghttp2/nghttp2/releases/download/v1.70.0/nghttp2-1.70.0.tar.xz', file: 'lib/nghttp2_ratelim.c', flags: ['-Ilib/includes', '-Ilib'],
    reads: 'lib/nghttp2_ratelim.c: nghttp2_ratelim_init, nghttp2_ratelim_drain (nghttp2_ratelim_update refused: UINT64_MAX is past the rule\'s numbers, and it divides by a variable)',
    summary: 'nghttp2\'s token bucket (it limits the rate of streams a peer resets): init fills it to its burst, drain takes n tokens or fails (-1, the step\'s failure, stated) changing nothing.',
    opts: {entry: 'nghttp2_ratelim', functions: ['nghttp2_ratelim_init', 'nghttp2_ratelim_drain'], fails: {nghttp2_ratelim_drain: '< 0'}},
    laws: [
      {name: 'burst is the maximum value of val', kind: 'safety', intent: 'docs', why: 'nghttp2_ratelim.h: "burst is the maximum value of val."', law: r => r.law('burst is the maximum value of val', s => s.val.atMost(s.burst))},
      {name: 'drain takes n from val', kind: 'step', intent: 'docs', why: 'nghttp2_ratelim.h: "nghttp2_ratelim_drain drains |n| from rl->val. It returns 0 if it succeeds"',
        law: r => r.stepLaw('drain takes n from val', (b, a) => all(a.val.eq(b.val.minus(b.nghttp2_ratelim_drain_n)), a.burst.eq(b.burst)), b => b.method.is('nghttp2_ratelim_drain'))},
      {name: 'a new limiter is full', kind: 'step', intent: 'tests', why: 'tests/nghttp2_ratelim_test.c: after nghttp2_ratelim_init(&rl, 1000, 21), rl.val is 1000 and rl.tstamp 0',
        law: r => r.stepLaw('a new limiter is full', (b, a) => all(a.val.eq(b.nghttp2_ratelim_init_burst), a.burst.eq(b.nghttp2_ratelim_init_burst), a.rate.eq(b.nghttp2_ratelim_init_rate), a.tstamp.eq(0)), b => b.method.is('nghttp2_ratelim_init'))},
    ]},
  {id: 'rate limit/enet/ENetPeer throttle', domain: 'rate limit', project: 'ENet', version: '1.3.18', licence: 'MIT', author: 'Lee Salzman', repo: 'lsalzman/enet',
    tarball: 'https://github.com/lsalzman/enet/archive/refs/tags/v1.3.18.tar.gz', file: 'peer.c', flags: ['-Iinclude'],
    reads: 'peer.c: enet_peer_throttle, enet_peer_ping_interval, enet_peer_timeout (on ENetPeer, whose lists, pointers and other fields they don\'t touch are left out and compared unchanged)',
    summary: 'ENet\'s packet throttle, the probability (out of 32) that an unreliable packet is sent: a round trip at most the last one raises it by the acceleration up to its limit (returning 1), one past the last plus twice its variance lowers it by the deceleration down to 0 (returning -1); the ping interval and the timeouts take their defaults where given 0.',
    opts: {entry: 'ENetPeer', functions: ['enet_peer_throttle', 'enet_peer_ping_interval', 'enet_peer_timeout']},
    laws: [
      {name: 'the throttle stays within its limit', kind: 'step', intent: 'docs', why: 'peer.c (enet_peer_throttle_configure): the throttle is a probability of at most ENET_PEER_PACKET_THROTTLE_SCALE; enet_peer_throttle caps it at packetThrottleLimit',
        law: r => r.stepLaw('the throttle stays within its limit', (_b, a) => a.packetThrottle.atMost(a.packetThrottleLimit), b => all(b.method.is('enet_peer_throttle'), b.packetThrottle.atMost(b.packetThrottleLimit)))},
      {name: 'a fast round trip raises the throttle by the acceleration', kind: 'step', intent: 'docs', why: 'peer.c: "If a measured round trip time happens to be significantly less than the mean round trip time ... the throttle probability is increased ... by an amount specified in the acceleration parameter"',
        law: r => r.stepLaw('a fast round trip raises the throttle by the acceleration', (b, a) => all(a.enet_peer_throttle_result.eq(1), a.packetThrottle.atLeast(b.packetThrottle), a.packetThrottle.atMost(b.packetThrottle.plus(b.packetThrottleAcceleration))),
          b => all(b.method.is('enet_peer_throttle'), b.lastRoundTripTime.gt(b.lastRoundTripTimeVariance), b.enet_peer_throttle_rtt.atMost(b.lastRoundTripTime), b.packetThrottle.atMost(b.packetThrottleLimit), b.packetThrottle.plus(b.packetThrottleAcceleration).lt(4294967296)))},
      {name: 'a slow round trip lowers the throttle by the deceleration, to no lower than 0', kind: 'step', intent: 'docs', why: 'peer.c: "If a measured round trip time happens to be significantly greater than the mean ... the throttle probability is decreased ... by an amount specified in the deceleration parameter"',
        law: r => r.stepLaw('a slow round trip lowers the throttle by the deceleration, to no lower than 0', (b, a) => all(a.enet_peer_throttle_result.eq(-1), a.packetThrottle.atMost(b.packetThrottle)),
          b => all(b.method.is('enet_peer_throttle'), b.lastRoundTripTime.gt(b.lastRoundTripTimeVariance), b.enet_peer_throttle_rtt.gt(b.lastRoundTripTime.plus(b.lastRoundTripTimeVariance.plus(b.lastRoundTripTimeVariance))), b.lastRoundTripTime.plus(b.lastRoundTripTimeVariance.plus(b.lastRoundTripTimeVariance)).lt(4294967296)))},
      {name: 'a ping interval of 0 is the default, 500', kind: 'step', intent: 'docs', why: 'peer.c: "@param pingInterval the interval at which to send pings; defaults to ENET_PEER_PING_INTERVAL if 0" (enet.h: 500)',
        law: r => r.stepLaw('a ping interval of 0 is the default, 500', (b, a) => a.pingInterval.eq(500), b => all(b.method.is('enet_peer_ping_interval'), b.enet_peer_ping_interval_pingInterval.eq(0)))},
      {name: 'timeouts of 0 are the defaults', kind: 'step', intent: 'docs', why: 'peer.c: timeoutLimit, timeoutMinimum and timeoutMaximum each "defaults to ENET_PEER_TIMEOUT_LIMIT / _MINIMUM / _MAXIMUM if 0" (enet.h: 32, 5000, 30000)',
        law: r => r.stepLaw('timeouts of 0 are the defaults', (_b, a) => all(a.timeoutLimit.eq(32), a.timeoutMinimum.eq(5000), a.timeoutMaximum.eq(30000)),
          b => all(b.method.is('enet_peer_timeout'), b.enet_peer_timeout_timeoutLimit.eq(0), b.enet_peer_timeout_timeoutMinimum.eq(0), b.enet_peer_timeout_timeoutMaximum.eq(0)))},
    ]},
]
