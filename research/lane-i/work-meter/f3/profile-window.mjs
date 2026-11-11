// CPU sample timestamps are startTime plus cumulative timeDeltas (microseconds).
// A sample-count suffix is not a time window when the sampler pauses.
export function selectProfileWindow(profile, quietWindowMs) {
  const invalid = (reason, details = {}) => ({stack: [], timing: {valid: false, reason, selection: 'timeDeltas', quietWindowMs, ...details}})
  if (!Number.isFinite(quietWindowMs) || quietWindowMs < 0) return invalid('invalid quiet window')
  if (!profile || !Number.isFinite(profile.startTime) || !Number.isFinite(profile.endTime) || profile.endTime < profile.startTime) return invalid('invalid profile interval')
  const samples = profile.samples, deltas = profile.timeDeltas
  if (!Array.isArray(samples) || !Array.isArray(deltas) || samples.length !== deltas.length || !Array.isArray(profile.nodes)) return invalid('missing or mismatched sample timestamps')
  const lowerBoundUs = Math.max(profile.startTime, profile.endTime - quietWindowMs * 1000), recent = []
  let time = profile.startTime
  for (let index = 0; index < samples.length; index++) {
    const delta = deltas[index]
    if (!Number.isFinite(delta) || delta < 0) return invalid('invalid sample delta', {invalidSampleIndex: index, invalidSampleDeltaUs: Number.isFinite(delta) ? delta : String(delta), previousSampleUs: time, profileStartUs: profile.startTime, profileEndUs: profile.endTime, totalSamples: samples.length})
    time += delta
    if (!Number.isFinite(time) || time > profile.endTime) return invalid('sample outside profile interval')
    if (time >= lowerBoundUs) recent.push({id: samples[index], time})
  }
  const nodes = new Map(profile.nodes.map(node => [node.id, node]))
  if (nodes.size !== profile.nodes.length || samples.some(id => !nodes.has(id))) return invalid('invalid sample node')
  const parents = new Map()
  for (const node of profile.nodes) for (const child of node.children ?? []) {
    if (!nodes.has(child) || parents.has(child)) return invalid('invalid profile parent')
    parents.set(child, node.id)
  }
  let gap = lowerBoundUs, maxGapUs = 0
  const frequencies = new Map()
  for (const sample of recent) {
    maxGapUs = Math.max(maxGapUs, sample.time - gap); gap = sample.time
    const previous = frequencies.get(sample.id)
    frequencies.set(sample.id, {count: (previous?.count ?? 0) + 1, last: sample.time})
  }
  maxGapUs = Math.max(maxGapUs, profile.endTime - gap)
  let leaf, bestCount = -1, bestLast = -Infinity
  for (const [id, frequency] of frequencies) if (frequency.count > bestCount || (frequency.count === bestCount && frequency.last >= bestLast)) {
    leaf = id; bestCount = frequency.count; bestLast = frequency.last
  }
  const stack = [], seen = new Set()
  for (let id = leaf; id !== undefined; id = parents.get(id)) {
    if (seen.has(id) || !nodes.get(id)?.callFrame) return invalid('invalid profile stack')
    seen.add(id); stack.push(nodes.get(id).callFrame)
  }
  return {stack, timing: {valid: true, selection: 'timeDeltas', quietWindowMs, profileStartUs: profile.startTime, profileEndUs: profile.endTime,
    lowerBoundUs, totalSamples: samples.length, samplesInWindow: recent.length, firstSampleUs: recent[0]?.time ?? null,
    lastSampleUs: recent.at(-1)?.time ?? null, latestSampleAgeMs: recent.length ? (profile.endTime - recent.at(-1).time) / 1000 : null,
    maxSampleGapMs: maxGapUs / 1000, selectedLeafId: leaf ?? null}}
}
