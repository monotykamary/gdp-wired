// Spelling used by C's answer bindings: exact integer constants or a placeholder
// for a source argument that is not part of the key. Split only at outer commas.
export function answerSignature(source: string, constants?: Record<string, number | string | boolean>): string {
  const args: string[] = []
  let depth = 0, start = 0
  for (let i = 0; i < source.length; i++) {
    const ch = source[i]
    if (ch === '(' || ch === '[') depth++
    else if (ch === ')' || ch === ']') depth--
    else if (ch === ',' && depth === 0) { args.push(source.slice(start, i).trim()); start = i + 1 }
  }
  if (source.slice(start).trim()) args.push(source.slice(start).trim())
  return args.map(a => {
    const k = /^-?\d+$/.test(a) ? Number(a) : constants && /^[A-Za-z_]\w*$/.test(a) && Object.hasOwn(constants, a) ? constants[a] : undefined
    return typeof k === 'number' && Number.isSafeInteger(k) ? String(k).replace('-', 'm') : 'x'
  }).join('_')
}
