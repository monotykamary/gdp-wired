// Every example domain: each file of domains/ exports `domain`. For examples.test.ts and lean-kernel/export-kernel.ts
// --examples.
import type {Domain} from './harness.ts'

const files = [...new Bun.Glob('*.ts').scanSync(`${import.meta.dir}/domains`)].sort()
export const domains: Domain[] = await Promise.all(files.map(async f => ((await import(`./domains/${f}`)) as {domain: Domain}).domain))
