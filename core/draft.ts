// Drafting laws from a clause (`gdp-wired draft`): a clause's text and the code's names in, `gdp: law` and `gdp: cite`
// comments out, for a person to read, change and sign. Who drafts (a language model, a colleague, the person) is
// outside this file: `draftPrompt` is the question, asked of anyone (`--llm <command>` pipes it to one), and the answer
// is JSON. What the drafter proposes is read here as every law is (core/laws.ts, over the code's names), so a law that
// names nothing the code has is refused before anyone reads it; whether a law is faithful to its clause is not checked
// by anything here. So every citation drafted says so, `[unreviewed: drafted by <who>]`, until a person replaces it
// with `[reviewed-by: <name>, <date>]`; `gdp-wired check --require-review` refuses (exit 2) a law cited unreviewed.
import type {Extraction} from './extract.ts'
import {type LawOpts, LawError, buildLaw, buildTwoRuns, isTwoRuns, namesWithClock} from './laws.ts'

export type Draft = {method?: string, name: string, expr: string, answers: string}
// The question: the clause, the code's names and what a law can say.
export function draftPrompt(x: Extraction, clause: string, cite: string): string {
  const role = {input: 'request', param: 'made with', answer: 'answered call', result: 'result', failed: 'failed', method: 'method', clock: 'clock', state: 'state', const: 'constant'} as const
  const names = namesWithClock(x).filter(n => n.role !== 'const').map(n => `  ${n.role === 'input' && n.method ? `${n.method}(${n.code})` : n.code}  ${role[n.role]}${n.map ? ` (fields: ${n.map.fields.join(', ')})` : ''}`)
  return `You draft machine-checked laws for code that must meet a regulation. A person reviews every law you draft; a prover then checks it against the code.

The clause (${cite}):
${clause.trim()}

The code (${x.model?.name ?? 'its rule'}) has these names (the code's name, then its role: state is a field, request an argument of a method, clock the request's time):
${names.join('\n')}

A law is one expression over those names: comparisons (< <= > >= == !=), + - and * by a constant, and/or/not/implies, a map at a key (m[k].field, k in m), forall k in m: ..., a choice by its value (status == "open"). On a method (method set below) it is a law of one call of it: fields are the state after the call, old(x) before, the method's arguments by name, now the request's time. Durations: now - t < 30 days, 72 hours, now - t <= 10 business days. The code acts only when it is called, so a deadline is a law of the call that acts: what that call leaves meets the deadline (on the method that grants a request: granted implies now - received <= 30 days; or a call past the deadline doesn't grant). About two runs: "<argument> never reaches <field>, <field>" (that argument never changes those fields), "isolated by <argument>" (one caller's calls never change what another sees).

State what the clause requires, not what the code does: a law the code breaks is what the review is for. Draft only laws whose every name is in the list; leave out what the clause asks of something this code doesn't hold. Answer with JSON only, an array (empty if nothing applies):
[{"method": "<the method it is about, or null for a law of every state>", "name": "<a short sentence>", "expr": "<the expression>", "answers": "<the words of the clause it answers>"}]`
}
// The drafter's answer: the first JSON array in it.
export function parseDraft(text: string): Draft[] {
  const at = text.indexOf('['), end = text.lastIndexOf(']')
  if (at < 0 || end < at) throw new Error('the answer holds no JSON array')
  const xs = JSON.parse(text.slice(at, end + 1)) as Record<string, unknown>[]
  return xs.map(o => ({...(typeof o.method === 'string' && o.method ? {method: o.method} : {}), name: String(o.name ?? '').replace(/:/g, ' -').trim().replace(/[.\s]+$/, ''), expr: String(o.expr ?? '').trim(), answers: String(o.answers ?? '').trim()}))
}
// Each draft read over the code's names as `check` would read it: kept, or refused with why.
export function vetDrafts(x: Extraction, ds: Draft[], opts: LawOpts = {}): {kept: Draft[], refused: {d: Draft, why: string}[]} {
  const kept: Draft[] = [], refused: {d: Draft, why: string}[] = []
  for (const d of ds) {
    if (!d.name || !d.expr) { refused.push({d, why: 'no name or no expression'}); continue }
    try {
      const l = {name: d.name, expr: d.expr, ...(d.method ? {method: d.method} : {})}
      if (isTwoRuns(d.expr)) buildTwoRuns(x, l); else buildLaw(x, l, opts)
      kept.push(d)
    } catch (e) { refused.push({d, why: e instanceof LawError ? e.message : String((e as Error).message)}) }
  }
  return {kept, refused}
}
// The comments to paste: each law with its citation, marked unreviewed.
export const draftComments = (c: string, d: Draft, cite: string, by: string): string[] =>
  [`${c} gdp: law ${d.name}: ${d.expr}`, `${c} gdp: cite ${d.name}: ${cite}: "${d.answers.replace(/\s+/g, ' ')}" [unreviewed: drafted by ${by}]`]
// A citation's review: signed off by a person, marked unreviewed, or neither (written by hand, its review the writer's).
export const reviewOf = (text: string): 'reviewed' | 'unreviewed' | 'unmarked' => (/\[\s*reviewed-by:\s*[^\]]+\]/i.test(text) ? 'reviewed' : /\[\s*unreviewed\b/i.test(text) ? 'unreviewed' : 'unmarked')
