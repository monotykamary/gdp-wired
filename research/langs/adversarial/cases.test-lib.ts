// The adversarial round's cases (this directory: RESULTS.md, cases.json), as tests in each front end's own test file:
// none is a checked proof of its false law ('n stays zero'); the four that were (WRONG: j01, j03, j04, p12) and the
// ones refused only incidentally (p01–p03, r01, t01) are refused for their own reason.
import {expect} from 'bun:test'
import {readFileSync} from 'node:fs'
import {proveRule} from '../../../core/dsl.ts'
import type {Extraction} from '../../../core/extract.ts'

export const ADV = new URL('./', import.meta.url).pathname
export type Case = {id: string, lang: string, attack: string, file: string, discover?: boolean}
export const cases = (lang: string): Case[] => (JSON.parse(readFileSync(`${ADV}cases.json`, 'utf8')) as Case[]).filter(c => c.lang === lang)
const WHY: Record<string, RegExp> = {
  p01: /given the rule's state/, p02: /given the rule's state/, p03: /given the rule's state/, r01: /given the rule's state/,
  j01: /given the rule's state/, j03: /given the rule's state/, j04: /given the rule's state/, t01: /given the object's state/,
  p12: /two injected dependencies of one type/,
  s01: /given the rule's state/, s02: /given the rule's state/, s03: /given the rule's state/, s04: /two injected dependencies of one type/,
}
export function judge(c: Case, x: Extraction) {
  if (WHY[c.id]) { expect(x.ok).toBe(false); expect(x.refusals.map(r => r.what).join('; ')).toMatch(WHY[c.id]!); return }
  if (!x.ok) return
  const r = x.rule as never as {law: (n: string, f: (s: {n: {eq: (k: number) => unknown}}) => unknown) => never}
  const v = proveRule(x.rule!, [...(x.invariants ?? []), r.law('n stays zero', ({n}) => n.eq(0))], {search: false})
  expect(v.proven && v.checked).toBeFalsy()
}
