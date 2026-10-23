// Repro for access/cedar-examples/documentCloud: runs the ORIGINAL policy set (cedar-examples@268c5618, fetched into a
// temp dir) through the Cedar engine (@cedar-policy/cedar-wasm 4.14.0, installed into the same temp dir) on the
// requests the refuted decisions' witnesses describe, and prints Cedar's decision.
//   bun research/realworld/repro/cedar-documentcloud.ts
import {execSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const dir = mkdtempSync(join(tmpdir(), 'cedar-dc-'))
const base = 'https://raw.githubusercontent.com/cedar-policy/cedar-examples/268c5618eb145052c21f07c2e14e1781482a23e9/cedar-example-use-cases/document_cloud'
const get = async (f: string) => { const t = await (await fetch(`${base}/${f}`)).text(); writeFileSync(join(dir, f), t); return t }
const policies = await get('policies.cedar')
const entities = JSON.parse(await get('entities.json')) as unknown[]
execSync('npm init -y >/dev/null && npm install --silent @cedar-policy/cedar-wasm@4.14.0', {cwd: dir, stdio: 'inherit'})
const cedar = await import(join(dir, 'node_modules/@cedar-policy/cedar-wasm/nodejs/cedar_wasm.js')) as {isAuthorized: (c: unknown) => {type: string, response?: {decision: string, diagnostics: {reason: string[], errors: unknown[]}}, errors?: unknown}}

// Two more entities for the public request: the Public::"public" principal the policies name (entities.json has only
// Public::"unauthenticated"), and nothing else changes.
const ents = [...entities, {uid: {type: 'Public', id: 'public'}, attrs: {}, parents: []}]
const ask = (label: string, principal: {type: string, id: string}, action: string, resource: {type: string, id: string}, authenticated: boolean) => {
  const out = cedar.isAuthorized({principal, action: {type: 'Action', id: action}, resource, context: {is_authenticated: authenticated}, policies: {staticPolicies: policies}, entities: ents})
  console.log(`${label}: ${out.type === 'success' ? `${out.response!.decision} (reasons ${JSON.stringify(out.response!.diagnostics.reason)})` : JSON.stringify(out.errors)}`)
}
// "the owner can delete their document": alice (blocks bob, not herself) deletes alice_public, which she owns.
ask('alice DeleteDocument alice_public, authenticated', {type: 'User', id: 'alice'}, 'DeleteDocument', {type: 'Document', id: 'alice_public'}, true)
// "the public can view a public document": alice_public is not private and has publicAccess "view".
ask('Public::"public" ViewDocument alice_public, unauthenticated', {type: 'Public', id: 'public'}, 'ViewDocument', {type: 'Document', id: 'alice_public'}, false)
ask('Public::"public" ViewDocument alice_public, authenticated', {type: 'Public', id: 'public'}, 'ViewDocument', {type: 'Document', id: 'alice_public'}, true)
ask('Public::"unauthenticated" ViewDocument alice_public, unauthenticated', {type: 'Public', id: 'unauthenticated'}, 'ViewDocument', {type: 'Document', id: 'alice_public'}, false)
// For contrast: alice views her own document (allowed).
ask('alice ViewDocument alice_public, authenticated', {type: 'User', id: 'alice'}, 'ViewDocument', {type: 'Document', id: 'alice_public'}, true)
