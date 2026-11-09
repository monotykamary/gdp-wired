import {test,expect} from 'bun:test'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {auditScheduling,readSchedulingReceipt} from './p1-scheduling-audit.ts'
const root=process.env.P1_AUDIT_INPUT??join(import.meta.dir,'p1-tools/audit-fixture')
const text=readFileSync(root+'/probe.log','utf8'),manifest=JSON.parse(readFileSync(root+'/input-manifest.json','utf8')),family=JSON.parse(readFileSync(root+'/family.json','utf8'))
const receipt=()=>readSchedulingReceipt(text)
test('accepts complete native receipts but refuses a whole-Paxos work increase',()=>{const r=auditScheduling(receipt(),manifest,family);expect(r.issues).toEqual([]);expect(r.p1Regression).toBe(true);expect(r.p1Restored).toBe(true);expect(r.paxosFullDelta).toBe(530);expect(r.jointCriterion).toBe(false)})
test('refuses missing and duplicate attempts',()=>{for(const duplicate of [false,true]){const r=receipt();r.records.pop();if(duplicate)r.records.push(r.records[0]);expect(auditScheduling(r,manifest,family).issues.length).toBeGreaterThan(0)}})
test('refuses changed native checker source',()=>{const r=receipt();r.sources[1].kernelHashes['kernel/kernel.ts']='changed';expect(auditScheduling(r,manifest,family).issues).toContain('current: kernel changed')})
test('refuses unverified p1 certificates and changed original families',()=>{const r=receipt();r.records[0].p1.audit.exit=1;expect(auditScheduling(r,manifest,family).issues.length).toBeGreaterThan(0);expect(auditScheduling(receipt(),manifest,{...family,m:{}}).issues.length).toBeGreaterThan(0)})
test('refuses mismatched input identity and frozen Paxos work',()=>{const r=receipt();r.inputManifestSha256='wrong';r.records[1].paxos.trace.solver++;expect(auditScheduling(r,manifest,family).issues).toContain('input manifest');expect(auditScheduling(r,manifest,family).issues).toContain('current/1: frozen Paxos work')})
test('refuses corrupt archives',()=>expect(()=>readSchedulingReceipt(text.replace('"encodedBytes":229340','"encodedBytes":1'))).toThrow())
