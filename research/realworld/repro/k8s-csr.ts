// Repro for approval/kubernetes/csrConditions' refuted law "a denied request never has a certificate" (Go: not run;
// reasoned from the source at kubernetes/kubernetes@f78e722310e50bcaca9276be22276d9e91d91308, Apache-2.0, and
// replayed on the rule).
//
// 1. PUT .../certificatesigningrequests/<name>/status with status.certificate set (valid PEM) on a CSR that has no
//    conditions: csrStatusStrategy.PrepareForUpdate (strategy.go:170-186) keeps the new certificate and conditions;
//    ValidateCertificateSigningRequestStatusUpdate (validation.go:285-289) sets allowSettingCertificate, and
//    validateCertificateSigningRequestUpdate (:297-337) only forbids changing a certificate that is already non-empty
//    and checks the PEM (:105-142, :213-217). Nothing reads the Approved condition.
// 2. PUT .../<name>/approval adding a Denied condition: csrApprovalStrategy.PrepareForUpdate (strategy.go:282-293)
//    takes the conditions and keeps the old certificate; validateConditions (:228-278) checks Approved/Denied
//    exclusivity, duplicates and statuses. Nothing reads status.certificate.
// The stored CSR is Denied with a certificate, which types.go:194 says does not happen ("If the certificate signing
// request is denied, a condition of type "Denied" is added and this field remains empty"): that sentence describes
// the signers (kube-controller-manager's signer checks IsCertificateRequestApproved before signing), not the API
// server, so it is a law error. Who may call /status and /approval is RBAC and the CertificateApproval/
// CertificateSigning admission plugins, outside the rule.
//   bun research/realworld/repro/k8s-csr.ts
import {csr} from '../items/invapprove-k8s.ts'

const r = csr(), m = r.interpreter(), p = r.encodeParams({})
let st = m.init(p)
for (const i of [{path: 'status', a: 0, d: 0, f: 0, allTrue: true, newCert: 1, certValid: true}, {path: 'approval', a: 0, d: 1, f: 0, allTrue: true, newCert: 0, certValid: false}]) {
  st = m.step(p, st, r.encodeInput(i))
  console.log(i.path.padEnd(9), JSON.stringify(r.decode(st)))
}
