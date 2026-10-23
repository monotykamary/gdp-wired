// Kubernetes v1.37.1, CertificateSigningRequest updates: the registry strategies (pkg/registry/certificates/
// certificates/strategy.go) and validation (pkg/apis/certificates/validation/validation.go). Apache-2.0, (c) The
// Kubernetes Authors.
// https://github.com/kubernetes/kubernetes/blob/f78e722310e50bcaca9276be22276d9e91d91308/pkg/apis/certificates/validation/validation.go
//
// A CSR's status: its conditions (here, how many of each of the types Approved, Denied and Failed it holds) and its
// issued certificate. An update goes through the main resource, /status or /approval: the strategy's PrepareForUpdate
// decides what of the request is kept, then validation accepts the new object or the API server refuses the update and
// nothing changes. Created CSRs start with no status (strategy.go:77-101 "users cannot create pre-approved certificate
// requests"). Line numbers are validation.go's unless strategy.go is named.
import {bool, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'kubernetes/kubernetes', commit: 'f78e722310e50bcaca9276be22276d9e91d91308', licence: 'Apache-2.0', author: 'The Kubernetes Authors', language: 'Go'}

export const csr = () => rule('Kubernetes CSR conditions')
  // One update: the path, the new object's counts of Approved, Denied and Failed conditions, whether they all have
  // status True (:247-253 trueConditionTypes), its status.certificate `newCert` (0: empty; else which content) and whether that
  // content parses as CERTIFICATE PEM blocks (:105-142; empty passes).
  .inputs({path: oneOf('update', 'status', 'approval'), a: nat, d: nat, f: nat, allTrue: bool, newCert: nat, certValid: bool})
  // The stored object's status: condition counts and the certificate. (Validation also tolerates legacy objects that
  // already break a rule, :353-437: both Approved and Denied, duplicate types, an invalid certificate; none is
  // reachable from a CSR created through this API, whose status starts empty, so the tolerances are kept only where
  // they read the counts.)
  .state({nA: 0, nD: 0, nF: 0, cert: 0})
  .flags(({path, a, d, f, allTrue, newCert, certValid, nA, nD, nF, cert: old}) => {
    // getValidationOptions (:353-364): what the old object already breaks is tolerated.
    const allowBoth = nA.gt(0).and(nD.gt(0)) // :366-381
    const allowDup = nA.gt(1).or(nD.gt(1), nF.gt(1)) // :392-409 (duplicate types; other types are not kept)
    // :228-278 validateConditions on the new object.
    const conds = allTrue.and(allowBoth.or(a.eq(0).or(d.eq(0))), allowDup.or(a.atMost(1).and(d.atMost(1), f.atMost(1))))
    // :301-309 no Approved, Denied or Failed condition is removed; :311-326 outside /approval (allowSettingApprovalConditions)
    // none is added or changed (strategy.go:181-183 copies the old instances back when the counts match).
    const keeps = a.atLeast(nA).and(d.atLeast(nD), f.atLeast(nF))
    const approvalOnly = a.eq(nA).and(d.eq(nD))
    // :328-335 the certificate: /status may set it (allowSettingCertificate) but not change it once non-empty
    // (allowResettingCertificate is false); :213-217 a new content must parse (:105-142) unless unchanged (:428-437).
    const certOk = newCert.eq(old).or(old.eq(0).and(certValid))
    return {
      // strategy.go:105-112: the main resource keeps the old status, so it changes nothing here.
      // strategy.go:170-186 /status: conditions and certificate from the request (spec kept).
      takesStatus: path.is('status').and(conds, keeps, approvalOnly, certOk),
      // strategy.go:282-293 /approval: only the conditions from the request; the certificate is the old one.
      takesApproval: path.is('approval').and(conds, keeps),
    }
  })
  .step(({a, d, f, newCert, nA, nD, nF, cert: old, takesStatus, takesApproval}) => {
    const takes = takesStatus.or(takesApproval)
    return {nA: when(takes, a, nA), nD: when(takes, d, nD), nF: when(takes, f, nF), cert: when(takesStatus, newCert, old)}
  })

const r = csr()
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})
export const items: RealItem[] = [{
  id: 'approval/kubernetes/csrConditions',
  domain: 'approval',
  source: cite('pkg/apis/certificates/validation/validation.go', '228-437', 'validateConditions, validateCertificateSigningRequestUpdate'),
  also: [cite('pkg/registry/certificates/certificates/strategy.go', '77-300', 'csrStrategy, csrStatusStrategy, csrApprovalStrategy'),
    cite('staging/src/k8s.io/api/certificates/v1/types.go', '185-250', 'CertificateSigningRequestStatus')],
  summary: 'A CSR is approved or denied through /approval and issued through /status; Approved and Denied are exclusive, no such condition is ever removed, and the certificate, once set, is immutable.',
  expressible: 'partial',
  gaps: [
    {gap: 'other', blocks: 'part', detail: 'conditions are counted per type (Approved, Denied, Failed): their order, reasons, messages, timestamps and other condition types are not kept, and an /approval update that rewrites an Approved condition\'s reason is the same update as one that keeps it'},
    {gap: 'string', blocks: 'part', detail: 'the certificate\'s PEM and x509 parsing is an input (whether the new content is valid), the content an interned value'},
    {gap: 'external', blocks: 'part', detail: 'who may call /approval (the `approve` verb on the signer, checked by the CertificateApproval admission plugin) and the signers that issue certificates are outside the API server\'s validation'},
  ],
  laws: [
    invariant(r, r.law('Approved and Denied are never both set', ({nA, nD}) => nA.eq(0).or(nD.eq(0))),
      'safety', 'docs', 'types.go:248 "Approved and Denied conditions are mutually exclusive."'),
    stepLaw(r, r.stepLaw('an Approved, Denied or Failed condition is never removed', ({nA, nD, nF}, after) => after.nA.atLeast(nA).and(after.nD.atLeast(nD), after.nF.atLeast(nF))),
      'step', 'docs', 'types.go:249 "Approved, Denied, and Failed conditions cannot be removed once added."'),
    stepLaw(r, r.stepLaw('only the approval subresource sets Approved or Denied', ({nA, nD}, after) => after.nA.eq(nA).and(after.nD.eq(nD)), ({path}) => path.is('approval').not()),
      'access', 'docs', 'strategy.go:181-183 "Specifically preserve existing Approved/Denied conditions. Adding/removing Approved/Denied conditions will cause these to fail"'),
    stepLaw(r, r.stepLaw('once populated, the certificate never changes', ({cert}, after) => after.cert.eq(cert), ({cert}) => cert.gt(0)),
      'step', 'docs', 'types.go:192 "This field is set via the /status subresource. Once populated, this field is immutable."'),
    invariant(r, r.law('every request holds at most one Approved condition', ({nA}) => nA.atMost(1)),
      'safety', 'tests', 'validation.go:271-276 duplicate condition types are refused for new data'),
    // Refuted (kept as stated): /status may set a valid certificate on a CSR that is not approved, and /approval may
    // then add Denied; neither update's validation reads the other's field. A law error with no restatement inside
    // this code: types.go:191-194 describe what signers do ("populated with an issued certificate by the signer after
    // an Approved condition is present"), which the API server leaves to them (repro/k8s-csr.ts).
    invariant(r, r.law('a denied request never has a certificate', ({nD, cert}) => nD.eq(0).or(cert.eq(0))),
      'safety', 'docs', 'types.go:194 "If the certificate signing request is denied, a condition of type \\"Denied\\" is added and this field remains empty."'),
  ],
}]
