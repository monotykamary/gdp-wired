// Repro for quota/kubernetes/ResourceQuota.CheckRequest#"every admitted request leaves the usage it charges within the
// hard limits" (refuted by a status write). Runs the ORIGINAL CheckRequest from k8s.io/apiserver v0.37.1 (the
// staging copy of kubernetes v1.37.1, commit f78e7223) with a stand-in evaluator whose Usage is the counterexample's
// `New` map, and the quota of the counterexample: hard {r0: 0, r3: 0}, used {r0: 0, r3: 0}.
// Run (in a fresh temp dir, nothing vendored):
//
//	d=$(mktemp -d) && cp research/realworld/repro/k8s-status-quota.go $d/main.go && cd $d && go mod init repro && \
//	go get k8s.io/apiserver/pkg/admission/plugin/resourcequota@v0.37.1 k8s.io/api@v0.37.1 k8s.io/apimachinery@v0.37.1 && \
//	go mod tidy && go run .
//
// Prints (v0.37.1):
//
//	subresource "": refused: pods "p" is forbidden: exceeded quota: q, requested: r0=1, used: r0=0, limited: r0=0
//	subresource "status": admitted, used r0 = 1, hard r0 = 0
package main

import (
	"fmt"

	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/resource"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/admission"
	"k8s.io/apiserver/pkg/admission/plugin/resourcequota"
	quota "k8s.io/apiserver/pkg/quota/v1"
)

// A stand-in for the object's evaluator: it handles everything, matches the quota, accepts every constraint, and
// measures every object at the counterexample's usage {r0: 1, r1: 1, r2: 1}.
type eval struct{}

func (eval) Constraints([]corev1.ResourceName, runtime.Object) error     { return nil }
func (eval) GroupResource() schema.GroupResource                         { return schema.GroupResource{Resource: "pods"} }
func (eval) Handles(admission.Attributes) bool                           { return true }
func (eval) Matches(*corev1.ResourceQuota, runtime.Object) (bool, error) { return true, nil }
func (eval) MatchingScopes(runtime.Object, []corev1.ScopedResourceSelectorRequirement) ([]corev1.ScopedResourceSelectorRequirement, error) {
	return nil, nil
}
func (eval) UncoveredQuotaScopes(_, _ []corev1.ScopedResourceSelectorRequirement) ([]corev1.ScopedResourceSelectorRequirement, error) {
	return nil, nil
}
func (eval) MatchingResources(in []corev1.ResourceName) []corev1.ResourceName { return in }
func (eval) Usage(runtime.Object) (corev1.ResourceList, error) {
	q := resource.MustParse("1")
	return corev1.ResourceList{"r0": q, "r1": q, "r2": q}, nil
}
func (eval) UsageStats(quota.UsageStatsOptions) (quota.UsageStats, error) {
	return quota.UsageStats{}, nil
}

func main() {
	zero := resource.MustParse("0")
	rq := corev1.ResourceQuota{ObjectMeta: metav1.ObjectMeta{Name: "q", Namespace: "ns"},
		Status: corev1.ResourceQuotaStatus{Hard: corev1.ResourceList{"r0": zero, "r3": zero}, Used: corev1.ResourceList{"r0": zero, "r3": zero}}}
	pod := &corev1.Pod{ObjectMeta: metav1.ObjectMeta{Name: "p", Namespace: "ns"}}
	for _, sub := range []string{"", "status"} {
		a := admission.NewAttributesRecord(pod, nil, schema.GroupVersionKind{Version: "v1", Kind: "Pod"}, "ns", "p",
			schema.GroupVersionResource{Version: "v1", Resource: "pods"}, sub, admission.Create, &metav1.CreateOptions{}, false, nil)
		out, err := resourcequota.CheckRequest([]corev1.ResourceQuota{rq}, a, eval{}, nil)
		if err != nil {
			fmt.Printf("subresource %q: refused: %v\n", sub, err)
			continue
		}
		used := out[0].Status.Used[corev1.ResourceName("r0")]
		hard := out[0].Status.Hard[corev1.ResourceName("r0")]
		fmt.Printf("subresource %q: admitted, used r0 = %s, hard r0 = %s\n", sub, used.String(), hard.String())
	}
}
