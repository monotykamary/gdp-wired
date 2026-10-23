#!/usr/bin/env bash
# Repro for access/kubernetes/rbacRuleAllows "a rule naming resources never allows an unnamed request": runs the
# ORIGINAL matchers (pkg/apis/rbac/v1/evaluation_helpers.go) and RuleAllows (plugin/pkg/auth/authorizer/rbac/rbac.go,
# the function cut out of the file as it is) at kubernetes v1.37.1 (f78e7223), fetched into a temp dir, against
# k8s.io/api's rbac/v1 types, on the counterexample's request: a resource request with no name ("") and a rule whose
# ResourceNames lists "" (with verbs and resources that match).
#   bash research/realworld/repro/k8s-rulenames.sh
set -euo pipefail
dir=$(mktemp -d)
base=https://raw.githubusercontent.com/kubernetes/kubernetes/f78e722310e50bcaca9276be22276d9e91d91308
mkdir -p "$dir/helpers"
curl -sf "$base/pkg/apis/rbac/v1/evaluation_helpers.go" > "$dir/helpers/evaluation_helpers.go"
# RuleAllows, cut from rbac.go as it is (its lines from `func RuleAllows` to the closing brace).
curl -sf "$base/plugin/pkg/auth/authorizer/rbac/rbac.go" | awk '/^func RuleAllows/{p=1} p{print} p&&/^}/{exit}' > "$dir/ruleallows.txt"
cd "$dir"
# The helpers file belongs to package v1 (it imports k8s.io/api/rbac/v1 as rbacv1); keep it as its own package.
sed -i.bak 's/^package v1$/package helpers/' helpers/evaluation_helpers.go && rm helpers/*.bak
cat > main.go <<'GO'
package main

import (
	"fmt"

	rbacv1 "k8s.io/api/rbac/v1"
	rbacv1helpers "example.com/repro/helpers"
)

// The four methods of authorizer.Attributes that RuleAllows reads, for one request.
type attrs struct{ verb, group, resource, sub, name, path string; resourceRequest bool }

func (a attrs) IsResourceRequest() bool  { return a.resourceRequest }
func (a attrs) GetVerb() string          { return a.verb }
func (a attrs) GetAPIGroup() string      { return a.group }
func (a attrs) GetResource() string      { return a.resource }
func (a attrs) GetSubresource() string   { return a.sub }
func (a attrs) GetName() string          { return a.name }
func (a attrs) GetPath() string          { return a.path }

type Attributes interface {
	IsResourceRequest() bool
	GetVerb() string
	GetAPIGroup() string
	GetResource() string
	GetSubresource() string
	GetName() string
	GetPath() string
}

GO
sed 's/requestAttributes authorizer.Attributes/requestAttributes Attributes/' ruleallows.txt >> main.go
cat >> main.go <<'GO'

func main() {
	create := attrs{verb: "create", group: "", resource: "pods", resourceRequest: true}
	named := rbacv1.PolicyRule{Verbs: []string{"create"}, APIGroups: []string{""}, Resources: []string{"pods"}, ResourceNames: []string{""}}
	other := rbacv1.PolicyRule{Verbs: []string{"create"}, APIGroups: []string{""}, Resources: []string{"pods"}, ResourceNames: []string{"web"}}
	fmt.Println(`create pods (no name), rule ResourceNames [""]:   allowed =`, RuleAllows(create, &named))
	fmt.Println(`create pods (no name), rule ResourceNames ["web"]: allowed =`, RuleAllows(create, &other))
}
GO
cat > go.mod <<'MOD'
module example.com/repro

go 1.22
MOD
go get k8s.io/api@v0.37.1 >/dev/null 2>&1 || go get k8s.io/api@latest >/dev/null 2>&1
go mod tidy >/dev/null 2>&1
go run .
