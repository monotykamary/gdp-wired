// The Go front end's reader (core/extract-go.ts): one package's files parsed by go/parser and checked by go/types, and
// printed as JSON, each expression with its type and, where go/types folds it, its constant value. Nothing is decided
// here: the TypeScript side reads the JSON, executes a step symbolically and refuses what is outside its subset. An
// import outside the standard library is not loaded (its package is empty here), so whatever the code reads of it has
// an invalid type, which the TypeScript side refuses where it is read.
//
//	go run . <dir>            every .go file of the package in <dir> (its build constraints, not its tests)
//	go run . <file.go>...     the files given
package main

import (
	"encoding/json"
	"fmt"
	"go/ast"
	"go/build"
	"go/constant"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"

	"strings"
)

type J = map[string]any

var (
	fset   = token.NewFileSet()
	info   = &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{}, Uses: map[*ast.Ident]types.Object{}, Selections: map[*ast.SelectorExpr]*types.Selection{}, Implicits: map[ast.Node]types.Object{}}
	tids   = map[types.Type]int{}
	ttab   []J
	pkg    *types.Package
	errors []string
)

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: reader <dir> | <file.go>...")
		os.Exit(2)
	}
	var files []string
	if st, err := os.Stat(os.Args[1]); err == nil && st.IsDir() {
		bp, err := build.Default.ImportDir(os.Args[1], 0)
		if err != nil {
			fail(err)
		}
		for _, f := range bp.GoFiles {
			files = append(files, filepath.Join(os.Args[1], f))
		}
	} else {
		files = os.Args[1:]
	}
	var asts []*ast.File
	for _, f := range files {
		a, err := parser.ParseFile(fset, f, nil, parser.SkipObjectResolution)
		if err != nil {
			fail(err)
		}
		asts = append(asts, a)
	}
	std := importer.Default()
	conf := types.Config{
		Importer: importerFunc(func(path string) (*types.Package, error) {
			if isStd(path) {
				return std.Import(path)
			}
			// Another package outside the standard library: read from its source where `go list` finds it (its names'
			// types, so its structs are data the step can read), its own imports empty (their names undefined, their
			// types invalid); empty itself where it isn't found.
			return foreignPackage(path, os.Args[1], std), nil
		}),
		Error: func(err error) { errors = append(errors, err.Error()) },
	}
	pkg, _ = conf.Check(asts[0].Name.Name, fset, asts, info)
	out := J{"package": asts[0].Name.Name}
	var fs, funcs, typs, consts, vars []J
	for i, a := range asts {
		imps := []J{}
		for _, im := range a.Imports {
			path := strings.Trim(im.Path.Value, `"`)
			name := ""
			if im.Name != nil {
				name = im.Name.Name
			}
			imps = append(imps, J{"path": path, "name": name, "std": isStd(path)})
		}
		fs = append(fs, J{"name": filepath.Base(files[i]), "imports": imps})
		for _, d := range a.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				funcs = append(funcs, funcDecl(d))
			case *ast.GenDecl:
				for _, s := range d.Specs {
					switch s := s.(type) {
					case *ast.TypeSpec:
						obj := info.Defs[s.Name]
						typs = append(typs, J{"name": s.Name.Name, "t": tid(obj.Type()), "p": pos(s.Pos()), "span": span(s)})
					case *ast.ValueSpec:
						for _, n := range s.Names {
							obj := info.Defs[n]
							if obj == nil {
								continue
							}
							if c, ok := obj.(*types.Const); ok {
								consts = append(consts, J{"name": n.Name, "t": tid(c.Type()), "c": cval(c.Val()), "p": pos(n.Pos())})
							} else {
								vj := J{"name": n.Name, "t": tid(obj.Type()), "p": pos(n.Pos())}
								if len(s.Values) == len(s.Names) {
									for k, m := range s.Names {
										if m == n {
											vj["init"] = expr(s.Values[k])
										}
									}
								}
								vars = append(vars, vj)
							}
						}
					}
				}
			}
		}
	}
	out["files"], out["funcs"], out["types"], out["consts"], out["vars"], out["errors"] = fs, funcs, typs, consts, vars, errors
	out["ttab"] = ttab
	enc := json.NewEncoder(os.Stdout)
	if err := enc.Encode(out); err != nil {
		fail(err)
	}
}

// Another package, one level deep: type-checked from its files with its own imports left empty, its errors (names of
// those imports, undefined) kept out of the package's own.
var foreign = map[string]*types.Package{}

func foreignPackage(path, from string, std types.Importer) *types.Package {
	if p, ok := foreign[path]; ok {
		return p
	}
	empty := func(p string) *types.Package {
		q := types.NewPackage(p, guessName(p))
		q.MarkComplete()
		return q
	}
	foreign[path] = empty(path)
	dir := from
	if st, err := os.Stat(from); err != nil || !st.IsDir() {
		dir = filepath.Dir(from)
	}
	pdir := localDir(path, dir)
	if pdir == "" {
		return foreign[path]
	}
	bp, err := build.Default.ImportDir(pdir, 0)
	if err != nil || len(bp.GoFiles) == 0 {
		return foreign[path]
	}
	var asts []*ast.File
	for _, f := range bp.GoFiles {
		a, err := parser.ParseFile(fset, filepath.Join(pdir, f), nil, parser.SkipObjectResolution)
		if err != nil {
			return foreign[path]
		}
		asts = append(asts, a)
	}
	conf := types.Config{
		Importer: importerFunc(func(p string) (*types.Package, error) {
			if isStd(p) {
				return std.Import(p)
			}
			return empty(p), nil
		}),
		Error: func(error) {},
	}
	tp, _ := conf.Check(path, fset, asts, nil)
	if tp == nil {
		return foreign[path]
	}
	foreign[path] = tp
	return tp
}

// Where a package of the module the code is in lives: under the module's root, or under a local replace of its go.mod
// (Kubernetes's staging modules). Another module's (downloaded) is not read: "".
func localDir(path, from string) string {
	root := from
	for {
		if _, err := os.Stat(filepath.Join(root, "go.mod")); err == nil {
			break
		}
		up := filepath.Dir(root)
		if up == root {
			return ""
		}
		root = up
	}
	data, err := os.ReadFile(filepath.Join(root, "go.mod"))
	if err != nil {
		return ""
	}
	under := func(base, mod string) string {
		if path == mod {
			return base
		}
		if strings.HasPrefix(path, mod+"/") {
			return filepath.Join(base, filepath.FromSlash(path[len(mod)+1:]))
		}
		return ""
	}
	inReplace := false
	for _, line := range strings.Split(string(data), "\n") {
		f := strings.Fields(strings.SplitN(line, "//", 2)[0])
		switch {
		case len(f) == 2 && f[0] == "module":
			if d := under(root, strings.Trim(f[1], `"`)); d != "" {
				return existing(d)
			}
		case len(f) >= 2 && f[0] == "replace" && f[1] == "(":
			inReplace = true
		case inReplace && len(f) == 1 && f[0] == ")":
			inReplace = false
		default:
			if len(f) > 0 && f[0] == "replace" {
				f = f[1:]
			} else if !inReplace {
				continue
			}
			// a [v] => ./local [v]
			for i, x := range f {
				if x == "=>" && i+1 < len(f) && i >= 1 && (strings.HasPrefix(f[i+1], "./") || strings.HasPrefix(f[i+1], "../")) {
					if d := under(filepath.Join(root, filepath.FromSlash(f[i+1])), f[0]); d != "" {
						return existing(d)
					}
				}
			}
		}
	}
	return ""
}
func existing(d string) string {
	if st, err := os.Stat(d); err == nil && st.IsDir() {
		return d
	}
	return ""
}

type importerFunc func(string) (*types.Package, error)

func (f importerFunc) Import(path string) (*types.Package, error) { return f(path) }

// The name the check's harness imports another package by (two packages may share a name: k8s.io/api/rbac/v1 and
// k8s.io/apimachinery/pkg/apis/meta/v1 are both v1). core/extract-go-check.ts's alias is the same.
func alias(path string) string {
	b := []byte("gdp_")
	for _, c := range []byte(path) {
		if c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' {
			b = append(b, c)
		} else {
			b = append(b, '_')
		}
	}
	return string(b)
}
func isStd(path string) bool {
	first := strings.SplitN(path, "/", 2)[0]
	return !strings.Contains(first, ".") && path != "C"
}
func guessName(path string) string {
	last := path[strings.LastIndex(path, "/")+1:]
	if strings.HasPrefix(last, "v") && len(last) > 1 && strings.Trim(last[1:], "0123456789") == "" && strings.Contains(path, "/") {
		rest := path[:strings.LastIndex(path, "/")]
		last = rest[strings.LastIndex(rest, "/")+1:]
	}
	last = strings.TrimPrefix(last, "go-")
	if i := strings.IndexAny(last, ".-"); i >= 0 {
		last = last[:i]
	}
	return last
}
func fail(err error) {
	fmt.Fprintln(os.Stderr, err)
	os.Exit(1)
}

// --- positions ------------------------------------------------------------------------------------------------------
func pos(p token.Pos) string {
	if !p.IsValid() {
		return ""
	}
	q := fset.Position(p)
	return fmt.Sprintf("%s:%d:%d", filepath.Base(q.Filename), q.Line, q.Column)
}
func span(n ast.Node) []int { return []int{fset.Position(n.Pos()).Line, fset.Position(n.End()).Line} }

// --- types: a table, each type once (named types by name, so recursive ones end) -----------------------------------
func tid(t types.Type) int {
	if t == nil {
		t = types.Typ[types.Invalid]
	}
	if i, ok := tids[t]; ok {
		return i
	}
	// Identical types share an entry (types.Identical), so the TypeScript side compares them by number.
	for u, i := range tids {
		if types.Identical(u, t) {
			tids[t] = i
			return i
		}
	}
	i := len(ttab)
	tids[t] = i
	ttab = append(ttab, nil)
	d := describe(t)
	// The type as Go writes it in the package (the check's harness declares values of it).
	d["go"] = types.TypeString(t, func(p *types.Package) string {
		if p == pkg {
			return ""
		}
		if !isStd(p.Path()) {
			return alias(p.Path())
		}
		return p.Name()
	})
	ttab[i] = d
	return i
}

func describe(t types.Type) J {
	switch t := t.(type) {
	case *types.Basic:
		return basic(t, "", "")
	case *types.Named:
		obj := t.Obj()
		path := ""
		if obj.Pkg() != nil {
			path = obj.Pkg().Path()
		}
		own := obj.Pkg() == pkg
		j := J{"name": obj.Name(), "pkg": path, "own": own}
		if t.TypeParams().Len() > 0 {
			j["generic"] = true
		}
		if t.TypeArgs().Len() > 0 {
			args := []int{}
			for i := 0; i < t.TypeArgs().Len(); i++ {
				args = append(args, tid(t.TypeArgs().At(i)))
			}
			j["args"] = args
		}
		// Another package's named type: opaque, but an integer, boolean or string one keeps its basic kind
		// (time.Duration is an int64), and math/big.Int, error and the like are recognized by name.
		if !own {
			if b, ok := t.Underlying().(*types.Basic); ok {
				for k, v := range basic(b, obj.Name(), path) {
					j[k] = v
				}
				return j
			}
			j["k"] = "ext"
			if _, ok := t.Underlying().(*types.Interface); ok {
				j["iface"] = true
			}
			// Another package's struct (outside the standard library): its fields too, as data. Its methods stay
			// another package's code.
			if st, ok := t.Underlying().(*types.Struct); ok && strings.Contains(strings.Split(path, "/")[0], ".") {
				fields := []J{}
				for i := 0; i < st.NumFields(); i++ {
					f := st.Field(i)
					fields = append(fields, J{"name": f.Name(), "t": tid(f.Type()), "embedded": f.Embedded(), "exported": f.Exported()})
				}
				j["xfields"] = fields
			}
			if obj.Name() == "error" && path == "" {
				j["k"] = "error"
			}
			return j
		}
		u := describe(t.Underlying())
		for k, v := range u {
			if k != "name" && k != "pkg" {
				j[k] = v
			}
		}
		methods := []J{}
		for i := 0; i < t.NumMethods(); i++ {
			m := t.Method(i)
			sig := m.Type().(*types.Signature)
			_, ptr := sig.Recv().Type().(*types.Pointer)
			methods = append(methods, J{"name": m.Name(), "ptr": ptr})
		}
		j["methods"] = methods
		return j
	case *types.Pointer:
		return J{"k": "ptr", "elem": tid(t.Elem())}
	case *types.Struct:
		fields := []J{}
		for i := 0; i < t.NumFields(); i++ {
			f := t.Field(i)
			fields = append(fields, J{"name": f.Name(), "t": tid(f.Type()), "embedded": f.Embedded(), "exported": f.Exported()})
		}
		return J{"k": "struct", "fields": fields}
	case *types.Map:
		return J{"k": "map", "key": tid(t.Key()), "elem": tid(t.Elem())}
	case *types.Slice:
		return J{"k": "slice", "elem": tid(t.Elem())}
	case *types.Array:
		return J{"k": "array", "len": t.Len(), "elem": tid(t.Elem())}
	case *types.Signature:
		ps, rs := []int{}, []int{}
		for i := 0; i < t.Params().Len(); i++ {
			ps = append(ps, tid(t.Params().At(i).Type()))
		}
		for i := 0; i < t.Results().Len(); i++ {
			rs = append(rs, tid(t.Results().At(i).Type()))
		}
		return J{"k": "func", "params": ps, "results": rs, "variadic": t.Variadic()}
	case *types.Tuple:
		es := []int{}
		for i := 0; i < t.Len(); i++ {
			es = append(es, tid(t.At(i).Type()))
		}
		return J{"k": "tuple", "elems": es}
	case *types.Interface:
		return J{"k": "iface", "empty": t.Empty()}
	case *types.TypeParam:
		return J{"k": "typeparam", "name": t.Obj().Name()}
	case *types.Chan:
		return J{"k": "chan"}
	case *types.Alias:
		return describe(types.Unalias(t))
	}
	return J{"k": "other", "s": t.String()}
}
func basic(b *types.Basic, name, path string) J {
	j := J{}
	if name != "" {
		j["name"], j["pkg"] = name, path
	}
	info := b.Info()
	switch {
	case b.Kind() == types.Invalid:
		j["k"] = "invalid"
	case b.Kind() == types.UntypedNil:
		j["k"] = "nil"
	case info&types.IsBoolean != 0:
		j["k"] = "bool"
	case info&types.IsString != 0:
		j["k"] = "string"
	case info&types.IsInteger != 0:
		j["k"] = "int"
		j["signed"] = info&types.IsUnsigned == 0
		j["bits"] = map[types.BasicKind]int{types.Int: 64, types.Int8: 8, types.Int16: 16, types.Int32: 32, types.Int64: 64, types.Uint: 64, types.Uint8: 8, types.Uint16: 16, types.Uint32: 32, types.Uint64: 64, types.Uintptr: 64, types.UntypedInt: 0, types.UntypedRune: 32}[b.Kind()]
		if info&types.IsUntyped != 0 {
			j["untyped"] = true
		}
	case info&types.IsFloat != 0:
		j["k"] = "float"
	case info&types.IsComplex != 0:
		j["k"] = "complex"
	default:
		j["k"] = "other"
		j["s"] = b.String()
	}
	if b.Kind() == types.UnsafePointer {
		j["k"] = "other"
	}
	return j
}
func cval(v constant.Value) any {
	if v == nil {
		return nil
	}
	switch v.Kind() {
	case constant.Int:
		return J{"int": v.ExactString()}
	case constant.Bool:
		return J{"bool": constant.BoolVal(v)}
	case constant.String:
		return J{"str": constant.StringVal(v)}
	case constant.Float:
		// A float constant that is a whole number is still a float (its type says so); its text is kept for the reason.
		return J{"float": v.ExactString()}
	}
	return J{"other": v.String()}
}

// --- declarations ---------------------------------------------------------------------------------------------------
func funcDecl(d *ast.FuncDecl) J {
	j := J{"name": d.Name.Name, "p": pos(d.Pos()), "span": span(d)}
	if d.Recv != nil && len(d.Recv.List) == 1 {
		r := d.Recv.List[0]
		t := info.Types[r.Type].Type
		_, ptr := t.(*types.Pointer)
		base := t
		if ptr {
			base = t.(*types.Pointer).Elem()
		}
		name := ""
		if n, ok := base.(*types.Named); ok {
			name = n.Obj().Name()
		}
		rj := J{"t": tid(t), "ptr": ptr, "type": name}
		if len(r.Names) == 1 && r.Names[0].Name != "_" {
			rj["name"], rj["id"] = r.Names[0].Name, objID(info.Defs[r.Names[0]])
		}
		j["recv"] = rj
	}
	if d.Type.TypeParams != nil && d.Type.TypeParams.NumFields() > 0 {
		j["generic"] = true
	}
	j["params"] = fields(d.Type.Params)
	j["results"] = fields(d.Type.Results)
	if d.Body != nil {
		j["body"] = block(d.Body)
	}
	return j
}
func fields(fl *ast.FieldList) []J {
	out := []J{}
	if fl == nil {
		return out
	}
	for _, f := range fl.List {
		t := tid(info.Types[f.Type].Type)
		_, variadic := f.Type.(*ast.Ellipsis)
		if len(f.Names) == 0 {
			out = append(out, J{"t": t, "variadic": variadic})
		}
		for _, n := range f.Names {
			out = append(out, J{"name": n.Name, "id": objID(info.Defs[n]), "t": tid(info.Defs[n].Type()), "variadic": variadic, "ts": types.ExprString(f.Type)})
		}
	}
	return out
}

// An object's identity: where it is declared (so the TypeScript side needs no scopes of its own).
func objID(o types.Object) string {
	if o == nil {
		return ""
	}
	if o.Pkg() != nil && o.Pkg() != pkg {
		return o.Pkg().Path() + "." + o.Name()
	}
	if o.Parent() == pkg.Scope() || o.Parent() == nil {
		if fn, ok := o.(*types.Func); ok {
			if r := fn.Type().(*types.Signature).Recv(); r != nil {
				return "method:" + o.Name()
			}
		}
		return "pkg:" + o.Name()
	}
	q := fset.Position(o.Pos())
	return fmt.Sprintf("%s:%d", filepath.Base(q.Filename), q.Offset)
}

// --- statements -----------------------------------------------------------------------------------------------------
func block(b *ast.BlockStmt) []J {
	out := []J{}
	if b == nil {
		return out
	}
	for _, s := range b.List {
		out = append(out, stmt(s))
	}
	return out
}
func stmt(s ast.Stmt) J {
	j := J{"p": pos(s.Pos())}
	switch s := s.(type) {
	case *ast.BlockStmt:
		j["s"], j["b"] = "block", block(s)
	case *ast.ExprStmt:
		j["s"], j["x"] = "expr", expr(s.X)
	case *ast.AssignStmt:
		j["s"], j["op"], j["l"], j["r"] = "assign", s.Tok.String(), exprs(s.Lhs), exprs(s.Rhs)
	case *ast.IncDecStmt:
		j["s"], j["op"], j["x"] = "incdec", s.Tok.String(), expr(s.X)
	case *ast.IfStmt:
		j["s"], j["c"], j["then"] = "if", expr(s.Cond), block(s.Body)
		if s.Init != nil {
			j["init"] = stmt(s.Init)
		}
		if s.Else != nil {
			j["else"] = stmt(s.Else)
		}
	case *ast.SwitchStmt:
		j["s"] = "switch"
		if s.Init != nil {
			j["init"] = stmt(s.Init)
		}
		if s.Tag != nil {
			j["tag"] = expr(s.Tag)
		}
		cases := []J{}
		for _, c := range s.Body.List {
			cc := c.(*ast.CaseClause)
			cj := J{"b": []J{}, "p": pos(cc.Pos())}
			if cc.List == nil {
				cj["default"] = true
			} else {
				cj["list"] = exprs(cc.List)
			}
			body := []J{}
			for _, x := range cc.Body {
				body = append(body, stmt(x))
			}
			cj["b"] = body
			cases = append(cases, cj)
		}
		j["cases"] = cases
	case *ast.TypeSwitchStmt:
		j["s"] = "typeswitch"
	case *ast.ReturnStmt:
		j["s"], j["r"] = "return", exprs(s.Results)
	case *ast.ForStmt:
		j["s"] = "for"
	case *ast.RangeStmt:
		j["s"] = "range"
		j["x"] = expr(s.X)
	case *ast.DeclStmt:
		j["s"] = "decl"
		specs := []J{}
		if g, ok := s.Decl.(*ast.GenDecl); ok {
			for _, sp := range g.Specs {
				if vs, ok := sp.(*ast.ValueSpec); ok {
					names := []J{}
					for _, n := range vs.Names {
						o := info.Defs[n]
						if o == nil {
							continue
						}
						nj := J{"name": n.Name, "id": objID(o), "t": tid(o.Type())}
						if c, ok := o.(*types.Const); ok {
							nj["c"] = cval(c.Val())
						}
						names = append(names, nj)
					}
					specs = append(specs, J{"names": names, "v": exprs(vs.Values), "const": g.Tok == token.CONST})
				} else {
					specs = append(specs, J{"type": true})
				}
			}
		}
		j["specs"] = specs
	case *ast.DeferStmt:
		j["s"], j["x"] = "defer", expr(s.Call)
	case *ast.GoStmt:
		j["s"] = "go"
	case *ast.BranchStmt:
		j["s"], j["tok"] = "branch", s.Tok.String()
		if s.Label != nil {
			j["label"] = s.Label.Name
		}
	case *ast.LabeledStmt:
		j["s"], j["label"], j["st"] = "labeled", s.Label.Name, stmt(s.Stmt)
	case *ast.EmptyStmt:
		j["s"] = "empty"
	case *ast.SendStmt:
		j["s"] = "send"
	case *ast.SelectStmt:
		j["s"] = "select"
	default:
		j["s"] = fmt.Sprintf("other:%T", s)
	}
	return j
}

// --- expressions ----------------------------------------------------------------------------------------------------
func exprs(xs []ast.Expr) []J {
	out := []J{}
	for _, x := range xs {
		out = append(out, expr(x))
	}
	return out
}
func expr(x ast.Expr) J {
	for {
		p, ok := x.(*ast.ParenExpr)
		if !ok {
			break
		}
		x = p.X
	}
	tv := info.Types[x]
	j := J{"p": pos(x.Pos()), "t": tid(tv.Type), "text": short(x)}
	if tv.Value != nil {
		j["c"] = cval(tv.Value)
	}
	switch x := x.(type) {
	case *ast.Ident:
		j["e"], j["n"] = "id", x.Name
		o := info.Uses[x]
		if o == nil {
			o = info.Defs[x]
		}
		j["o"], j["id"] = objKind(o), objID(o)
	case *ast.BasicLit:
		j["e"] = "lit"
	case *ast.SelectorExpr:
		j["e"], j["n"], j["x"] = "sel", x.Sel.Name, nil
		if sel, ok := info.Selections[x]; ok {
			j["x"] = expr(x.X)
			switch sel.Kind() {
			case types.FieldVal:
				j["k"] = "field"
			case types.MethodVal:
				j["k"] = "method"
				fn := sel.Obj().(*types.Func)
				sig := fn.Type().(*types.Signature)
				_, ptr := sig.Recv().Type().(*types.Pointer)
				j["mptr"] = ptr
				rt := sig.Recv().Type()
				if p, ok := rt.(*types.Pointer); ok {
					rt = p.Elem()
				}
				if n, ok := rt.(*types.Named); ok {
					j["mtype"] = n.Obj().Name()
					if n.Obj().Pkg() != nil {
						j["mpkg"] = n.Obj().Pkg().Path()
					}
				}
			case types.MethodExpr:
				j["k"] = "methodexpr"
			}
			idx := sel.Index()
			j["path"] = idx
			j["indirect"] = sel.Indirect()
		} else {
			// A qualified name: pkg.Name.
			o := info.Uses[x.Sel]
			j["k"] = "qual"
			if o != nil && o.Pkg() != nil {
				j["pkg"] = o.Pkg().Path()
			} else if id, ok := x.X.(*ast.Ident); ok {
				if pn, ok := info.Uses[id].(*types.PkgName); ok {
					j["pkg"] = pn.Imported().Path()
				}
			}
			j["o"] = objKind(o)
		}
	case *ast.CallExpr:
		j["e"], j["f"], j["a"] = "call", expr(x.Fun), exprs(x.Args)
		// (its end too: a check stubs an answered call by rewriting it from its position to its end)
		if q := fset.Position(x.End()); q.IsValid() {
			j["end"] = fmt.Sprintf("%d:%d", q.Line, q.Column)
		}
		if x.Ellipsis.IsValid() {
			j["ell"] = true
		}
		if ftv, ok := info.Types[x.Fun]; ok && ftv.IsType() {
			j["conv"] = true
		}
		if ftv, ok := info.Types[x.Fun]; ok && ftv.IsBuiltin() {
			id := x.Fun
			for {
				if p, ok := id.(*ast.ParenExpr); ok {
					id = p.X
					continue
				}
				break
			}
			if i, ok := id.(*ast.Ident); ok {
				j["builtin"] = i.Name
			}
		}
	case *ast.BinaryExpr:
		j["e"], j["op"], j["x"], j["y"] = "bin", x.Op.String(), expr(x.X), expr(x.Y)
	case *ast.UnaryExpr:
		j["e"], j["op"], j["x"] = "un", x.Op.String(), expr(x.X)
	case *ast.StarExpr:
		j["e"], j["x"] = "star", expr(x.X)
	case *ast.CompositeLit:
		j["e"] = "comp"
		elts := []J{}
		for _, el := range x.Elts {
			if kv, ok := el.(*ast.KeyValueExpr); ok {
				if id, ok := kv.Key.(*ast.Ident); ok {
					if _, isField := info.Uses[id].(*types.Var); isField {
						if _, st := tv.Type.Underlying().(*types.Struct); st {
							elts = append(elts, J{"field": id.Name, "v": expr(kv.Value)})
							continue
						}
					}
				}
				elts = append(elts, J{"k": expr(kv.Key), "v": expr(kv.Value)})
			} else {
				elts = append(elts, J{"v": expr(el)})
			}
		}
		j["elts"] = elts
	case *ast.IndexExpr:
		j["e"], j["x"], j["i"] = "index", expr(x.X), expr(x.Index)
		if xt, ok := info.Types[x.X]; ok {
			if _, isSig := xt.Type.(*types.Signature); isSig {
				j["e"] = "inst"
			}
		}
	case *ast.IndexListExpr:
		j["e"] = "inst"
		j["x"] = expr(x.X)
	case *ast.SliceExpr:
		j["e"], j["x"] = "slice", expr(x.X)
		if x.Low != nil {
			j["lo"] = expr(x.Low)
		}
		if x.High != nil {
			j["hi"] = expr(x.High)
		}
		if x.Slice3 {
			j["three"] = true
		}
	case *ast.FuncLit:
		j["e"] = "funclit"
	case *ast.TypeAssertExpr:
		j["e"] = "assert"
	case *ast.ArrayType, *ast.MapType, *ast.StructType, *ast.InterfaceType, *ast.FuncType, *ast.ChanType, *ast.Ellipsis:
		j["e"] = "type"
	default:
		j["e"] = fmt.Sprintf("other:%T", x)
	}
	return j
}
func objKind(o types.Object) string {
	switch o := o.(type) {
	case *types.Var:
		if o.IsField() {
			return "field"
		}
		return "var"
	case *types.Const:
		return "const"
	case *types.Func:
		return "func"
	case *types.TypeName:
		return "type"
	case *types.Nil:
		return "nil"
	case *types.Builtin:
		return "builtin"
	case *types.PkgName:
		return "pkgname"
	}
	return "none"
}

// The expression's text, short (for reasons).
func short(x ast.Expr) string {
	var b strings.Builder
	var walk func(ast.Expr)
	walk = func(x ast.Expr) {
		switch x := x.(type) {
		case *ast.Ident:
			b.WriteString(x.Name)
		case *ast.SelectorExpr:
			walk(x.X)
			b.WriteString("." + x.Sel.Name)
		case *ast.CallExpr:
			walk(x.Fun)
			b.WriteString("(")
			for i, a := range x.Args {
				if i > 0 {
					b.WriteString(", ")
				}
				walk(a)
			}
			b.WriteString(")")
		case *ast.BasicLit:
			b.WriteString(x.Value)
		case *ast.BinaryExpr:
			walk(x.X)
			b.WriteString(" " + x.Op.String() + " ")
			walk(x.Y)
		case *ast.UnaryExpr:
			b.WriteString(x.Op.String())
			walk(x.X)
		case *ast.StarExpr:
			b.WriteString("*")
			walk(x.X)
		case *ast.ParenExpr:
			b.WriteString("(")
			walk(x.X)
			b.WriteString(")")
		case *ast.IndexExpr:
			walk(x.X)
			b.WriteString("[")
			walk(x.Index)
			b.WriteString("]")
		case *ast.CompositeLit:
			b.WriteString("{...}")
		default:
			b.WriteString("…")
		}
	}
	walk(x)
	s := b.String()
	if len(s) > 60 {
		s = s[:60]
	}
	return s
}
