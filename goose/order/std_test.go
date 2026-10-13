package order_test

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/goose/order"
	"golang.org/x/tools/go/packages"
)

// TestRewriteStd rewrites every package of the standard library and checks
// that the result parses, type-checks and is in normal form.
func TestRewriteStd(t *testing.T) {
	if testing.Short() {
		t.Skip("type-checks the standard library twice")
	}
	cfg := &packages.Config{Mode: packages.NeedSyntax | packages.NeedTypes | packages.NeedTypesInfo |
		packages.NeedName | packages.NeedCompiledGoFiles, Tests: true}
	pkgs, err := packages.Load(cfg, "std", "cmd/...")
	if err != nil {
		t.Fatal(err)
	}
	changed := 0
	fset := token.NewFileSet()
	imp := importer.ForCompiler(fset, "source", nil) // shared: it caches what it imports
	for _, p := range pkgs {
		var files []*ast.File
		pkgChanged := false
		for i, f := range p.Syntax {
			name := p.CompiledGoFiles[i]
			src, err := os.ReadFile(name)
			if err != nil {
				t.Fatal(err)
			}
			out, ch, err := order.Rewrite(p.Fset, p.Types, p.TypesInfo, f, src, nil)
			if err != nil {
				t.Errorf("%s: %v", p.PkgPath, err)
				continue
			}
			if ch {
				changed++
				pkgChanged = true
			}
			nf, err := parser.ParseFile(fset, name, out, parser.ParseComments)
			if err != nil {
				t.Errorf("%s: rewritten file does not parse: %v", p.PkgPath, err)
				continue
			}
			files = append(files, nf)
		}
		// An external test package (x_test) imports its package's test
		// variant, which the source importer does not build.
		if !pkgChanged || len(files) != len(p.Syntax) || strings.HasSuffix(p.Name, "_test") {
			continue
		}
		info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{},
			Uses: map[*ast.Ident]types.Object{}, Selections: map[*ast.SelectorExpr]*types.Selection{},
			Implicits: map[ast.Node]types.Object{}}
		var typeErr error
		conf := types.Config{Importer: imp, Error: func(err error) {
			if typeErr == nil {
				typeErr = err
			}
		}}
		conf.Check(p.PkgPath, fset, files, info)
		if typeErr != nil {
			t.Errorf("%s: rewritten package does not type-check: %v", p.PkgPath, typeErr)
			continue
		}
		for _, f := range files {
			for _, v := range order.CheckFile(info, f, nil) {
				t.Errorf("rewritten statement not in normal form: %v", fset.Position(v.Pos))
			}
		}
	}
	t.Logf("%d files rewritten", changed)
}
