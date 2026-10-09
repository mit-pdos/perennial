package util

import (
	"go/ast"
	"go/token"
	"go/types"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"golang.org/x/tools/go/packages"
)

// FuncName is the name of a function or method as the declaration filter
// sees it: `f`, or `T.m` for a method of `T` or `*T`.
func FuncName(f *types.Func) string {
	maybeTypeName := ""
	if recv := f.Type().(*types.Signature).Recv(); recv != nil {
		recvType := recv.Type()
		if ptrType, ok := recvType.(*types.Pointer); ok {
			recvType = ptrType.Elem()
		}
		maybeTypeName = types.TypeString(recvType, func(_ *types.Package) string { return "" }) + "."
	}
	return maybeTypeName + f.Name()
}

// LocalTypeSpecs returns the type declarations in a function body (including
// those in nested function literals), in source order.
//
// Goose translates a local type as a package-level type of the same name
// (rejecting it if that name is not unique in the package), and translates it
// exactly when it translates the enclosing function.
func LocalTypeSpecs(body *ast.BlockStmt) []*ast.TypeSpec {
	var specs []*ast.TypeSpec
	if body == nil {
		return nil
	}
	ast.Inspect(body, func(n ast.Node) bool {
		if s, ok := n.(*ast.DeclStmt); ok {
			if d, ok := s.Decl.(*ast.GenDecl); ok && d.Tok == token.TYPE {
				for _, spec := range d.Specs {
					specs = append(specs, spec.(*ast.TypeSpec))
				}
			}
		}
		return true
	})
	return specs
}

// withLocalTypes extends df to translate the local types of the functions df
// translates.
func withLocalTypes(pkg *packages.Package, df declfilter.DeclFilter) declfilter.DeclFilter {
	names := make(map[string]bool)
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			d, ok := d.(*ast.FuncDecl)
			if !ok {
				continue
			}
			fn, ok := pkg.TypesInfo.Defs[d.Name].(*types.Func)
			if !ok || df.GetAction(FuncName(fn)) != declfilter.Translate {
				continue
			}
			for _, spec := range LocalTypeSpecs(d.Body) {
				names[spec.Name.Name] = true
			}
		}
	}
	return declfilter.WithTranslated(df, names)
}
