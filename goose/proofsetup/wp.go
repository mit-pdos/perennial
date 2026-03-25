package proofsetup

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/types"
	"io"
	"slices"
	"strings"

	"github.com/mit-pdos/perennial/goose/util"
	"github.com/pkg/errors"
	"golang.org/x/tools/go/packages"
)

type receiverType struct {
	Name    string
	Pointer bool
}

func (rt receiverType) FullName(pkgname string) string {
	// if rt.Pointer {
	// return rt.Name + "'ptr"
	return "ptrT.id " + pkgname + "." + rt.Name + ".id"
	// } else {
	// 	return rt.Name
	// }
}

// getReceiverType extracts information about the receiver of a method
func getReceiverType(t types.Type) receiverType {
	switch t := types.Unalias(t).(type) {
	case *types.Named:
		return receiverType{
			Name:    t.Obj().Name(),
			Pointer: false,
		}
	case *types.Pointer:
		underlyingT := types.Unalias(t.Elem()).(*types.Named)
		return receiverType{
			Name:    underlyingT.Obj().Name(),
			Pointer: true,
		}
	}
	panic(errors.Errorf("unexpected receiver type %v", t))
}

func argGallinaBinder(pkg *packages.Package, x ast.Expr, xName string) (string, error) {
	typeinfo := pkg.TypesInfo.TypeOf(x)
	if typeinfo == nil {
		return "", fmt.Errorf("cannot find type information for type %s", xName)
	}
	err, ty := util.ToCoqType(typeinfo)
	return fmt.Sprintf("(%s: %s)", xName, ty), err
}

func receiverIsInstantiated(pkg *packages.Package, decl *ast.FuncDecl) bool {
	if decl.Recv == nil || len(decl.Recv.List) == 0 {
		return false
	}
	t := pkg.TypesInfo.TypeOf(decl.Recv.List[0].Type)
	if t == nil {
		return false
	}
	if p, ok := types.Unalias(t).(*types.Pointer); ok {
		t = p.Elem()
	}
	n, ok := types.Unalias(t).(*types.Named)
	return ok && n.TypeArgs() != nil && n.TypeArgs().Len() > 0
}

func funcDeclToWp(pkg *packages.Package, decl *ast.FuncDecl) (string, string, error) {
	if decl.Type.TypeParams != nil {
		return decl.Name.Name, "", errors.Errorf("generics not supported")
	}

	if receiverIsInstantiated(pkg, decl) {
		return decl.Name.Name, "", errors.Errorf("generic instantiation in receiver not supported")
	}

	s := new(bytes.Buffer)

	var rt *receiverType = nil
	if decl.Recv != nil {
		recv := decl.Recv.List[0].Type
		t := pkg.TypesInfo.TypeOf(recv)
		actualRt := getReceiverType(t)
		rt = &actualRt
	}

	var gallinaBinders []string
	var args []string
	// TODO: binder for rt
	if rt != nil {
		var recv string
		if len(decl.Recv.List[0].Names) > 0 {
			recv = decl.Recv.List[0].Names[0].Name
		} else {
			recv = "recv"
		}
		// gallinaBinders = append(gallinaBinders, fmt.Sprintf("(%s: %s)", recv, rt.Name))
		fmt.Printf("rt name: %v\n", rt.Name)
		binder, err := argGallinaBinder(pkg, decl.Recv.List[0].Type, recv)
		if err != nil {
			return decl.Name.Name, "", err
		}
		gallinaBinders = append(gallinaBinders, binder)
	}

	params := []string{}
	unnamedIdx := 0
	for _, param := range decl.Type.Params.List {
		if len(param.Names) == 0 {
			paramName := fmt.Sprintf("arg%d", unnamedIdx)
			unnamedIdx++
			// unnamed parameter
			typ, err := argGallinaBinder(pkg, param.Type, paramName)
			if err != nil {
				return decl.Name.Name, "", err
			}

			gallinaBinders = append(gallinaBinders, typ)

			args = append(args, "#"+paramName)
		} else {
			// single or multiple parameters with same type
			for _, name := range param.Names {
				typ, err := argGallinaBinder(pkg, param.Type, name.Name)
				if err != nil {
					return decl.Name.Name, "", err
				}
				gallinaBinders = append(gallinaBinders, typ)

				args = append(args, "#"+name.Name)
			}
		}

	}

	if len(args) == 0 {
		args = []string{"#()"}
	}

	var name string

	if rt != nil {
		name = "wp_" + rt.Name + "__" + decl.Name.Name
	} else {
		name = "wp_" + decl.Name.Name
	}
	fmt.Fprintf(s, "Lemma %s %s :\n", name, strings.Join(gallinaBinders, " "))

	fmt.Fprintf(s, "  {{{ is_pkg_init %s }}}\n", pkg.Name)

	if rt == nil {
		// fmt.Fprintf(s, "    %s @ \"%s\" %s\n", pkg.Name, decl.Name, strings.Join(args, " "))
		fmt.Fprintf(s, "    @! %s.%s %s\n", pkg.Name, decl.Name, strings.Join(args, " "))
	} else {
		var recv string
		if len(decl.Recv.List[0].Names) > 0 {
			recv = decl.Recv.List[0].Names[0].Name
		} else {
			recv = "recv"
		}
		// fmt.Fprintf(s, "    %s @ %s @ \"%s\" @ \"%s\" %s\n", recv.Name, pkg.Name, rt.FullName(), decl.Name, strings.Join(args, " "))
		fmt.Fprintf(s, "    %s @ (%s) @ \"%s\" %s\n", recv, rt.FullName(pkg.Name), decl.Name, strings.Join(args, " "))
	}

	// return types
	fmt.Fprintf(s, "  {{{ ")
	printReturns(s, decl, params, pkg)
	fmt.Fprintf(s, " }}}.")

	return name, s.String(), nil
}

// makeName turns 0 -> "a", 1 -> "b", ..., 25 -> "z", 26 -> "aa", etc.
func makeName(i int) string {
	alphabet := "abcdefghijklmnopqrstuvwxyz"
	if i < 26 {
		return string(alphabet[i])
	}
	var b []byte
	for i >= 0 {
		b = append([]byte{alphabet[i%26]}, b...)
		i = i/26 - 1
	}
	return string(b)
}

func printReturns(w io.Writer, decl *ast.FuncDecl, params []string, pkg *packages.Package) {
	if decl.Type.Results == nil || len(decl.Type.Results.List) == 0 {
		fmt.Fprintf(w, "RET #(); True")
		return
	}

	var typedParts []string
	var retRefs []string
	idx := 0
	for _, f := range decl.Type.Results.List {
		typ := ""
		if _, ok := f.Type.(*ast.StarExpr); ok {
			typ = "loc"
		} else {
			// interesting case: receiver type is specialization of generic type. example: go/src/crypto/elliptic/nistec.go:pointFromAffine
			// for now, not supported
			_, typ = util.ToCoqType(pkg.TypesInfo.TypeOf(f.Type))
		}
		n := 1
		if len(f.Names) > 0 {
			n = len(f.Names)
		}
		for k := 0; k < n; k++ {
			name := makeName(idx)
			if slices.Contains(params, name) {
				k = k - 1
				idx++
				continue
			}
			typedParts = append(typedParts, fmt.Sprintf("(%s: %s)", name, typ))
			retRefs = append(retRefs, "#"+name)
			idx++
		}
	}

	fmt.Fprintf(w, "%s, RET (%s); True",
		strings.Join(typedParts, " "),
		strings.Join(retRefs, ", "),
	)
}

func packageWps(pkg *packages.Package, verbose bool) ([]string, map[string]string) {
	var names []string
	wpsMap := make(map[string]string)
	for _, f := range pkg.Syntax {
		for _, decl := range f.Decls {
			if decl, ok := decl.(*ast.FuncDecl); ok {
				name, lemma, err := funcDeclToWp(pkg, decl)
				if err != nil && verbose {
					fmt.Printf("function %s: %v\n", name, err)
					continue
				}
				names = append(names, name)
				wpsMap[name] = lemma
			}
		}
	}
	return names, wpsMap
}
