package util

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"hash/fnv"
	"sort"
)

// AnonStructName is the name of the synthetic named type that stands for an
// anonymous struct type with fields of package pkg (a hash of the type, so that
// goose and proofgen agree on it).
func AnonStructName(pkgPath string, t *types.Struct) string {
	qual := func(p *types.Package) string {
		if p.Path() == pkgPath {
			return ""
		}
		return p.Path()
	}
	h := fnv.New64a()
	h.Write([]byte(types.TypeString(t, qual)))
	return fmt.Sprintf("anonStruct_%016x", h.Sum64())
}

// IsAnonStruct reports whether t is an anonymous struct type with fields: one that
// is not the underlying type of a named type (those come with their own declaration).
func IsAnonStruct(t types.Type) (*types.Struct, bool) {
	s, ok := t.(*types.Struct)
	return s, ok && s.NumFields() > 0
}

// AnonStructSpecs finds the anonymous struct types with fields that the package's
// declarations and expressions use, and gives each a synthetic type declaration
// (registered in info, as a named type of the package whose underlying type is the
// struct). Goose models an anonymous struct type's values by the Lean structure of
// this declaration, while its Go type stays the unnamed struct type (go.StructType,
// the synthetic declaration's underlying type).
func AnonStructSpecs(pkg *types.Package, info *types.Info) []*ast.TypeSpec {
	found := make(map[string]*types.Struct)
	visited := make(map[types.Type]bool)
	var walk func(t types.Type, top bool)
	walk = func(t types.Type, top bool) {
		t = types.Unalias(t)
		if t == nil || visited[t] {
			return
		}
		visited[t] = true
		switch t := t.(type) {
		case *types.Named:
			for i := range t.TypeArgs().Len() {
				walk(t.TypeArgs().At(i), false)
			}
		case *types.Struct:
			if !top && t.NumFields() > 0 {
				found[AnonStructName(pkg.Path(), t)] = t
			}
			for i := range t.NumFields() {
				walk(t.Field(i).Type(), false)
			}
		case *types.Pointer:
			walk(t.Elem(), false)
		case *types.Slice:
			walk(t.Elem(), false)
		case *types.Array:
			walk(t.Elem(), false)
		case *types.Map:
			walk(t.Key(), false)
			walk(t.Elem(), false)
		case *types.Chan:
			walk(t.Elem(), false)
		case *types.Signature:
			for i := range t.Params().Len() {
				walk(t.Params().At(i).Type(), false)
			}
			for i := range t.Results().Len() {
				walk(t.Results().At(i).Type(), false)
			}
		}
	}
	// first the named types: the struct of a named type is its own declaration (its
	// fields' types may have anonymous structs)
	for _, obj := range info.Defs {
		if tn, ok := obj.(*types.TypeName); ok && tn.Pkg() == pkg {
			if named, ok := tn.Type().(*types.Named); ok {
				walk(named.Underlying(), true)
			}
		}
	}
	for _, obj := range info.Defs {
		if obj == nil || obj.Pkg() != pkg {
			continue
		}
		if _, ok := obj.(*types.TypeName); ok {
			continue
		}
		walk(obj.Type(), false)
	}
	for _, tv := range info.Types {
		if tv.Type != nil {
			walk(tv.Type, false)
		}
	}
	names := make([]string, 0, len(found))
	for n := range found {
		names = append(names, n)
	}
	sort.Strings(names)
	var specs []*ast.TypeSpec
	for _, n := range names {
		st := found[n]
		ident := ast.NewIdent(n)
		tn := types.NewTypeName(token.NoPos, pkg, n, nil)
		types.NewNamed(tn, st, nil)
		info.Defs[ident] = tn
		typeExpr := &ast.StructType{Fields: &ast.FieldList{}}
		info.Types[typeExpr] = types.TypeAndValue{Type: st}
		specs = append(specs, &ast.TypeSpec{Name: ident, Type: typeExpr})
	}
	return specs
}

// SortedSpecs are the specs of the map, by name.
func SortedSpecs(m map[string]*ast.TypeSpec) []*ast.TypeSpec {
	names := make([]string, 0, len(m))
	for n := range m {
		names = append(names, n)
	}
	sort.Strings(names)
	var specs []*ast.TypeSpec
	for _, n := range names {
		specs = append(specs, m[n])
	}
	return specs
}
