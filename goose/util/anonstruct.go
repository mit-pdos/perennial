package util

import (
	"crypto/sha256"
	"encoding/hex"
	"go/types"
)

// IsAnonStruct reports whether t is a struct type that is not a defined type
// and has fields: goose models its values by a generated structure, as it does
// a defined struct type's (see AnonStructName).
func IsAnonStruct(t types.Type) (*types.Struct, bool) {
	s, ok := t.(*types.Struct)
	return s, ok && s.NumFields() > 0
}

// AnonStructName is the name of the structure modeling the values of the
// unnamed struct type s: `struct#` and a hash of the type as Go prints it
// (packages by path). Go's identity of unnamed struct types is structural, so
// the name is a function of the type: every occurrence of the type in a
// package names the same structure, independently of the order of the
// declarations, and goose and proofgen compute it alike. `#` is in no Go
// identifier, so the name is distinct from the package's own names.
func AnonStructName(s *types.Struct) string {
	key := types.TypeString(s, func(p *types.Package) string { return p.Path() })
	h := sha256.Sum256([]byte(key))
	return "struct#" + hex.EncodeToString(h[:4])
}

// AnonStructParams are the type parameters the unnamed struct type s mentions,
// in order of first occurrence: the parameters of its structure.
func AnonStructParams(s *types.Struct) []*types.TypeParam {
	var params []*types.TypeParam
	visited := make(map[types.Type]bool)
	var walk func(t types.Type)
	walk = func(t types.Type) {
		if visited[t] {
			return
		}
		visited[t] = true
		switch t := t.(type) {
		case *types.TypeParam:
			params = append(params, t)
		case *types.Alias:
			if args := t.TypeArgs(); args != nil {
				for i := range args.Len() {
					walk(args.At(i))
				}
			}
			walk(types.Unalias(t))
		case *types.Named:
			for i := range t.TypeArgs().Len() {
				walk(t.TypeArgs().At(i))
			}
		case *types.Pointer:
			walk(t.Elem())
		case *types.Slice:
			walk(t.Elem())
		case *types.Array:
			walk(t.Elem())
		case *types.Map:
			walk(t.Key())
			walk(t.Elem())
		case *types.Chan:
			walk(t.Elem())
		case *types.Signature:
			for i := range t.Params().Len() {
				walk(t.Params().At(i).Type())
			}
			for i := range t.Results().Len() {
				walk(t.Results().At(i).Type())
			}
		case *types.Struct:
			for i := range t.NumFields() {
				walk(t.Field(i).Type())
			}
		case *types.Interface:
			for i := range t.NumExplicitMethods() {
				walk(t.ExplicitMethod(i).Type())
			}
			for i := range t.NumEmbeddeds() {
				walk(t.EmbeddedType(i))
			}
		case *types.Union:
			for i := range t.Len() {
				walk(t.Term(i).Type())
			}
		}
	}
	walk(s)
	return params
}

// AnonStructsByValue are the unnamed struct types (with fields) whose values
// are part of a value of type t (through struct fields, array elements and
// type arguments, not through pointers or other references), each after the
// ones its own fields reach.
func AnonStructsByValue(t types.Type) []*types.Struct {
	var out []*types.Struct
	var walk func(t types.Type)
	walk = func(t types.Type) {
		switch t := types.Unalias(t).(type) {
		case *types.Named:
			for i := range t.TypeArgs().Len() {
				walk(t.TypeArgs().At(i))
			}
		case *types.Array:
			walk(t.Elem())
		case *types.Struct:
			for i := range t.NumFields() {
				walk(t.Field(i).Type())
			}
			if t.NumFields() > 0 {
				out = append(out, t)
			}
		}
	}
	walk(t)
	return out
}

// AnonStructsInDef are AnonStructsByValue of a type declaration's definition
// def: of its fields if def is a struct type (the defined type's own, not an
// unnamed one).
func AnonStructsInDef(def types.Type) []*types.Struct {
	if s, ok := def.(*types.Struct); ok {
		var out []*types.Struct
		for i := range s.NumFields() {
			out = append(out, AnonStructsByValue(s.Field(i).Type())...)
		}
		return out
	}
	return AnonStructsByValue(def)
}
