package util

import (
	"crypto/sha256"
	"encoding/hex"
	"go/types"
	"strconv"
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
	h := sha256.Sum256([]byte(AnonStructKey(s)))
	return "struct#" + hex.EncodeToString(h[:4])
}

// AnonStructKey identifies the unnamed struct type s as Go's type identity does:
// the type as Go prints it (packages by path), which omits the package of a
// field, followed by the package of every unexported or blank field of every
// struct type literal in s (s's own and nested ones, through any type
// constructor), in a fixed depth-first order. Two such fields of different
// packages are different fields in Go, so `struct{ x int }` declared in p and in
// q have different keys (and names), as their field lists (ModelFieldName) are.
// (Equal printed types have equal structure, so the walk lists the fields in
// the same order: the list needs no separators.) A type with no unexported or
// blank field keeps the key it had before (its printed form).
func AnonStructKey(s *types.Struct) string {
	key := types.TypeString(s, func(p *types.Package) string { return p.Path() })
	var pkgs []string
	visited := make(map[types.Type]bool)
	var walk func(t types.Type)
	walk = func(t types.Type) {
		if visited[t] {
			return
		}
		visited[t] = true
		switch t := t.(type) {
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
				f := t.Field(i)
				if !f.Exported() && f.Pkg() != nil {
					pkgs = append(pkgs, strconv.Itoa(i)+"="+f.Pkg().Path())
				}
				walk(f.Type())
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
	for _, p := range pkgs {
		key += " " + p
	}
	return key
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

// ModelFieldName is the name the model gives field i of st: the Go name (blank
// fields "_#i"). In an unnamed struct type (unnamed), an unexported or blank
// field's name is qualified by its package path ("p/q.x"): Go's type
// identity distinguishes unexported field names of different packages
// (`struct{x int}` declared in p and in q are different types), and the model's
// go.StructType is compared structurally, so the qualification keeps them apart.
// A defined type is identified by its name, so its fields keep their Go names.
func ModelFieldName(st *types.Struct, i int, unnamed bool) string {
	f := st.Field(i)
	if f.Name() == "_" {
		// a blank field is non-exported too: qualified in a struct type literal
		// (go.isBlankField recognizes both forms)
		if unnamed && f.Pkg() != nil {
			return f.Pkg().Path() + "._#" + strconv.Itoa(i)
		}
		return "_#" + strconv.Itoa(i)
	}
	return ModelFieldVarName(f, unnamed)
}

// ModelFieldVarName is ModelFieldName for a non-blank field given by its object
// (a keyed composite literal's key).
func ModelFieldVarName(f *types.Var, unnamed bool) string {
	if unnamed && !f.Exported() && f.Pkg() != nil {
		return f.Pkg().Path() + "." + f.Name()
	}
	return f.Name()
}
