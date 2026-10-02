package util

import (
	"errors"
	"fmt"
	"go/types"
	"iter"
	"strings"
)

func TypeGetDependencies(pkgPath string, ty types.Type) iter.Seq[string] {
	ty = types.Unalias(ty)
	return func(yield func(string) bool) {
		visited := make(map[types.Type]bool)
		var q []types.Type
		q = append(q, ty)

		for len(q) > 0 {
			current := q[0]
			q = q[1:]

			if visited[current] {
				continue
			}
			visited[current] = true

			switch t := current.(type) {
			case *types.Named:
				if t.Obj().Pkg() != nil && t.Obj().Pkg().Path() == pkgPath {
					if !yield(t.Obj().Name()) {
						return
					}
				}
				for i := range t.TypeArgs().Len() {
					q = append(q, t.TypeArgs().At(i))
				}

			case *types.Struct:
				for i := 0; i < t.NumFields(); i++ {
					q = append(q, t.Field(i).Type())
				}
			case *types.Array:
				q = append(q, t.Elem())
			}
		}
	}
}

func BasicTypeToCoq(t *types.Basic) (error, string) {
	switch t.Name() {
	case "uint64", "int64":
		return nil, "w64"
	case "uint32", "int32":
		return nil, "w32"
	case "uint16", "int16":
		return nil, "w16"
	case "uint8", "int8", "byte":
		return nil, "w8"
	case "uint", "int":
		return nil, "w64"
	case "float64":
		return nil, "w64"
	case "bool":
		return nil, "bool"
	case "string", "untyped string":
		return nil, "go_string"
	case "Pointer", "uintptr":
		return nil, "loc"
	default:
		return errors.New("Unknown basic type " + t.Name()), ""
	}
}

func NamedTypeToCoq(t *types.Named) (error, string) {
	var baseName string
	pkg := t.Obj().Pkg()
	if pkg != nil {
		baseName = pkg.Name() + "." + t.Obj().Name() + ".t"
	} else {
		baseName = t.Obj().Name() + ".t"
	}
	// if TypeParams() is not nil, there are type parameters in the base named type
	if t.TypeParams() != nil {
		var params []string
		for i := 0; i < t.TypeArgs().Len(); i++ {
			err, t := ToCoqType(t.TypeArgs().At(i))
			if err != nil {
				return err, ""
			}
			params = append(params, t)
		}
		return nil, fmt.Sprintf("(%s %s)", baseName, strings.Join(params, " "))
	}
	return nil, baseName
}

// ToCoqType converts a type to a Gallina type modeling that type
func ToCoqType(t types.Type) (error, string) {
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return BasicTypeToCoq(t)
	case *types.Slice:
		return nil, "slice.t"
	case *types.Array:
		err, elem := ToCoqType(t.Elem())
		if err != nil {
			return err, ""
		}
		return nil, fmt.Sprintf("(vec %s (uint.nat (W64 %d)))", elem, t.Len())
	case *types.Pointer:
		return nil, "loc"
	case *types.Signature:
		return nil, "func.t"
	case *types.Interface:
		return nil, "interface.t"
	case *types.Map, *types.Chan:
		return nil, "loc"
	case *types.Named:
		return NamedTypeToCoq(t)
	case *types.TypeParam:
		return nil, t.String()
	case *types.Struct:
		if t.NumFields() == 0 {
			return nil, "unit"
		} else {
			return errors.New("Anonymous structs with fields are not supported" + t.String()), ""
		}
	}
	return fmt.Errorf("Unknown type %s (of type %T)", t, t), ""
}
