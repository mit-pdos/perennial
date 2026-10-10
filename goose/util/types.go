package util

import (
	"go/types"
	"iter"
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
				// an anonymous struct type with fields has a synthetic declaration
				// (AnonStructSpecs), except at the top (the struct of a named type)
				if current != ty && t.NumFields() > 0 {
					if !yield(AnonStructName(pkgPath, t)) {
						return
					}
				}
				for i := 0; i < t.NumFields(); i++ {
					q = append(q, t.Field(i).Type())
				}
			case *types.Array:
				q = append(q, t.Elem())
			}
		}
	}
}
