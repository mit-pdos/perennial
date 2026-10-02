package toposort

import "iter"

// uses depth first search
func ToposortSeq[V comparable](vs iter.Seq[V], deps func(v V) iter.Seq[V],
	handleCycle func(vs []V)) iter.Seq[V] {
	return func(yield func(v V) bool) {
		visited := make(map[V]bool)
		dipath := make([]V, 0)
		onDipath := make(map[V]bool)

		var visit func(v V)
		visit = func(v V) {
			if visited[v] {
				return
			} else if onDipath[v] {
				handleCycle(dipath)
			} else {
				dipath, onDipath[v] = append(dipath, v), true
				for d := range deps(v) {
					visit(d)
				}
			}
			visited[v] = true
			delete(onDipath, v)
			dipath = dipath[:len(dipath)-1]
			if !yield(v) {
				return
			}
		}

		for v := range vs {
			visit(v)
		}
	}
}
