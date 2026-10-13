package filtered_vars

// The config translates only F: the variables below are not translated (each
// initializer is an 'init axiom), so what goose would refuse in them does not
// fail the package.

type SB = struct {
	X int `json:"b"`
}

func g[T any]() any {
	var x T
	return x
}

// an instantiation whose type argument loses its identity in translation
var a = g[SB]()

// a local type in an initializer
var b, c = func() any {
	type L struct{}
	return L{}
}(), 0

func F() int {
	return 1
}
