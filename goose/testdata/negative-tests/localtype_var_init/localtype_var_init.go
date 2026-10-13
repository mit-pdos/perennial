package localtype_var_init

// A type declared in a package-level variable's initializer would be
// translated by its name, the same as the package-level type L.

type L struct{ X int }

var mk = func() any {
	type L struct{ X int } // ERROR local type in a package-level variable initializer
	return L{1}
}

func f() bool {
	_, ok := mk().(L)
	return ok
}
