package localtype_shadow

// goose translates a local type as a package-level type of the same name

type t struct{ a uint64 }

func f() uint64 {
	type t struct{ b uint64 } // ERROR local type t: the name is not unique in the package
	return t{b: 1}.b
}

func g() uint64 {
	return t{a: 1}.a
}
