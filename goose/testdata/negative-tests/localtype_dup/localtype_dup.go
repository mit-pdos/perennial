package localtype_dup

// goose translates a local type as a package-level type of the same name

func f() uint64 {
	type t struct{ a uint64 }
	return t{a: 1}.a
}

func g() uint64 {
	type t struct{ b uint64 } // ERROR two local types are named t
	return t{b: 1}.b
}
