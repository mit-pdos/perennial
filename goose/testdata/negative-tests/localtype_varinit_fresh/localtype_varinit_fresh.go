package localtype_varinit_fresh

// A type declared in a function literal of a package-level variable's initializer
// is refused even when its name is unique: goose registers only the local types of
// function declarations.

var mk = func() uint64 {
	type u struct{ a uint64 } // ERROR local type u in a package-level variable's initializer
	return u{a: 1}.a
}
