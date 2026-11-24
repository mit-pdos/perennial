package localtype_varinit

// A type declared in a function literal of a package-level variable's initializer
// is not translated as a package-level type: goose would resolve E below to the
// package-level E (review finding F1, 2026-11-24: errors.As and the type assertion
// in Check2 would be true where Go's are false).

import "errors"

type base struct{}

func (base) Error() string { return "b" }

type E struct{ base }

var mk = func() error {
	type E struct{ base } // ERROR local type E in a package-level variable's initializer
	return &E{}
}

func Check() bool {
	var t *E
	return errors.As(mk(), &t)
}

func Check2() bool {
	_, ok := mk().(*E)
	return ok
}
