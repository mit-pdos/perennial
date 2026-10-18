package method_name_dup

import "github.com/mit-pdos/perennial/goose/testdata/negative-tests/method_name_dup/other"

// S's method set has two methods named m: its own and other's, promoted (the
// generated MethodUnfold facts are keyed by name)
type S struct { // ERROR methods
	other.T
}

func (S) m() {}
