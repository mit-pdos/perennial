package unittest

// Assignments to an interface variable convert the value even where goose
// does not see an assignment statement: Go gives the value an itab for the
// variable's type.

type assignIface interface {
	A() string
	Error() string
}

func rangeAssignInterface(xs []assignIface) error {
	var x error
	for _, x = range xs {
	}
	return x
}

func selectSendInterface(ch chan error, i assignIface) {
	select {
	case ch <- i:
	}
}

func typeParamToInterface[X error](x X) error {
	var e error = x
	return e
}
