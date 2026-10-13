package chan_typeparam_intersection

// The type set of ErrChan is {chan error}, but its terms mention chan I2 too:
// goose does not compute the core type, so it must not pick an element type.

type I2 interface {
	A() string
	Error() string
}

type ErrChan interface {
	interface{ chan I2 | chan error }
	chan error
}

func Send[C ErrChan](ch C, i I2) {
	ch <- i // ERROR whose core type goose does not determine
}
