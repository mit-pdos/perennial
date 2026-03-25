package unittest

func recur() {
	recur()
}

type R struct {
}

func (r *R) recurMethod() {
	r.recurMethod()
}

type Other struct {
	*RecursiveEmbedded
}

type RecursiveEmbedded struct {
	Other
}

func (r *RecursiveEmbedded) recurEmbeddedMethod() {
	r.Other.recurEmbeddedMethod()
}
