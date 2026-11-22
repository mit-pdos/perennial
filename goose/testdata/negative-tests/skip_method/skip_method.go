package skip_method

type T struct{ n uint64 }

func (t T) M() uint64 { return t.n }

var X T

func F() func() uint64 {
	return X.M // ERROR skipped variable X (skip: "a constant: cannot panic, no effect beyond the variable") is referenced by translated F
}
