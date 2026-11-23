package skip_funclit

var X = uint64(1)

func F() func() uint64 {
	return func() uint64 {
		return X // ERROR skipped variable X (skip: "a constant: cannot panic, no effect beyond the variable") is referenced by translated F
	}
}
