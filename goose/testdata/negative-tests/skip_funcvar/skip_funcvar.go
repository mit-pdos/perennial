package skip_funcvar

var X = func() uint64 { return 1 }

func F() uint64 {
	return X() // ERROR skipped variable X
}
