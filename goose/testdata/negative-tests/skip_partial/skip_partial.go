package skip_partial

func pair() (uint64, uint64) { return 1, 2 }

var a, b = pair() // ERROR the initializer of a, b is only partly skipped (skipped: a; not skipped: b)
