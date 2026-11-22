package skip_partial_translate

// perennial#657: one initializer of two variables, one of them axiomatized

func pair() (uint64, uint64) { return 1, 2 }

var a, b = pair() // ERROR the initializer of a, b is only partly translated (translated: a; trusted or axiomatized: b)
