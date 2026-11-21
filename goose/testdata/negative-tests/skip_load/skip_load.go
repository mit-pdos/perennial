package skip_load

var X = uint64(1)

func F() uint64 {
	return X // ERROR skipped variable X (skip: "a constant: cannot panic, no effect beyond the variable") is referenced by translated F at skip_load.go:6; translate X or do not translate F
}
