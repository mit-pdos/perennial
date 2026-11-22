package skip_store

var X = uint64(1)

func F() {
	X = 2 // ERROR skipped variable X
}
