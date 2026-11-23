package skip_addr

var X = uint64(1)

func F() *uint64 {
	return &X // ERROR skipped variable X
}
