package evalorder_opassign

// `x op= y` evaluates x's operands once; goose's translation (x = x op y)
// would receive from ch twice.

func f(ch chan uint64, a []uint64) {
	a[<-ch] += 1 // ERROR evaluation order
}
