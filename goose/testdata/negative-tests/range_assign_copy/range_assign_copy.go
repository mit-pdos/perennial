package range_assign_copy

type big struct{ a, b, c int64 }

func last(p *big, s []big) {
	for _, *p = range s { // ERROR range with = that copies
	}
}
