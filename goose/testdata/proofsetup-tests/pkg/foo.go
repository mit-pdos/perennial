package pkg

func Sum(n uint64) uint64 {
	var s, i uint64
	for i < n {
		s = s + i
		i = i + 1
	}
	return s
}
