package unittest

import (
	"github.com/goose-lang/primitive"
)

func atomicCreateStub(dir string, fname string, data []byte) {}

func useSlice() {
	s := make([]byte, 1)
	s1 := append(s, s...)
	atomicCreateStub("dir", "file", s1)
}

func useSliceIndexing() uint64 {
	s := make([]uint64, 2)
	s[1] = 2
	x := s[0]
	return x
}

func useMap() {
	m := make(map[uint64][]byte)
	m[1] = nil
	x, ok := m[2]
	if ok {
		return
	}
	m[3] = x
}

func usePtr() {
	p := new(uint64)
	*p = 1
	x := *p
	*p = x
}

func iterMapKeysAndValues(m map[uint64]uint64) uint64 {
	sumPtr := new(uint64)
	for k, v := range m {
		sum := *sumPtr
		*sumPtr = sum + k + v
	}
	sum := *sumPtr
	return sum
}

func iterMapKeys(m map[uint64]uint64) []uint64 {
	keysSlice := make([]uint64, 0)
	keysRef := new([]uint64)
	*keysRef = keysSlice
	for k := range m {
		keys := *keysRef
		newKeys := append(keys, k)
		*keysRef = newKeys
	}
	keys := *keysRef
	return keys
}

func getRandom() uint64 {
	r := primitive.RandomUint64()
	return r
}
