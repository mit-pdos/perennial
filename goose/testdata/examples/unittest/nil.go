package unittest

func AssignNilSlice() {
	s := make([][]byte, 4)
	s[2] = nil
}

func AssignNilPointer() {
	s := make([]*uint64, 4)
	s[2] = nil
}

func CompareSliceToNil() bool {
	s := make([]byte, 0)
	return s != nil
}

func ComparePointerToNil() bool {
	s := new(uint64)
	return s != nil
}

type containsPointer struct {
	s *uint64
}

func useNilField() *containsPointer {
	return &containsPointer{s: nil}
}
