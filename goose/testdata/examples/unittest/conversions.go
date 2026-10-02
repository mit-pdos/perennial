package unittest

type stringWrapper string

func typedLiteral() uint64 {
	return 3
}

func literalCast() uint64 {
	// produces a uint64 -> uint64 conversion
	x := uint64(2)
	return x + 2
}

func castInt(p []byte) uint64 {
	return uint64(len(p))
}

func stringToByteSlice(s string) []byte {
	// must be lifted, impure operation
	p := []byte(s)
	return p
}

func byteSliceToString(p []byte) string {
	// must be lifted, impure operation
	s := string(p)
	return s
}

func stringToStringWrapper(s string) stringWrapper {
	return stringWrapper(s)
}

func stringWrapperToString(s stringWrapper) string {
	return string(s)
}

type Uint32 uint32

func testU32NewtypeLen() bool {
	s := make([]byte, 20)
	return Uint32(len(s)) == Uint32(20)
}

type numWrapper int

func (n *numWrapper) inc() {
	*n++
}

func testNumWrapper() {
	n := numWrapper(0)
	n.inc()
}

type withInterface struct {
	a any
}

func testConversionLiteral() bool {
	s := withInterface{nil}
	s = withInterface{a: nil}
	m := map[any]any{nil: nil}
	m[nil] = s
	m[s] = nil
	return m[m[s]] == s
}
