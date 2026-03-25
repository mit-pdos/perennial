package unittest

type Foo [10]uint64

func takesArray(x [13]string) string {
	return x[3]
}

func takesPtr(x *string) {
	*x += "bar"
}

func usesArrayElemRef() {
	x := [...]string{
		"a",
		"b",
	}
	x[1] = "c"
	takesPtr(&x[1])
}

func sum(x [100]uint64) uint64 {
	sum := uint64(0)
	for i := uint64(0); i < uint64(len(x)); i++ {
		sum += x[i]
	}
	sum += uint64(cap(x))
	return sum
}

func arrayToSlice() []string {
	x := [...]string{
		"a",
		"b",
	}
	return x[:]
}

const (
	arrayA = 0
	arrayB = 10
)

func arrayLiteralKeyed() string {
	var x = [...]string{
		arrayB: "B",
		"1",
		"2",
		arrayA: "A",
		"3",
	}
	return x[0]
}
