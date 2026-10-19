package semantics

// helpers
type ArrayEditor struct {
	s        []uint64
	next_val uint64
}

func (ae *ArrayEditor) Advance(arr []uint64, next uint64) {
	arr[0] += 1
	ae.s[0] = ae.next_val
	ae.next_val = next
	ae.s = ae.s[1:]
}

// tests
func testSliceOps() bool {
	x := make([]uint64, 10)
	x[1] = 5
	x[2] = 10
	x[3] = 15
	x[4] = 20

	v1 := x[2]
	v2 := x[2:3]
	v3 := x[:3]
	v4 := &x[2]

	var ok = true
	ok = ok && (v1 == 10)
	ok = ok && (v2[0] == 10)
	ok = ok && (len(v2) == 1)
	ok = ok && (v3[1] == 5)
	ok = ok && (v3[2] == 10)
	ok = ok && (len(v3) == 3)
	ok = ok && (*v4 == 10)
	return ok
}

func testSliceCapacityOps() bool {
	x := make([]uint64, 0, 10)

	sub1 := x[:6]
	sub1[0] = 1
	sub2 := x[2:4]
	sub2[0] = 2
	// Doing something like `x[2:]` panics

	var ok = true
	ok = ok && (len(sub1) == 6)
	ok = ok && (cap(sub1) == 10)
	ok = ok && (x[:10][0] == 1) // affected by the sub1[0] assignment above
	ok = ok && (len(sub2) == 2)
	ok = ok && (cap(sub2) == 8)
	ok = ok && (x[:10][2] == 2) // affected by the sub2[0] assignment above
	return ok
}

func testOverwriteArray() bool {
	var arr = make([]uint64, 4)

	ae1 := &ArrayEditor{s: arr[0:], next_val: 1}
	ae2 := &ArrayEditor{s: arr[1:], next_val: 102}
	ae2.Advance(arr, 103)
	ae2.Advance(arr, 104)
	ae2.Advance(arr, 105) // 105 never gets written to array

	ae1.Advance(arr, 2) // resets arr[0]
	ae1.Advance(arr, 3)
	ae1.Advance(arr, 4)
	ae1.Advance(arr, 5) // 5 never written to array

	// make sure all values were overwritten properly
	if arr[0]+arr[1]+arr[2]+arr[3] >= 100 {
		return false
	}
	return arr[3] == 4 && arr[0] == 4
}

func testSliceLiteral() bool {
	bytes := []byte{1, 2}
	var ok = true
	ok = ok && bytes[0] == byte(1)
	ints := []uint64{1, 2, 3}
	ok = ok && ints[1] == uint64(2)
	return ok
}

func testSliceAppend() bool {
	var ok = true
	var bytes = make([]byte, 0)
	bytes = append(bytes, 1)
	newBytes := []byte{2, 3}
	bytes = append(bytes, newBytes...)
	ok = ok && uint64(len(bytes)) == uint64(3)
	ok = ok && bytes[2] == byte(3)
	return ok
}

func testSliceRef() bool {
	var sl = make([]uint64, 5)
	var ptr = &sl[0]
	*ptr = 1
	return (sl[0] == 1)
}

func testAppendStringVar() bool {
	b := []byte("ab")
	s := "cd"
	b = append(b, s...)
	return string(b) == "abcd"
}

func testAppendStringConst() bool {
	b := []byte("ab")
	b = append(b, "cd"...)
	return string(b) == "abcd"
}

func appendBytesOrString[S ~[]byte | ~string](b []byte, s S) []byte {
	return append(b, s...)
}

func testAppendGenericString() bool {
	return string(appendBytesOrString([]byte("ab"), "cd")) == "abcd"
}

func testAppendGenericBytes() bool {
	return string(appendBytesOrString([]byte("ab"), []byte("cd"))) == "abcd"
}

type appendNamedSlice []uint64

func testAppendNilNamed() bool {
	x := appendNamedSlice{1, 2}
	y := append(x, nil...)
	return len(y) == 2 && y[1] == 2
}

func testCopyStringVar() bool {
	b := make([]byte, 2)
	s := "cd"
	n := copy(b, s)
	return n == 2 && string(b) == "cd"
}

func testCopyStringConst() bool {
	b := make([]byte, 2)
	n := copy(b, "cd")
	return n == 2 && string(b) == "cd"
}

func testCopyStringShortDst() bool {
	b := make([]byte, 1)
	n := copy(b, "cd")
	return n == 1 && b[0] == 'c'
}

func copyBytesOrString[S ~[]byte | ~string](b []byte, s S) int {
	return copy(b, s)
}

func testCopyGenericString() bool {
	b := make([]byte, 2)
	n := copyBytesOrString(b, "cd")
	return n == 2 && string(b) == "cd"
}

func testCopyGenericBytes() bool {
	b := make([]byte, 2)
	n := copyBytesOrString(b, []byte("cd"))
	return n == 2 && string(b) == "cd"
}
