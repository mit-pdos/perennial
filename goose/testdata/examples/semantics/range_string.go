package semantics

type rangeStr string

// tests
func testRangeStringASCII() bool {
	var keys int
	var sum rune
	for i, r := range "abc" {
		keys += i
		sum += r
	}
	return keys == 3 && sum == 'a'+'b'+'c'
}

func testRangeStringMultibyte() bool {
	// 'é' has 2 bytes, '世' 3 and '😀' 4
	s := "aé世😀b"
	var keys [5]int
	var runes [5]rune
	n := 0
	for i, r := range s {
		keys[n] = i
		runes[n] = r
		n++
	}
	return n == 5 &&
		keys == [5]int{0, 1, 3, 6, 10} &&
		runes == [5]rune{'a', 'é', '世', '😀', 'b'}
}

func testRangeStringInvalid() bool {
	// a stray continuation byte, an invalid byte, a truncated 3-byte
	// sequence, an encoded surrogate and an overlong encoding of '/'
	s := "\x80\xff\xe4\xb8\xed\xa0\x80\xc0\xaf"
	var keys []int
	for i, r := range s {
		if r != '�' {
			return false
		}
		keys = append(keys, i)
	}
	if len(keys) != len(s) {
		return false
	}
	for i := range keys {
		if keys[i] != i {
			return false
		}
	}
	return true
}

func testRangeStringKeysOnly() bool {
	var keys int
	for i := range "aé世" {
		keys += i
	}
	var n int
	for range "aé世" {
		n++
	}
	return keys == 0+1+3 && n == 3
}

func testRangeStringValuesOnly() bool {
	var sum rune
	for _, r := range "é世" {
		sum += r
	}
	return sum == 'é'+'世'
}

func testRangeStringBreakContinue() bool {
	var sum rune
	for _, r := range "abcdef" {
		if r == 'b' {
			continue
		}
		if r == 'e' {
			break
		}
		sum += r
	}
	return sum == 'a'+'c'+'d'
}

func rangeStringFind(s string, x rune) int {
	for i, r := range s {
		if r == x {
			return i
		}
	}
	return -1
}

func testRangeStringReturn() bool {
	return rangeStringFind("aé世", '世') == 3 && rangeStringFind("abc", 'z') == -1
}

func testRangeStringEmpty() bool {
	for range "" {
		return false
	}
	return true
}

func testRangeStringNamed() bool {
	s := rangeStr("a世")
	var keys int
	for i := range s {
		keys += i
	}
	return keys == 1
}

func testRangeStringAssign() bool {
	var i int
	var r rune
	for i, r = range "ab世" {
	}
	return i == 2 && r == '世'
}

func testRangeStringEvalOnce() bool {
	calls := 0
	f := func() string {
		calls++
		return "abc"
	}
	n := 0
	for range f() {
		n++
	}
	return calls == 1 && n == 3
}

// countRune returns the number of runes of s that are x.
func countRune(s string, x rune) int {
	n := 0
	for _, r := range s {
		if r == x {
			n++
		}
	}
	return n
}

func testRangeStringCount() bool {
	return countRune("aé世é", 'é') == 2 && countRune("\xffa\xe4\xb8", '�') == 3
}
