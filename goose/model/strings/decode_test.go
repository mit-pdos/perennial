package strings

import "testing"

func check(t *testing.T, s string) {
	var ks []int
	var rs []rune
	for k, r := range s {
		ks = append(ks, k)
		rs = append(rs, r)
	}
	j := 0
	for k := 0; k < len(s); j++ {
		r, next := DecodeRune(s, k)
		if j >= len(ks) || ks[j] != k || rs[j] != r {
			t.Fatalf("%q: iteration %d: got (%d, %U)", s, j, k, r)
		}
		k = next
	}
	if j != len(ks) {
		t.Fatalf("%q: %d iterations, want %d", s, j, len(ks))
	}
}

// DecodeRune steps through a string as a range loop over it does: on every
// string of up to 3 bytes, and on every 4-byte string with a 4-byte lead byte
// whose other bytes are around the continuation bytes 0x80-0xBF.
func TestDecodeRuneExhaustive(t *testing.T) {
	for n := 0; n <= 3; n++ {
		b := make([]byte, n)
		var rec func(i int)
		rec = func(i int) {
			if i == n {
				check(t, string(b))
				return
			}
			for c := 0; c < 256; c++ {
				b[i] = byte(c)
				rec(i + 1)
			}
		}
		rec(0)
	}
	for c0 := 0xF0; c0 < 0xF8; c0++ {
		for c1 := 0x7E; c1 < 0xC2; c1++ {
			for c2 := 0x7E; c2 < 0xC2; c2++ {
				for c3 := 0x7E; c3 < 0xC2; c3++ {
					check(t, string([]byte{byte(c0), byte(c1), byte(c2), byte(c3)}))
				}
			}
		}
	}
}

func FuzzDecodeRune(f *testing.F) {
	f.Add("héllo, 世界 \xff\xed\xa0\x80 \U0010FFFF")
	f.Fuzz(func(t *testing.T, s string) { check(t, s) })
}
