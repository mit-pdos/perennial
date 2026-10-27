package strings

const (
	runeError = '�'
	runeSelf  = 0x80
	maxRune   = '\U0010FFFF'

	surrogateMin = 0xD800
	surrogateMax = 0xDFFF

	t2 = 0xC0
	t3 = 0xE0
	t4 = 0xF0
	t5 = 0xF8

	maskx = 0x3F
	mask2 = 0x1F
	mask3 = 0x0F
	mask4 = 0x07

	rune1Max = 1<<7 - 1
	rune2Max = 1<<11 - 1
	rune3Max = 1<<16 - 1

	locb = 0x80
	hicb = 0xBF
)

// DecodeRune returns the rune that a range loop over s yields at byte index
// k, 0 <= k < len(s), and the index of the next iteration (runtime.decoderune,
// after the loop's test for a single-byte rune).
func DecodeRune(s string, k int) (r rune, next int) {
	if s[k] < runeSelf {
		return rune(s[k]), k + 1
	}
	s = s[k:]
	switch {
	case t2 <= s[0] && s[0] < t3:
		if len(s) > 1 && (locb <= s[1] && s[1] <= hicb) {
			r = rune(s[0]&mask2)<<6 | rune(s[1]&maskx)
			if rune1Max < r {
				return r, k + 2
			}
		}
	case t3 <= s[0] && s[0] < t4:
		if len(s) > 2 && (locb <= s[1] && s[1] <= hicb) && (locb <= s[2] && s[2] <= hicb) {
			r = rune(s[0]&mask3)<<12 | rune(s[1]&maskx)<<6 | rune(s[2]&maskx)
			if rune2Max < r && !(surrogateMin <= r && r <= surrogateMax) {
				return r, k + 3
			}
		}
	case t4 <= s[0] && s[0] < t5:
		if len(s) > 3 && (locb <= s[1] && s[1] <= hicb) && (locb <= s[2] && s[2] <= hicb) && (locb <= s[3] && s[3] <= hicb) {
			r = rune(s[0]&mask4)<<18 | rune(s[1]&maskx)<<12 | rune(s[2]&maskx)<<6 | rune(s[3]&maskx)
			if rune3Max < r && r <= maxRune {
				return r, k + 4
			}
		}
	}
	return runeError, k + 1
}
