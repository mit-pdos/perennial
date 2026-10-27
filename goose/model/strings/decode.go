package strings

// The constants and decoderune are copied verbatim from Go 1.26's
// runtime/utf8.go.

const (
	runeError = '\uFFFD'     // the "error" Rune or "Unicode replacement character"
	runeSelf  = 0x80         // characters below runeSelf are represented as themselves in a single byte.
	maxRune   = '\U0010FFFF' // Maximum valid Unicode code point.
)

// Code points in the surrogate range are not valid for UTF-8.
const (
	surrogateMin = 0xD800
	surrogateMax = 0xDFFF
)

const (
	t1 = 0x00 // 0000 0000
	tx = 0x80 // 1000 0000
	t2 = 0xC0 // 1100 0000
	t3 = 0xE0 // 1110 0000
	t4 = 0xF0 // 1111 0000
	t5 = 0xF8 // 1111 1000

	maskx = 0x3F // 0011 1111
	mask2 = 0x1F // 0001 1111
	mask3 = 0x0F // 0000 1111
	mask4 = 0x07 // 0000 0111

	rune1Max = 1<<7 - 1
	rune2Max = 1<<11 - 1
	rune3Max = 1<<16 - 1

	// The default lowest and highest continuation byte.
	locb = 0x80 // 1000 0000
	hicb = 0xBF // 1011 1111
)

// countrunes returns the number of runes in s.

// DecodeRune is the step of a range loop over s at byte index k, 0 <= k <
// len(s), as gc lowers the loop (cmd/compile/internal/walk/range.go): it
// returns the rune at k and the index of the next iteration. A byte below
// runeSelf is a rune by itself; any other starts a rune that decoderune
// decodes.
func DecodeRune(s string, k int) (r rune, next int) {
	if s[k] < runeSelf {
		return rune(s[k]), k + 1
	}
	return decoderune(s, k)
}

// decoderune returns the non-ASCII rune at the start of
// s[k:] and the index after the rune in s.
//
// decoderune assumes that caller has checked that
// the to be decoded rune is a non-ASCII rune.
//
// If the string appears to be incomplete or decoding problems
// are encountered (runeerror, k + 1) is returned to ensure
// progress when decoderune is used to iterate over a string.
func decoderune(s string, k int) (r rune, pos int) {
	pos = k

	if k >= len(s) {
		return runeError, k + 1
	}

	s = s[k:]

	switch {
	case t2 <= s[0] && s[0] < t3:
		// 0080-07FF two byte sequence
		if len(s) > 1 && (locb <= s[1] && s[1] <= hicb) {
			r = rune(s[0]&mask2)<<6 | rune(s[1]&maskx)
			pos += 2
			if rune1Max < r {
				return
			}
		}
	case t3 <= s[0] && s[0] < t4:
		// 0800-FFFF three byte sequence
		if len(s) > 2 && (locb <= s[1] && s[1] <= hicb) && (locb <= s[2] && s[2] <= hicb) {
			r = rune(s[0]&mask3)<<12 | rune(s[1]&maskx)<<6 | rune(s[2]&maskx)
			pos += 3
			if rune2Max < r && !(surrogateMin <= r && r <= surrogateMax) {
				return
			}
		}
	case t4 <= s[0] && s[0] < t5:
		// 10000-1FFFFF four byte sequence
		if len(s) > 3 && (locb <= s[1] && s[1] <= hicb) && (locb <= s[2] && s[2] <= hicb) && (locb <= s[3] && s[3] <= hicb) {
			r = rune(s[0]&mask4)<<18 | rune(s[1]&maskx)<<12 | rune(s[2]&maskx)<<6 | rune(s[3]&maskx)
			pos += 4
			if rune3Max < r && r <= maxRune {
				return
			}
		}
	}

	return runeError, k + 1
}
