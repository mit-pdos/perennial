package unittest

func IterateMapKeys(m map[uint64]uint64, sum *uint64) {
	for k := range m {
		oldSum := *sum
		*sum = oldSum + k
	}
}

func MapSize(m map[uint64]bool) uint64 {
	return uint64(len(m))
}

type IntWrapper uint64

type MapWrapper map[uint64]bool

func MapTypeAliases(m1 map[IntWrapper]bool, m2 MapWrapper) {
	m1[4] = m2[uint64(0)]
}

func StringMap(m map[string]uint64) uint64 {
	return m["foo"]
}

type mapElem struct {
	a uint64
	b uint64
}

func mapUpdateField() {
	x := make(map[uint64]*mapElem)
	x[0].a = 10
}

var mapLiteral = map[string]uint64{
	"a": 10,
}

var mapLiteralWithConversion = map[any]any{
	"a": 10,
}

func mapGetCall() {
	handlers := make(map[uint64]func())
	handlers[0] = func() {}
	handlers[0]()
}

func mapLiteralTest() map[string]uint64 {
	ascii := map[string]uint64{
		"a": 97,
		"b": 98,
		"c": 99,
	}
	return ascii
}

func mapClearTest() int {
	m := make(map[int]bool)
	m[1] = true
	m[2] = false
	m[7] = true
	clear(m)
	return len(m)
}

func mapLookupConversion() bool {
	m := make(map[any]bool)
	return m["ok"]
}
