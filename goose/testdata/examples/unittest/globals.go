package unittest

func foo() uint64 {
	return 10
}

var GlobalX uint64 = foo()
var globalY string

var globalA, globalB = "a", "b"

const MaxRune = '\U0010FFFF'
const runeWithType rune = 'a'
const IntWidth = 8

var _ = foo()

func other() {
	globalY = "ok"
}

func bar() {
	other()
	if GlobalX != 10 || globalY != "ok" {
		panic("bad")
	}
}

func init() {
	GlobalX = GlobalX
}

func init() {
	globalY = ""
}

func useUntypedRune() {
	if runeWithType > MaxRune {
		panic("invalid comparison")
	}
}
