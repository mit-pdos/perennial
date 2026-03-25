package externalglobals

import (
	"github.com/mit-pdos/perennial/goose/testdata/examples/unittest"
)

func f() {
	unittest.GlobalX = 11
}
