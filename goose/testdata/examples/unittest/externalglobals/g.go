package externalglobals

import (
	"github.com/mit-pdos/perennial/goose/testdata/examples/unittest"
)

func f() {
	unittest.GlobalX = 11
}

// unittest.MsTagged's unexported method tag is promoted: extTagged implements
// unittest.MsTagger, whose tag is unittest's, and not localTagger, whose tag is
// this package's (a different method in Go)
type extTagged struct {
	unittest.MsTagged
}

type localTagger interface {
	tag() uint64
}
