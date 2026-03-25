package semantics

import (
	"sync"

	"github.com/goose-lang/primitive"
)

func testLinearize() bool {
	m := new(sync.Mutex)
	m.Lock()
	primitive.Linearize()
	m.Unlock()
	return true
}
