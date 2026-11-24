// Package modeloverlay is translated with the Go model overlay of its goose
// config ([model] in github_com/.../modeloverlay.toml): the model, in
// goose/testdata/models/modeloverlay, replaces the type Counter, its method Inc and the first init
// function, and adds bump (translated), choose (a primitive stub, in
// trusted) and unmodelled (names-only, in names_only). The translation has the model's declarations in the real ones'
// places, with go: positions in its model.go, and the real Get, the
// second init and the variables between them as they are.
package modeloverlay

import "sync/atomic"

var order []uint64

func init() {
	order = append(order, 1)
}

// Counter counts.
type Counter struct {
	n uint64
}

// Inc adds one.
func (c *Counter) Inc() {
	atomic.AddUint64(&c.n, 1)
}

// Get is not replaced: it reads the model's field n.
func (c *Counter) Get() uint64 {
	return c.n
}

var total uint64 = 2

func init() {
	order = append(order, total)
}
