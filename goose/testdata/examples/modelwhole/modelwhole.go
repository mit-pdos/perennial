// Package modelwhole is translated with a whole-package Go model
// (goose/testdata/models/modelwhole, replaces = ["*"], translate listing its declarations):
// every declaration is the model's. W embeds counter, so W's method sets have
// the methods promoted from it, whose MethodUnfold the translation has
// although no declaration W.get exists.
package modelwhole

type counter struct {
	n uint64
}

func (c counter) get() uint64 { return c.n }

func (c *counter) inc() { c.n++ }

// W has get and inc through its embedded counter.
type W struct {
	counter
}

// Get returns w's count.
func (w W) Get() uint64 { return w.get() }
