// Package pkg is translated with the overlay of TestOverlay
// (../overlay.json, whose relative paths are relative to goose/,
// where the test runs), which adds and replaces files of it.
package pkg

type Counter struct {
	n uint64
}

func (c *Counter) Get() uint64 {
	return c.n
}
