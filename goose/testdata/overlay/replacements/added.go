//go:build goose || pbmodel

package pkg

// Inc is a method added to Counter by the overlay (as pkg/added.go).
func (c *Counter) Inc() {
	c.n += 1
}
