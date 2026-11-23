//go:build !goose

package pkg

// Excluded is added by the overlay (as pkg/excluded.go) under a build
// constraint goose does not meet: it is not translated.
func Excluded() uint64 {
	return 3
}
