package skip_unlisted

// ERROR the blank package variable _@skip_unlisted.go:10 (var _ = T{}) is not listed in a skip entry

type T struct{}

var _ = T{}

// as if a Go upgrade added it
var _ = T{}
