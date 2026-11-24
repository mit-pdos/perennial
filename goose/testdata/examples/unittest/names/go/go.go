// Package gopkg is at a path whose last component is a framework namespace
// (`go`): its namespace is …names.go” (glang.NamespacePath), so its `len`
// cannot capture the framework's `go.len` that the importing package refers to.
package gopkg

func len[T any](x T) int { return 0 }

func Used() {}
