// Package dep has a package variable, X, whose initializer the model skips:
// its configuration (dep/github_com/.../skipinit/dep.toml, and
// Perennial/Code/.../skipinit/dep.toml) lists X as trusted, with the model
// `def X.init : val := go.skipInit` (Perennial/TrustedCode/.../skipinit/dep.lean).
// X is then not allocated, so code that loads or stores it has no proof, and
// package user shows that code that can only reach such a load in a branch it
// never takes is still provable.
package dep

// X's initializer can be skipped: newX only allocates, so it cannot panic and
// has no effect beyond X.
var X = newX()

func newX() *uint64 {
	v := uint64(42)
	return &v
}
