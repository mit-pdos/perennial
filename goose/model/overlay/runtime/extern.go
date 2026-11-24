// The Go model of runtime.buildVersion (Perennial/Code/runtime.toml, [model]),
// spliced into extern.go in place of the real declaration.

package runtime

import "internal/gomodel"

// MODEL: buildVersion is the Go tree's version string at build time, the
// string Version returns. Go's declaration has no initializer: the linker
// writes the value into the binary (cmd/link/internal/ld/main.go:
// addstrdata1(ctxt, "runtime.buildVersion="+buildVersion), the toolchain's
// version, plus "-X:<experiments>" for a non-default GOEXPERIMENT), schedinit
// replaces an empty value by "unknown", and `-ldflags=-X
// runtime.buildVersion=<s>` sets any string s, invalid UTF-8 included
// (goose/model/runtime/version_test.go). Nothing writes it after that (a
// go:linkname pull of it is refused by the linker since Go 1.23). The model
// initializes it to an arbitrary string (gomodel.ChooseString, which can be
// every string): every value Go can have is one of its values. The
// translation of the real declaration would be "", more defined than Go.
var buildVersion = gomodel.ChooseString()
