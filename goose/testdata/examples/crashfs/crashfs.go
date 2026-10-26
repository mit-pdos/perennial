// Package crashfs is an example of a crash-safe program: Main is the boot
// program, which runs when the node starts and again after every crash. It
// marks the file "f" as done, and checks (by panicking) that the file only ever
// holds "" (not yet done) or "done", and that the write is durable. Its proof,
// with the crash adequacy theorem, is in
// Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/crashfs.
package crashfs

import "github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsffi"

func Main() {
	s := fsffi.Read("f")
	if s == "" {
		fsffi.Write("f", "done")
	} else if s != "done" {
		panic("unexpected contents")
	}
	if fsffi.Read("f") != "done" {
		panic("write lost")
	}
}
