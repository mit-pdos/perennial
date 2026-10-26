/-
Trusted Go model of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsffi`
(namespace of the generated package), in terms of the filesystem extension of
`Perennial.GooseLang.Ext.Fs.Impl` (`fsExt` and its operations `FsOp.*`), for any
program whose extensions include it.

The Go functions are primitives: `Read(name string) string` and
`Write(name, data string)`, whole-file operations on a durable filesystem (the Go
implementation reads with `os.ReadFile`, and writes a temporary file, syncs it
and renames it over the file, so that the write is atomic and durable). A Go
string is a value (`#s`), as the extension's operations take and return. The
model is less defined than Go: reading a file that does not exist is stuck,
where Go panics, and the model has no I/O errors, where Go panics.
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ext.Fs.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi
section fs
variable [GooseExts] [ElemExt fsExt] [GoGlobalContext]

/-- Type: func(string) string -/
def Read.impl : val :=
  λ: "name", ExternalOp (extOp fsExt FsOp.ReadOp) "name"

/-- Type: func(string, string) -/
def Write.impl : val :=
  λ: "name" "data", ExternalOp (extOp fsExt FsOp.WriteOp) ("name", "data")

end fs
end github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi

end Perennial
