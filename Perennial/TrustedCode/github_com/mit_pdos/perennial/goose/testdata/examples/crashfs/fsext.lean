/-
Trusted Go model of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsext`
(namespace of the generated package), in terms of the filesystem extension of
`Perennial.GooseLang.Ext.Fs.Impl` (`fsExt` and its operations `FsOp.*`), for any
program whose extensions include it.

The Go functions are primitives: `Read(name string) string` and
`Write(name, data string)`, whole-file operations on a durable filesystem.
What is trusted is the operating system's file API (`os.ReadFile`,
`os.CreateTemp`, `File.Sync`, `os.Rename`, ...), which goose leaves
axiomatized, together with the claim that the Go implementation composes it
into atomic, durable whole-file operations: the operations hold a package
mutex, so that no `Read` sees a `Write` before it is durable; a `Write` writes
a fresh temporary file in the file's directory, syncs it, renames it over the
file and syncs the directory; a failed operation is retried, never reported.
A Go string is a value (`#s`), as the extension's operations take and return.

The model departs from Go only by being less defined: reading a file that does
not exist is stuck (Go retries forever), and an operation that Go keeps
retrying forever on a persistent I/O error succeeds in the model; as a safety
model, the model only needs to cover the executions in which the Go operation
returns. Files the implementation leaves behind (a temporary file of a `Write`
interrupted by a crash) are not in the model, so reading one is stuck.

This is a toy extension, not a sound model of a Linux filesystem: see the
divergences listed in `Perennial/GooseLang/Ext/Fs/Impl.lean`.
-/
module

public import Perennial.Golang.Defn
public import Perennial.GooseLang.Ext.Fs.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext
section fs
variable [GooseExts] [ElemExt fsExt] [GoGlobalContext]

/-- Type: func(string) string -/
def Read.impl : val :=
  λ: "name", ExternalOp (extOp fsExt FsOp.ReadOp) "name"

/-- Type: func(string, string) -/
def Write.impl : val :=
  λ: "name" "data", ExternalOp (extOp fsExt FsOp.WriteOp) ("name", "data")

end fs
end github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext

end Perennial
