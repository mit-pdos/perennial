/-
Trusted models of part of `os`'s package initialization (namespace `os`, as the generated
package): the initializers of the package-level variables whose initializer calls code Perennial
does not translate, and `os`'s `init` function. The other initializers (the `errors.New` errors,
`checkWrapErr`, `dirBufPool`) are translated (`Code/os.toml`).

`os` is translated names-only otherwise, so no translated code calls an `os` function, and the only
`os` variable translated code reads is `Stderr` (a logger's output, e.g. raft's `DefaultLogger`).
Every initializer below is of Go 1.26's `os` for linux (the toolchain the standard library is
translated from). Each cannot panic; the models of the variables no translated code reads do
nothing, and in particular do not allocate the variable, so a translated reader would be stuck
(the model is less defined than Go there, never different). `Stderr`'s model allocates the
variable and stores a fresh `*File` in it.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace os
section code
variable [GooseExts] [GoGlobalContext]

/-! ### Copies of `io/fs`'s and `internal/poll`'s errors

`error.go`: `ErrInvalid = fs.ErrInvalid`, ..., `ErrClosed = fs.ErrClosed` copy an `io/fs` error
variable, `ErrNoDeadline = errNoDeadline()` and `ErrDeadlineExceeded = errDeadlineExceeded()`
return `internal/poll`'s `ErrNoDeadline` and `ErrDeadlineExceeded`. Neither package is
translated. Each cannot panic and has no other effect. -/

/-- `ErrInvalid = fs.ErrInvalid` (`error.go`). The model does nothing. -/
def ErrInvalid.init : val := λ: <>, #()
/-- `ErrPermission = fs.ErrPermission` (`error.go`). The model does nothing. -/
def ErrPermission.init : val := λ: <>, #()
/-- `ErrExist = fs.ErrExist` (`error.go`). The model does nothing. -/
def ErrExist.init : val := λ: <>, #()
/-- `ErrNotExist = fs.ErrNotExist` (`error.go`). The model does nothing. -/
def ErrNotExist.init : val := λ: <>, #()
/-- `ErrClosed = fs.ErrClosed` (`error.go`). The model does nothing. -/
def ErrClosed.init : val := λ: <>, #()
/-- `ErrNoDeadline = errNoDeadline()` (`error.go`; `return poll.ErrNoDeadline`). The model does
nothing. -/
def ErrNoDeadline.init : val := λ: <>, #()
/-- `ErrDeadlineExceeded = errDeadlineExceeded()` (`error.go`; `return poll.ErrDeadlineExceeded`).
The model does nothing. -/
def ErrDeadlineExceeded.init : val := λ: <>, #()

/-! ### Signals -/

/-- `Interrupt Signal = syscall.SIGINT` (`exec_posix.go`): a constant of `syscall`'s type
`Signal` (not translated) converted to the interface `os.Signal`. The model does nothing. -/
def Interrupt.init : val := λ: <>, #()
/-- `Kill Signal = syscall.SIGKILL` (`exec_posix.go`): as `Interrupt`. The model does nothing. -/
def Kill.init : val := λ: <>, #()

/-! ### The standard files -/

/-- `Stdin = NewFile(uintptr(syscall.Stdin), "/dev/stdin")` (`file.go`). `NewFile` on a
non-negative descriptor queries its flags (`unix.Fcntl`, a system call, whose error it ignores)
and builds a `*File` (`newFile`: `internal/poll`'s `FD`, a cleanup), so it bottoms out in system
calls and the runtime; it cannot panic, and has no effect other code observes. The model does
nothing. -/
def Stdin.init : val := λ: <>, #()
/-- `Stdout = NewFile(uintptr(syscall.Stdout), "/dev/stdout")` (`file.go`): as `Stdin`. The
model does nothing. -/
def Stdout.init : val := λ: <>, #()

/-- `Stderr = NewFile(uintptr(syscall.Stderr), "/dev/stderr")` (`file.go`): as `Stdin`, and
`NewFile` returns a non-nil `*File`. The model allocates `Stderr` (named by its string as goose
names it, since this file comes before the generated code) and stores a freshly allocated zero
`File` in it: a fresh, non-nil `*File`, as Go's. Go's `File` holds a pointer to a `file` (the
descriptor, the name, ...) where the model's holds `nil`; only `*File`'s methods read it, and
they are not translated (`os` is names-only), so no translated code can tell the two apart. -/
def Stderr.init : val :=
  λ: <>,
    go.GlobalAlloc go!"os.Stderr" (go.PointerType (go.Named go!"os.File" [])) #() ;;
    GlobalVarAddr go!"os.Stderr" #() <-[go.PointerType (go.Named go!"os.File" [])]
      (GoAlloc (go.Named go!"os.File" []) (GoZeroVal (go.Named go!"os.File" []) #()))

/-! ### Other variables -/

/-- The blank variables `var _ fs.StatFS = dirFS("")`, `fs.ReadFileFS`, `fs.ReadDirFS`,
`fs.ReadLinkFS` (`file.go`): conversions of a string to `io/fs`'s interfaces (not translated),
which cannot panic and are discarded. The model of each does nothing. -/
def «_».init : val := λ: <>, #()
/-- `lstat = Lstat` (`file.go`): a function value, whose type `func(string) (FileInfo, error)`
names `io/fs`'s `FileInfo` (through the alias `os.FileInfo`), which goose cannot name with `io/fs`
untranslated. The model does nothing. -/
def lstat.init : val := λ: <>, #()
/-- `checkPidfdOnce = sync.OnceValue(checkPidfd)` (`pidfd_linux.go`): `OnceValue` only builds a
closure (it does not call `checkPidfd`); Perennial translates `sync.OnceValue` names-only. The
model does nothing. -/
def checkPidfdOnce.init : val := λ: <>, #()
/-- `pollCopyFileRange = poll.CopyFileRange` (`zero_copy_linux.go`): a function value of
`internal/poll` (not translated). The model does nothing. -/
def pollCopyFileRange.init : val := λ: <>, #()
/-- `pollSplice = poll.Splice` (`zero_copy_linux.go`): as `pollCopyFileRange`. The model does
nothing. -/
def pollSplice.init : val := λ: <>, #()

/-! ### `init` -/

/-- `os`'s `init` (`proc.go`):

```go
func init() {
	if runtime.GOOS == "windows" {
		// Initialized in exec_windows.go.
		return
	}
	Args = runtime_args()
}
```

`runtime_args` is a `go:linkname` into the runtime, with no Go body: it returns a copy of the
command-line arguments, and cannot panic. The model does nothing: `Args` is read by no
translated code (and is not allocated, `os` being names-only there). -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end os

end Perennial
