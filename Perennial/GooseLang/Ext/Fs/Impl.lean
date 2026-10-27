/-
The filesystem extension of GooseLang [Trusted definitions!].

A node's durable filesystem: a map from file names to contents, with
whole-file operations.

**A toy, not a sound model of a Linux filesystem.** It is the example
extension of the crash adequacy theorem (`crashfs`). Known divergences from its
Go side (`crashfs/fsext`) on a real filesystem, where the model is more defined
than Go: names are byte strings, so two names of one file (`x`, `./x`,
`sub/../x`) are two files of the model; files the operating system changes on
its own (`/proc/self/stat`) are constant in the model; a temporary file left by
a `Write` interrupted by a crash is not in the model; a `Read` of a huge file
may exhaust memory in Go and not in the model.

* `"Read"` of `f` returns the entire contents of the file `f`. Reading a file that
  does not exist is stuck.
* `"Write"` of `(f, data)` replaces the entire contents of the file `f` by `data`,
  creating it if it does not exist. The write is atomic and durable: once it
  is visible (to a read), a crash keeps it, and a crash never exposes a
  partial write.
* Neither operation fails. The Go side (`crashfs/fsext`, whose
  `TrustedCode` model states what is trusted about it) retries a failed
  operation instead of reporting it, and serializes the operations, so that a
  write is durable before any read sees it.
* Crashes (`ExtSemantics.crash`): the files survive unchanged.
* Neither operation changes the heap; file names and contents are passed and
  returned as Go values (`#f`, `#data`).
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

/-- The files of a node: name to contents. -/
abbrev FsState := GMap GoString (List w8)

instance : Inhabited FsState := ⟨∅⟩

/-- The filesystem extension. It has no values of its own and no global state. -/
@[reducible] def fsExt : GooseExt where
  name := "github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsext"
  Val := Empty
  LocalState := FsState
  GlobalState := Unit

section fs
variable [GooseExts] [GoGlobalContext]

/-- The step relation of the filesystem. -/
def FsStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (fs : FsState) (_g : Unit)
    (e' : Expr) (h' : GMap Loc (NonAtomic val)) (fs' : FsState) (_g' : Unit) : Prop :=
  h' = h ∧
  match op with
  | "Read" => ∃ (f : GoString) (data : List w8),
      v = #f ∧ fs !! f = some data ∧ e' = Val (#data) ∧ fs' = fs
  | "Write" => ∃ (f : GoString) (data : List w8),
      v = PairV (#f) (#data) ∧ e' = Val (#()) ∧ fs' = <[f := data]> fs
  | _ => False

end fs

/-- On a crash, the files survive unchanged. -/
instance fs_semantics : ExtSemantics fsExt where
  step := FsStep
  crash fs fs' := fs' = fs

end Perennial
