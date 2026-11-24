/-
`fmt.Sprintf`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `fmt.Sprintf(format, args...)`, for a format made of the pieces `ps` and arguments that are
the `as` (`fmt.isArg`), in the verified subset (`fmt.Fits`: literal text, `%%`, `%d %v %x` and
`%0Nd %0Nv %0Nx` of an integer, `%v` of a bool or `nil`, `%s %v %x` of a string or of a value with
an `Error()` or `String()` method, `%s %v %d %x` of a `[]byte`; one argument per directive):
returns the string `s` with `fmt.Out ps as s`, the pieces' outputs in order. The arguments' slice
and what `isArg` holds (a `[]byte`'s contents) come back. -/
abbrev fmt.Sprintf.spec : Prop :=
  ∀ (format : GoString) (ps : List Piece) (args_sl : GoSlice) (xs : List GoInterface)
    (args : List Arg) (dq : DFrac),
    format = encode ps → Fits ps args →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        [∗list] x;a ∈ xs;args, isArg x a }}
      (App (App (Val (@! Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ([∗list] x;a ∈ xs;args, isArg x a) ∗
        ⌜Out ps args s⌝ }}

end spec

end Perennial
