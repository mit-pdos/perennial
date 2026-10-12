/-
The proof of `internal.abi.initialize'`.
-/
module

public import Perennial.Spec.internal.abi.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.abi.Assumptions]

theorem internal.abi.initialize'.wp_proof :
    internal.abi.initialize'.spec (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoSlice) kindNames (go.SliceType go.string) as Hk
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) _
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨-, -⟩
  wp_auto
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
