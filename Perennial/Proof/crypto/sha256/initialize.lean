/-
The proof of `crypto/sha256.initialize'`.
-/
module

public import Perennial.Spec.crypto.sha256.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] {ok : Sha256Filter} [HasSha256 ok]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha256.Assumptions]

theorem crypto.sha256.initialize'.wp_proof :
    crypto.sha256.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  -- init.0: its trusted body does nothing
  wp_auto
  repeat (first | wp_func_call | wp_call | wp_auto)
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
