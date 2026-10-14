/-
The proof of `time.Time.addSec`.
-/
module

public import Perennial.Spec.time.Time__addSec
public import Perennial.Spec.time.Time__stripMono

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Time.addSec.wp_proof
    (wp_Time_stripMono : time.Time.stripMono.spec (GF := GF) (hG := hG)) :
    time.Time.addSec.spec (GF := GF) (hG := hG) := by
  intro l tv d
  wp_start as Hl
  wp_auto
  wp_if_destruct
  · wp_if_destruct <;> (try wp_if_destruct) <;> wp_end
  · wp_if_destruct
    · wp_if_destruct
      · wp_end
      · wp_apply wp_Time_stripMono $$ [$Hl] as %tv' Hl
        wp_if_destruct <;> (try wp_if_destruct) <;> wp_end
    · wp_apply wp_Time_stripMono $$ [$Hl] as %tv' Hl
      wp_if_destruct <;> (try wp_if_destruct) <;> wp_end

end proof

end Perennial
