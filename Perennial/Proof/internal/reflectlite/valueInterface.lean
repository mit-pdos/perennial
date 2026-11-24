/-
The proof of `internal.reflectlite.valueInterface`.
-/
module

public import Perennial.Spec.internal.reflectlite.valueInterface
public import Perennial.Spec.internal.reflectlite.packEface
public import Perennial.Spec.internal.reflectlite.flag__kind

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.valueInterface.wp_proof
    (wp_flag_kind : internal.reflectlite.flag.kind.spec (GF := GF) (hG := hG))
    (wp_packEface : internal.reflectlite.packEface.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.valueInterface.spec (GF := GF) (hG := hG) :=
    @fun W _ _ t ut _ _ kt xv x hkt hi hn => by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  have hb := internal.reflectlite.flag_bits kt (internal.reflectlite.kindOf_lt hkt)
    (internal.reflectlite.kindOf_pos hkt)
  obtain ⟨hb0, hb0i, hbk, hbki, hbi, hbii, hbro, hbroi, -⟩ := hb
  have hk20 := internal.reflectlite.kne_20 kt (internal.reflectlite.kindOf_lt hkt)
    (internal.reflectlite.kindOf_ne_20 hkt hi)
  have hku := internal.reflectlite.kind_u8 kt (internal.reflectlite.kindOf_lt hkt)
  wp_start as Hx
  ihave ⟨%hF, Hx⟩ := internal.reflectlite.valueOfRepr_facts xv t kt x (internal.reflectlite.kindOf_lt hkt) (internal.reflectlite.kindOf_pos hkt) $$ Hx
  have hf : xv.flag' ≠ W64 0 ∧ xv.flag' &&& W64 31 = W64 kt := ⟨hF.2.1, hF.2.2.1⟩
  try wp_auto
  try simp only [hf.1]
  try wp_auto
  wp_meths
  try rw [hf.2, hku]
  try simp only [hk20, decide_false]
  try wp_auto
  wp_apply wp_packEface kt xv x hkt hi hn $$ [$Hx] as Hx
  iapply HΦ
  iexact Hx

end proof

end Perennial
