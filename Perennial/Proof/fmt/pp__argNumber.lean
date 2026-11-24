/-
The proof of `fmt.(*pp).argNumber`.
-/
module

public import Perennial.Spec.fmt.pp__argNumber

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.pp.argNumber.wp_proof : fmt.pp.argNumber.spec (GF := GF) (hG := hG) :=
    fun p argNum format i numArgs hi hc => by
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  wp_if_destruct
  · iapply HΦ
    ipureintro; trivial
  · have hlt : sint.nat i < format.length := by word
    obtain ⟨c, hc'⟩ : ∃ c, format[sint.nat i]? = some c :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [ite_eq_left hi, hc']
    have hc91 : c ≠ W8 91 := fun h => hc (h ▸ hc')
    wp_auto
    rw [show (!decide (c = W8 91)) = true by simpa using hc91]
    wp_auto
    iapply HΦ
    ipureintro; trivial

end proof

end Perennial
