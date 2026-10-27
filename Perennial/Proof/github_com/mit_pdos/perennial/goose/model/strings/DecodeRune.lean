module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.model.strings.DecodeRune
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.model.strings.decoderune_

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]

theorem github_com.mit_pdos.perennial.goose.model.strings.DecodeRune.wp_proof
    (wp_decoderune : github_com.mit_pdos.perennial.goose.model.strings.decoderune.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.model.strings.DecodeRune.spec (GF := GF) (hG := hG) := by
  intro s E str k hk0 hk
  wp_start
  wp_auto
  have hget : str[sint.nat k]? = some ((str.drop (sint.nat k)).getD 0 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  simp only [hk0, ↓reduceIte, hget]
  wp_auto
  unfold go.decodeRune
  simp only [show uint.Z (W8 128) = 128 by rfl]
  wp_if_destruct
  · simp only [hk0, ↓reduceIte, hget]
    wp_auto
    simp only [Hif, ↓reduceIte]
    rw [show k + W64 1 = W64 ((sint.nat k + 1 : Nat) : Int) by word]
    iapply HΦ
    iexact Hpre
  · wp_apply wp_decoderune str k hk0 hk
    simp only [Hif, ↓reduceIte]
    have hw := go.decodeMulti_len (str.drop (sint.nat k))
    simp only [List.length_drop] at hw
    rw [show k + W64 ((go.decodeMulti (str.drop (sint.nat k))).2 : Int) =
        W64 ((sint.nat k + (go.decodeMulti (str.drop (sint.nat k))).2 : Nat) : Int) by word]
    iapply HΦ
    iexact Hpre

end proof

end Perennial
