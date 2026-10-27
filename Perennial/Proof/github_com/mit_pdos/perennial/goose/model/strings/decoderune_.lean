module

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

set_option maxHeartbeats 2000000 in
theorem github_com.mit_pdos.perennial.goose.model.strings.decoderune.wp_proof :
    github_com.mit_pdos.perennial.goose.model.strings.decoderune.spec (GF := GF) (hG := hG) := by
  intro s E str k hk0 hk
  wp_start
  wp_auto
  wp_apply wp_string_len with %Hlen
  wp_if_destruct
  · exfalso; word
  wp_apply wp_string_len with %-
  rw [if_pos (by word)]
  have htake : List.take (sint.nat (W64 ↑str.length) - sint.nat k) (List.drop (sint.nat k) str) =
      List.drop (sint.nat k) str := by
    apply List.take_of_length_le; simp only [List.length_drop]; word
  rw [htake]
  have htlen : 0 < (List.drop (sint.nat k) str).length := by simp only [List.length_drop]; omega
  have htle : (List.drop (sint.nat k) str).length ≤ str.length := by simp only [List.length_drop]; omega
  generalize List.drop (sint.nat k) str = t at htlen htle ⊢
  have htl : sint.Z (W64 t.length) = t.length := by word
  have hget : ∀ i, i < t.length → t[i]? = some (t.getD i 0) := by
    intro i hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  wp_auto
  repeat' (first
    | wp_if_destruct
    | (simp (disch := word) only [hget]; wp_auto)
    | (wp_apply wp_string_len with %-))
  all_goals
    try simp only [@eq_comm Bool true, decide_eq_true_eq] at *
    try simp only [htl, show uint.Z (W8 192) = 192 by rfl, show uint.Z (W8 224) = 224 by rfl,
      show uint.Z (W8 240) = 240 by rfl, show uint.Z (W8 248) = 248 by rfl,
      show uint.Z (W8 128) = 128 by rfl, show uint.Z (W8 191) = 191 by rfl,
      show sint.Z (W32 127) = 127 by rfl, show sint.Z (W32 2047) = 2047 by rfl,
      show sint.Z (W32 65535) = 65535 by rfl, show sint.Z (W32 1114111) = 1114111 by rfl,
      show sint.Z (W32 55296) = 55296 by rfl, show sint.Z (W32 57343) = 57343 by rfl,
      show sint.Z (W64 1) = 1 by rfl, show sint.Z (W64 2) = 2 by rfl,
      show sint.Z (W64 3) = 3 by rfl] at *
    first
      | (exfalso; omega)
      | (simp only [go.decodeMulti, go.runeError]
         simp (disch := omega) only [ite_eq_left, ite_eq_right]
         try simp only [Nat.cast_ofNat]
         iapply HΦ
         iexact Hpre)
  done

end proof

end Perennial
