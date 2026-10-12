/-
The proof of `internal.bytealg.HashStr`.
-/
module

public import Perennial.Spec.internal.bytealg.HashStr
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

theorem internal.bytealg.HashStr.wp_proof :
    internal.bytealg.HashStr.spec (GF := GF) (hG := hG) := fun sep => by
  wp_start
  wp_auto
  ihave IH : iprop(∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "hash" ∷ hash_ptr ↦ rkHash (sep.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sep.length⌝) $$ [i hash]
  · iexists (W64 0)
    rw [show rkHash (sep.take (sint.nat (W64 0))) = W32 0 from rfl]
    iframe
    ipureintro
    exact ⟨by decide, by word⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have hlt : sint.nat i < sep.length := by word
    obtain ⟨c, hc⟩ : ∃ c, sep[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Hi.1, ↓reduceIte, hc]
    wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1)
    have Htake : sep.take (sint.nat (i + W64 1)) = sep.take (sint.nat i) ++ [c] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, hc]; rfl
    rw [Htake, rkHash_snoc, show (W32 16777619 : w32) = primeRK from rfl]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · have Hnot : ¬ sint.Z i < sint.Z (W64 sep.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    rw [show sint.nat i = sep.length by word, List.take_length]
    wp_auto
    rw [show (W32 16777619 : w32) = primeRK from rfl]
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    ihave IH2 : iprop(∃ (j : w64) (sq pw : w32),
        "i" ∷ i_ptr ↦ j ∗
        "sq" ∷ sq_ptr ↦ sq ∗
        "pow" ∷ pow_ptr ↦ pw ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ pw * sq ^ sint.nat j = primeRK ^ sep.length⌝) $$ [i sq pow]
    · iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [show sint.nat (W64 sep.length) = sep.length by word]
      grind
    wp_for IH2
    wp_if_destruct
    · have Hhalf : sint.Z (BitVec.sshiftRight' j (W64 1)) = sint.Z j / 2 := sshiftRight_one j Hj.1
      have Hhalf' : sint.nat (BitVec.sshiftRight' j (W64 1)) = sint.nat j / 2 := by
        show (sint.Z _).toNat = (sint.Z j).toNat / 2
        rw [Hhalf]; omega
      wp_if_destruct
      · -- `j` even
        have Heven : sint.nat j % 2 = 0 := (and_one_eq_zero_iff j Hj.1).1 Hif
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by word, ?_⟩
        rw [Hhalf', pow_sq, ← Hj.2, show 2 * (sint.nat j / 2) = sint.nat j by omega]
      · -- `j` odd: `pow *= sq`
        have Hodd : sint.nat j % 2 = 1 := by
          have := mt (and_one_eq_zero_iff j Hj.1).2 Hif; omega
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by word, ?_⟩
        rw [Hhalf', pow_sq, ← Hj.2]
        conv => rhs; rw [show sint.nat j = 2 * (sint.nat j / 2) + 1 by omega, BitVec.pow_succ]
        grind
    · have hj0 : sint.nat j = 0 := by word
      have hpw : pw = primeRK ^ sep.length := by rw [← Hj.2, hj0]; grind
      rw [hpw]
      iapply HΦ; itrivial

end proof

end Perennial
