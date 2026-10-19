/-
The proof of `fmt.Sprintf`.
-/
module

public import Perennial.Spec.fmt.Sprintf
public import Perennial.Proof.fmt.SprintfModel

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.Sprintf.wp_proof :
    fmt.Sprintf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq Hxs
  wp_start as Hsl
  wp_auto
  ihave %Hxlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (n k : w64) (acc : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "argNum" ∷ argNum_ptr ↦ k ∗
      "out" ∷ out_ptr ↦ acc ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (format.length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (xs.length : Int)⌝ ∗
      "%Hacc" ∷ ⌜∀ r, SprintfOut (format.drop (sint.nat n)) (xs.drop (sint.nat k)) r →
        SprintfOut format xs (acc ++ r)⌝) $$ [i argNum out]
  · iexists _, _, _
    iframe
    ipureintro
    rw [show zero_val w64 = W64 0 from rfl, show zero_val GoString = [] from rfl,
      show sint.nat (W64 0) = 0 from rfl]
    exact ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => by simpa using h⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat n]? = some c ∧
        format.drop (sint.nat n) = c :: format.drop (sint.nat n + 1) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    rw [Hc]
    wp_auto
    wp_if_destruct
    · -- `%`
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_if_destruct
      · -- `%` and a byte `d` after it
        have Hlt1 : sint.nat n + 1 < format.length := by word
        obtain ⟨d, Hd, Hdrop1⟩ : ∃ d, format[sint.nat n + 1]? = some d ∧
            format.drop (sint.nat n + 1) = d :: format.drop (sint.nat n + 2) :=
          ⟨_, List.getElem?_eq_getElem Hlt1, List.drop_eq_getElem_cons Hlt1⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, Hd]
        wp_auto
        wp_if_destruct
        · -- `%%`
          wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro
          refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
          rw [show sint.nat (n + W64 2) = sint.nat n + 2 by word] at h
          have := Hacc (W8 37 :: r) (by rw [Hdrop, Hdrop1]; exact .percent _ _ _ h)
          simpa using this
        · -- `%` and a byte `d` other than `%`
          have Hnp : (format.drop (sint.nat n + 1)).head? ≠ some (W8 37) := by
            rw [Hdrop1]; simpa using Hif
          wp_if_destruct
          · -- an argument is left
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z args_sl.len from ⟨Hk.1, Hif⟩,
              and_self, ↓reduceIte]
            have Hklt : sint.nat k < xs.length := by word
            obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat k]? = some x ∧
                xs.drop (sint.nat k) = x :: xs.drop (sint.nat k + 1) :=
              ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
            wp_apply wp_load_slice_index args_sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
            · iframe; ipureintro; exact Hx
            have Hxmem : x ∈ xs := List.mem_of_getElem? Hx
            wp_apply wp_formatArg format n x ⟨Hn.1, by word⟩
              (fun ii h => Hxs ii (h ▸ Hxmem)) as %s %next %ok ⟨%Hf1, %Hf2⟩
            cases ok
            · wp_auto
              wp_apply wp_arbitraryString as %junk -
              wp_for_post
              iapply HΦ
              iframe
              ipureintro
              refine Hacc junk ?_
              rw [Hdrop, Hdropk]
              exact .other _ _ _ (Hf2 rfl Hnp _)
            · obtain ⟨Hn1, Hn2, Hout⟩ := Hf1 rfl
              wp_auto
              wp_for_post
              iframe
              iexists _, _, _
              iframe
              ipureintro
              refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
              rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word] at h
              have := Hacc (s ++ r) (by rw [Hdrop, Hdropk]; exact Hout _ _ h)
              simpa using this
          · -- no argument left
            wp_apply wp_arbitraryString as %junk -
            wp_for_post
            iapply HΦ
            iframe
            ipureintro
            refine Hacc junk ?_
            rw [Hdrop, show xs.drop (sint.nat k) = [] from List.drop_eq_nil_of_le (by word)]
            exact .other _ _ _ (not_simpleDirective_nil _ Hnp)
      · -- a trailing `%`
        have Hnp : (format.drop (sint.nat n + 1)).head? ≠ some (W8 37) := by
          rw [List.drop_eq_nil_of_le (by word)]; simp
        (try wp_auto)
        wp_if_destruct
        · -- an argument is left
          simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z args_sl.len from ⟨Hk.1, Hif⟩,
            and_self, ↓reduceIte]
          have Hklt : sint.nat k < xs.length := by word
          obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat k]? = some x ∧
              xs.drop (sint.nat k) = x :: xs.drop (sint.nat k + 1) :=
            ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
          wp_apply wp_load_slice_index args_sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
          · iframe; ipureintro; exact Hx
          have Hxmem : x ∈ xs := List.mem_of_getElem? Hx
          wp_apply wp_formatArg format n x ⟨Hn.1, by word⟩
            (fun ii h => Hxs ii (h ▸ Hxmem)) as %s %next %ok ⟨%Hf1, %Hf2⟩
          cases ok
          · wp_auto
            wp_apply wp_arbitraryString as %junk -
            wp_for_post
            iapply HΦ
            iframe
            ipureintro
            refine Hacc junk ?_
            rw [Hdrop, Hdropk]
            exact .other _ _ _ (Hf2 rfl Hnp _)
          · obtain ⟨Hn1, Hn2, Hout⟩ := Hf1 rfl
            wp_auto
            wp_for_post
            iframe
            iexists _, _, _
            iframe
            ipureintro
            refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
            rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word] at h
            have := Hacc (s ++ r) (by rw [Hdrop, Hdropk]; exact Hout _ _ h)
            simpa using this
        · -- no argument left
          wp_apply wp_arbitraryString as %junk -
          wp_for_post
          iapply HΦ
          iframe
          ipureintro
          refine Hacc junk ?_
          rw [Hdrop, show xs.drop (sint.nat k) = [] from List.drop_eq_nil_of_le (by word)]
          exact .other _ _ _ (not_simpleDirective_nil _ Hnp)
    · -- a byte other than `%`
      rw [Hc]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [c]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.byte #c)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Hc_sl, -⟩
      wp_apply wp_bytes_to_string $$ Hc_sl as -
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word] at h
      have := Hacc (c :: r) (by rw [Hdrop]; exact .byte c _ _ _ Hif h)
      simpa using this
  · -- the end of the format
    have Hnot : ¬ sint.Z n < sint.Z (W64 format.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    rw [show sint.nat n = format.length by word, List.drop_length] at Hacc
    wp_auto
    wp_if_destruct
    · -- arguments are left
      wp_apply wp_arbitraryString as %junk -
      iapply HΦ
      iframe
      ipureintro
      refine Hacc junk ?_
      rw [List.drop_eq_getElem_cons (show sint.nat k < xs.length by word)]
      exact .extra _ _ _
    · iapply HΦ
      iframe
      ipureintro
      have := Hacc [] (by rw [List.drop_eq_nil_of_le (by word)]; exact .done)
      simpa using this

end proof

end Perennial
