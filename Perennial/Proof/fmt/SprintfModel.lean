/-
Specs of the helpers of the model of `fmt.Sprintf` (`Perennial/TrustedCode/fmt.lean`), which
are not functions of package `fmt`: `arbitraryString`, `formatInt`, `intVerb`, `intArg` and
`formatArg`.
-/
module

public import Perennial.Proof.fmt.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- The helper `fmt.arbitraryString` of the model of `Sprintf` returns some string. -/
theorem wp_arbitraryString :
    {{ (True : IProp GF) }}
      (App (Val arbitraryString) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ - HΦ
  unfold arbitraryString
  wp_auto
  ihave IH : iprop(∃ str : GoString, "s" ∷ s_ptr ↦ str) $$ [s]
  · iexists _; iframe
  wp_for IH
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %b -
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z b)]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z b)))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_apply wp_bytes_to_string $$ Hsl as -
    wp_for_post
    iframe
    iexists _
    iframe
  · have Hf : (!decide (c = W64 0)) = false := by
      revert Hif; cases (!decide (c = W64 0)) <;> simp
    rw [Hf]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

/-- The integer of sign `neg` and magnitude `mag`. -/
def signedValue (neg : Bool) (mag : w64) : Int := if neg then -uint.Z mag else uint.Z mag

theorem decimalPad_signedValue_false (w : Nat) (mag : w64) :
    decimalPad w (signedValue false mag) = padZeros w (decimalNat (uint.nat mag)) := by
  have h : (uint.Z mag).natAbs = uint.nat mag := by word
  simp only [decimalPad, signedValue, Bool.false_eq_true, ↓reduceIte, h]
  rw [ite_eq_right (by word)]

theorem decimalPad_signedValue_true (w : Nat) (mag : w64) (hmag : uint.Z mag ≠ 0) :
    decimalPad w (signedValue true mag) = W8 45 :: padZeros (w - 1) (decimalNat (uint.nat mag)) := by
  have h : (-uint.Z mag).natAbs = uint.nat mag := by word
  simp only [decimalPad, signedValue, ↓reduceIte, h]
  rw [ite_eq_left (by word)]

/-- The helper `fmt.formatInt` of the model of `Sprintf`: the decimal of the integer of sign `neg`
and magnitude `mag` (non-zero if `neg`), zero-padded to `width`. -/
theorem wp_formatInt (neg : Bool) (mag width : w64) (hneg : neg = true → uint.Z mag ≠ 0)
    (hw : 0 ≤ sint.Z width ∧ sint.Z width ≤ 1000000) :
    {{ (True : IProp GF) }}
      (App (App (App (Val formatInt) (Val #neg)) (Val #mag)) (Val #width))
    {{ RET #(decimalPad (sint.nat width) (signedValue neg mag)); True }} := by
  iintro %Φ - HΦ
  unfold formatInt
  wp_auto
  ihave IH : iprop(∃ (m : w64) (ds : GoString),
      "mag" ∷ mag_ptr ↦ m ∗
      "digits" ∷ digits_ptr ↦ ds ∗
      "%Hds" ∷ ⌜decimalNat (uint.nat mag) = decimalNat (uint.nat m) ++ ds⌝) $$ [mag digits]
  · iexists _, _
    iframe
    ipureintro
    simp [show zero_val GoString = [] from rfl]
  wp_for IH
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (m % W64 10)) + W8 48]
  wp_auto
  rw [show go.arrayLiteralSize
    [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z (m % W64 10)) + W8 48))] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_apply wp_bytes_to_string $$ Hsl as -
  have Hdig : W8 (uint.Z (m % W64 10)) + W8 48 = digitByte (uint.nat m % 10) := by
    unfold digitByte; word
  rw [Hdig]
  wp_if_destruct
  · -- the last digit
    wp_for_post
    have Hm : uint.nat m < 10 := by
      have := congrArg uint.Z Hif; word
    have HD : decimalNat (uint.nat mag) = [digitByte (uint.nat m % 10)] ++ ds := by
      rw [Hds, decimalNat_of_lt Hm, Nat.mod_eq_of_lt Hm]
    rw [← HD]
    generalize HDdef : decimalNat (uint.nat mag) = D
    have HDlen : D.length ≤ 20 := by
      rw [← HDdef]
      exact length_decimalNat_le _ 20 (by omega) (by word)
    -- the width without the sign
    obtain ⟨w1, W, Hw1, HW, Hwc⟩ : ∃ (w1 : w64) (W : Nat),
        (if neg then width - W64 1 else width) = w1 ∧
        W = (if neg then sint.nat width - 1 else sint.nat width) ∧
        ∀ n : Nat, n < 2 ^ 63 → (sint.Z (W64 n) < sint.Z w1 ↔ n < W) := by
      refine ⟨_, _, rfl, rfl, ?_⟩
      intro n hn
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try word)
    cases neg
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at Hw1 HW
      subst Hw1
      wp_auto
      ihave IH2 : iprop(∃ (k : Nat),
          "digits" ∷ digits_ptr ↦ (List.replicate k (W8 48) ++ D) ∗
          "%Hk" ∷ ⌜k ≤ W - D.length⌝) $$ [digits]
      · iexists 0; iframe; ipureintro; simp
      wp_for IH2
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
      wp_if_destruct
      · -- one more `0`
        have Hlt := (Hwc _ Hlen).1 (of_decide_eq_true (go.intoVal_inj Hif))
        wp_for_post
        iframe
        iexists k + 1
        have h48 : (48#8 : w8) = W8 48 := by decide
        rw [h48, List.singleton_append,
          show W8 48 :: (List.replicate k (W8 48) ++ D) = List.replicate (k + 1) (W8 48) ++ D from rfl]
        iframe
        ipureintro
        simp only [List.length_append, List.length_replicate] at Hlt
        omega
      · have Hge : ¬ (List.replicate k (W8 48) ++ D).length < W := fun h =>
          Hif (by rw [decide_eq_true ((Hwc _ Hlen).2 h)])
        simp only [decide_eq_false (fun h => Hge ((Hwc _ Hlen).1 h)),
          Bool.false_eq_true, ↓reduceIte]
        have Hpad : List.replicate k (W8 48) ++ D = padZeros W D := by
          unfold padZeros
          simp only [List.length_append, List.length_replicate] at Hge
          congr 2
          omega
        rw [Hpad]
        wp_auto
        rw [← HDdef]
        first
        | rw [decimalPad_signedValue_false, ← HW]
        | rw [decimalPad_signedValue_true _ _ (hneg rfl), ← HW,
            show ([45#8] ++ padZeros W (decimalNat (uint.nat mag))) =
              W8 45 :: padZeros W (decimalNat (uint.nat mag)) from by
                rw [show (45#8 : w8) = W8 45 by decide]; rfl]
        iapply HΦ
        itrivial
    done
  · wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    have Hm : 10 ≤ uint.nat m := by
      have : m / W64 10 ≠ W64 0 := fun h => Hif (by rw [h])
      word
    rw [Hds, decimalNat_of_ge Hm, show uint.nat (m / W64 10) = uint.nat m / 10 by word]
    simp

/-- The helper `fmt.intVerb` of the model of `Sprintf`: at the `%` at index `i` of `format`, the
integer directive that follows, `parseIntVerb` of the format after the `%`, with the index after
it. -/
theorem wp_intVerb (format : GoString) (i : w64)
    (Hi : 0 ≤ sint.Z i ∧ sint.Z i < (format.length : Int)) :
    {{ (True : IProp GF) }}
      (App (App (Val intVerb) (Val #format)) (Val #i))
    {{ (w next : w64) (ok : Bool), RET (PairV (PairV #w #next) #ok);
        ⌜ok = true → parseIntVerb (format.drop (sint.nat i + 1)) =
            some (sint.nat w, format.drop (sint.nat next)) ∧
          0 ≤ sint.Z w ∧ sint.Z w ≤ 1000000 ∧ sint.Z i < sint.Z next ∧
          sint.Z next ≤ (format.length : Int)⌝ ∗
        ⌜ok = false → parseIntVerb (format.drop (sint.nat i + 1)) = none⌝ }} := by
  iintro %Φ - HΦ
  unfold intVerb
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · -- a byte `c` after the `%`
    have Hlt : sint.nat i + 1 < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat i + 1]? = some c ∧
        format.drop (sint.nat i + 1) = c :: format.drop (sint.nat i + 2) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    have Hidx : format[sint.nat (i + W64 1)]? = some c := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]; exact Hc
    rw [Hidx]
    wp_auto
    have Hdrop2 : sint.nat (i + W64 2) = sint.nat i + 2 := by word
    by_cases hd : c = W8 100 ∨ c = W8 118
    · -- `%d` or `%v`
      rcases hd with h | h
      · subst h
        simp only [_root_.decide_true]
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro _
          rw [Hdrop, Hdrop2]
          refine ⟨by simp [parseIntVerb] <;> rfl, by word, by word, by word, by word⟩
        · ipureintro; intro h; cases h
      · subst h
        rw [decide_eq_false (by decide)]
        wp_auto
        rw [Hidx]
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro _
          rw [Hdrop, Hdrop2]
          refine ⟨by simp [parseIntVerb] <;> rfl, by word, by word, by word, by word⟩
        · ipureintro; intro h; cases h
    · rw [not_or] at hd
      rw [decide_eq_false hd.1]
      wp_auto
      rw [Hidx]
      wp_auto
      rw [decide_eq_false hd.2]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      rw [decide_eq_true Hif]
      wp_auto
      rw [Hidx]
      wp_auto
      by_cases h0 : c = W8 48
      · subst h0
        simp only [_root_.decide_true]
        wp_auto
        ihave IH : iprop(∃ (jv wv : w64) (Wn : Nat),
            "j" ∷ j_ptr ↦ jv ∗
            "width" ∷ width_ptr ↦ wv ∗
            "%Hinv" ∷ ⌜sint.Z wv = Wn ∧ Wn ≤ 10000009 ∧ sint.Z i + 2 ≤ sint.Z jv ∧
              sint.Z jv ≤ format.length ∧
              scanWidth 0 (format.drop (sint.nat i + 2)) =
                scanWidth Wn (format.drop (sint.nat jv))⌝) $$ [j width]
        · iexists _, _, 0
          iframe
          ipureintro
          refine ⟨rfl, by omega, by word, by word, by rw [Hdrop2]⟩
        wp_for IH
        obtain ⟨HWn, HWb, Hj1, Hj2, Hscan⟩ := Hinv
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        wp_if_destruct
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [List.drop_eq_nil_of_le (by word)]; rfl
        rotate_right
        have Hjlt : sint.nat jv < format.length := by word
        obtain ⟨cj, Hcj, Hdropj⟩ : ∃ cj, format[sint.nat jv]? = some cj ∧
            format.drop (sint.nat jv) = cj :: format.drop (sint.nat jv + 1) :=
          ⟨_, List.getElem?_eq_getElem Hjlt, List.drop_eq_getElem_cons Hjlt⟩
        rw [Hcj]
        wp_auto
        wp_if_destruct
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [Hdropj, scanWidth, ite_eq_right (by rintro ⟨h1, -, -⟩; apply Hif; word)]
        rotate_right
        rw [Hcj]
        wp_auto
        wp_if_destruct
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [Hdropj, scanWidth, ite_eq_right (by rintro ⟨-, h2, -⟩; apply Hif; word)]
        rotate_right
        by_cases Hwle : sint.Z wv ≤ sint.Z (W64 1000000)
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [Hdropj, scanWidth, ite_eq_right (by rintro ⟨-, -, h3⟩; apply Hwle; word)]
        simp only [decide_eq_false Hwle, Bool.false_eq_true, ↓reduceIte]
        rotate_right
        simp only [decide_eq_true Hwle, ↓reduceIte]
        -- a digit: the loop goes on
        wp_auto
        rw [Hcj]
        wp_auto
        wp_for_post
        iframe
        iexists _, _, Wn * 10 + (uint.nat cj - 48)
        iframe
        ipureintro
        refine ⟨by word, by word, by word, by word, ?_⟩
        rw [Hscan, Hdropj, scanWidth, ite_eq_left ⟨by word, by word, by word⟩,
          show sint.nat (jv + W64 1) = sint.nat jv + 1 by word]
        -- the end of the width: the four ways out of the loop
        all_goals
          have Hsc : scanWidth 0 (format.drop (sint.nat i + 2)) =
              (Wn, format.drop (sint.nat jv)) := Hscan.trans Hexit
          have Hparse : parseIntVerb (format.drop (sint.nat i + 1)) =
              (match format.drop (sint.nat jv) with
                | d :: rest =>
                  if (d :: rest).length < (format.drop (sint.nat i + 2)).length ∧ d = W8 100 ∧
                    Wn ≤ 1000000 then some (Wn, rest) else none
                | [] => none) := by
            rw [Hdrop, parseIntVerb, ite_eq_right (by rintro (h | h) <;> simp_all),
              ite_eq_left rfl, Hsc]
            generalize format.drop (sint.nat jv) = l
            cases l <;> rfl
          clear Hexit Hscan Hsc
          (try wp_auto)
          wp_if_destruct
          · -- a digit was read
            wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
            wp_if_destruct
            · have Hk : sint.nat jv < format.length := by word
              obtain ⟨ck, Hck, Hdropk⟩ : ∃ ck, format[sint.nat jv]? = some ck ∧
                  format.drop (sint.nat jv) = ck :: format.drop (sint.nat jv + 1) :=
                ⟨_, List.getElem?_eq_getElem Hk, List.drop_eq_getElem_cons Hk⟩
              rw [Hck]
              wp_auto
              by_cases hck : ck = W8 100
              · subst hck
                simp only [_root_.decide_true]
                wp_auto
                by_cases Hwle' : sint.Z wv ≤ sint.Z (W64 1000000)
                · simp only [decide_eq_true Hwle']
                  wp_auto
                  iapply HΦ
                  isplitl []
                  · ipureintro; intro _
                    refine ⟨?_, by word, by word, by word, by word⟩
                    rw [Hparse, Hdropk]
                    dsimp only
                    rw [ite_eq_left ⟨by simp; word, rfl, by word⟩,
                      show sint.nat (jv + W64 1) = sint.nat jv + 1 by word,
                      show sint.nat wv = Wn by word]
                  · ipureintro; intro h; cases h
                · simp only [decide_eq_false Hwle']
                  wp_auto
                  iapply HΦ
                  isplitl []
                  · ipureintro; intro h; cases h
                  · ipureintro; intro _
                    rw [Hparse, Hdropk]
                    dsimp only
                    rw [ite_eq_right (by rintro ⟨-, -, h⟩; apply Hwle'; word)]
              · rw [decide_eq_false hck]
                wp_auto
                iapply HΦ
                isplitl []
                · ipureintro; intro h; cases h
                · ipureintro; intro _
                  rw [Hparse, Hdropk]
                  dsimp only
                  rw [ite_eq_right (by rintro ⟨-, h, -⟩; exact hck h)]
            · iapply HΦ
              isplitl []
              · ipureintro; intro h; cases h
              · ipureintro; intro _
                rw [Hparse, List.drop_eq_nil_of_le (by word)]
          · -- no digit
            iapply HΦ
            isplitl []
            · ipureintro; intro h; cases h
            · ipureintro; intro _
              rw [Hparse, show sint.nat jv = sint.nat i + 2 by word]
              split
              · rw [ite_eq_right (by rintro ⟨h, -, -⟩; simp_all)]
              · rfl
      · rw [decide_eq_false h0]
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _
          rw [Hdrop]
          simp only [parseIntVerb, hd.1, hd.2, h0, _root_.or_self, ↓reduceIte]
  · -- a trailing `%`
    have Hnil : format.drop (sint.nat i + 1) = [] := List.drop_eq_nil_of_le (by word)
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_if_destruct
    · exfalso; word
    · iapply HΦ
      isplitl []
      · ipureintro; intro h; cases h
      · ipureintro; intro _; rw [Hnil]; rfl

set_option maxRecDepth 100000 in
/-- The helper `fmt.intArg` of the model of `Sprintf`: the sign and magnitude of the integer an
argument holds, if its dynamic type is one of Go's integer types. -/
theorem wp_intArg (x : GoInterface) (Hx : ∀ ii, x = interface.ok ii → ArgWf ii) :
    {{ (True : IProp GF) }}
      (App (Val intArg) (Val #x))
    {{ (neg : Bool) (mag : w64) (ok : Bool), RET (PairV (PairV #neg #mag) #ok);
        ⌜ok = true → ∃ ii, x = interface.ok ii ∧ IntArgValue ii (signedValue neg mag) ∧
          (neg = true → uint.Z mag ≠ 0)⌝ ∗
        ⌜ok = false → ∀ ii, x = interface.ok ii → ¬ IsIntType ii.ty⌝ }} := by
  iintro %Φ - HΦ
  unfold intArg
  wp_auto
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; simp
    · ipureintro; intro _ ii h; cases h
  | ok ii =>
    obtain ⟨ty, v⟩ := ii
    wp_auto
    by_cases h1 : ty = go.int
    · subst h1
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h1, ↓reduceIte, decide_false]
    wp_auto
    by_cases h2 : ty = go.int64
    · subst h2
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int64 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h2, ↓reduceIte, decide_false]
    wp_auto
    by_cases h3 : ty = go.int32
    · subst h3
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int32 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h3, ↓reduceIte, decide_false]
    wp_auto
    by_cases h4 : ty = go.int16
    · subst h4
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int16 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h4, ↓reduceIte, decide_false]
    wp_auto
    by_cases h5 : ty = go.int8
    · subst h5
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int8 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h5, ↓reduceIte, decide_false]
    wp_auto
    by_cases h6 : ty = go.uint
    · subst h6
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h6, ↓reduceIte, decide_false]
    wp_auto
    by_cases h7 : ty = go.uint64
    · subst h7
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint64 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h7, ↓reduceIte, decide_false]
    wp_auto
    by_cases h8 : ty = go.uint32
    · subst h8
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint32 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h8, ↓reduceIte, decide_false]
    wp_auto
    by_cases h9 : ty = go.uint16
    · subst h9
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint16 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h9, ↓reduceIte, decide_false]
    wp_auto
    by_cases h10 : ty = go.uint8
    · subst h10
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint8 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h10, ↓reduceIte, decide_false]
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; intro h; cases h
    · ipureintro
      intro _ ii h
      cases h
      simp only [IsIntType, not_or]
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

omit [FfiSemantics ext ffi] in
theorem not_simpleDirective (f : GoString) (x : GoInterface) (args : List GoInterface)
    (h1 : f.head? ≠ some (W8 37))
    (h2 : f.head? ≠ some (W8 115) ∨ ∀ ii, x = interface.ok ii → ii.ty ≠ go.string)
    (h3 : parseIntVerb f = none ∨ ∀ ii, x = interface.ok ii → ¬ IsIntType ii.ty) :
    ¬ SimpleDirective f (x :: args) := by
  cases f with
  | nil => simp [SimpleDirective]
  | cons c f =>
    simp only [SimpleDirective, List.cons.injEq]
    rintro (h | ⟨hc, ii, rest, ⟨rfl, -⟩, hty⟩ | ⟨hp, ii, rest, ⟨rfl, -⟩, hty⟩)
    · exact h1 (by simp [h])
    · rcases h2 with h2 | h2
      · exact h2 (by simp [hc])
      · exact h2 ii rfl hty
    · rcases h3 with h3 | h3
      · rw [h3] at hp; simp at hp
      · exact h3 ii rfl hty

omit [FfiSemantics ext ffi] in
theorem not_simpleDirective_nil (f : GoString) (h : f.head? ≠ some (W8 37)) :
    ¬ SimpleDirective f [] := by
  cases f with
  | nil => simp [SimpleDirective]
  | cons c f =>
    simp only [SimpleDirective]
    rintro (h' | ⟨-, ii, rest, h', -⟩ | ⟨-, ii, rest, h', -⟩)
    · exact h (by simp [h'])
    · cases h'
    · cases h'

/-- The helper `fmt.formatArg` of the model of `Sprintf`: at the `%` at index `i` of `format`, the
output of the directive for the argument `x` and the index after it, if the model formats it. -/
theorem wp_formatArg (format : GoString) (i : w64) (x : GoInterface)
    (Hi : 0 ≤ sint.Z i ∧ sint.Z i < (format.length : Int))
    (Hx : ∀ ii, x = interface.ok ii → ArgWf ii) :
    {{ (True : IProp GF) }}
      (App (App (App (Val formatArg) (Val #format)) (Val #i)) (Val #x))
    {{ (s : GoString) (next : w64) (ok : Bool), RET (PairV (PairV #s #next) #ok);
        ⌜ok = true → sint.Z i < sint.Z next ∧ sint.Z next ≤ (format.length : Int) ∧
          ∀ args r, SprintfOut (format.drop (sint.nat next)) args r →
            SprintfOut (W8 37 :: format.drop (sint.nat i + 1)) (x :: args) (s ++ r)⌝ ∗
        ⌜ok = false → (format.drop (sint.nat i + 1)).head? ≠ some (W8 37) →
          ∀ args, ¬ SimpleDirective (format.drop (sint.nat i + 1)) (x :: args)⌝ }} := by
  iintro %Φ - HΦ
  unfold formatArg
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · have Hlt : sint.nat i + 1 < format.length := by word
    have Hdrop2 : sint.nat (i + W64 2) = sint.nat i + 2 := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat i + 1]? = some c ∧
        format.drop (sint.nat i + 1) = c :: format.drop (sint.nat i + 2) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    have Hidx : format[sint.nat (i + W64 1)]? = some c := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]; exact Hc
    rw [Hidx]
    wp_auto
    by_cases hs : c = W8 115
    · -- `%s`
      subst hs
      simp only [_root_.decide_true]
      have Hnp : parseIntVerb (format.drop (sint.nat i + 1)) = none := by
        rw [Hdrop]; simp [parseIntVerb]
      cases x with
      | nil =>
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _ hp args
          exact not_simpleDirective _ _ _ hp (.inr (fun ii h => by cases h)) (.inl Hnp)
      | ok ii =>
        by_cases hty : ii.ty = go.string
        · obtain ⟨sx, hv⟩ := (Hx ii rfl).1 hty
          obtain ⟨ty, v⟩ := ii
          simp only at hty hv
          subst hty hv
          wp_auto
          iapply HΦ
          isplitl []
          · ipureintro; intro _
            refine ⟨by word, by word, fun args r hr => ?_⟩
            rw [Hdrop2] at hr
            rw [Hdrop]
            exact SprintfOut.str sx _ _ _ hr
          · ipureintro; intro h; cases h
        · wp_auto
          simp only [hty, ↓reduceIte, decide_false]
          wp_auto
          iapply HΦ
          isplitl []
          · ipureintro; intro h; cases h
          · ipureintro; intro _ hp args
            exact not_simpleDirective _ _ _ hp
              (.inr (fun ii' h => by cases h; exact hty)) (.inl Hnp)
    · rw [decide_eq_false hs]
      wp_auto
      have Hns : (format.drop (sint.nat i + 1)).head? ≠ some (W8 115) := by
        rw [Hdrop]; simpa using hs
      wp_apply wp_intVerb format i Hi as %w %next %ok ⟨%Hv1, %Hv2⟩
      cases ok
      · wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _ hp args
          exact not_simpleDirective _ _ _ hp (.inl Hns) (.inl (Hv2 rfl))
      · obtain ⟨Hparse, Hw1, Hw2, Hn1, Hn2⟩ := Hv1 rfl
        wp_auto
        wp_apply wp_intArg x Hx as %neg %mag %ok2 ⟨%Ha1, %Ha2⟩
        cases ok2
        · wp_auto
          iapply HΦ
          isplitl []
          · ipureintro; intro h; cases h
          · ipureintro; intro _ hp args
            exact not_simpleDirective _ _ _ hp (.inl Hns) (.inr (Ha2 rfl))
        · obtain ⟨ii, rfl, Hval, Hmag⟩ := Ha1 rfl
          wp_auto
          wp_apply wp_formatInt neg mag w Hmag ⟨Hw1, Hw2⟩
          iapply HΦ
          isplitl []
          · ipureintro; intro _
            exact ⟨Hn1, Hn2, fun args r hr => SprintfOut.int _ _ _ _ _ _ _ Hparse Hval hr⟩
          · ipureintro; intro h; cases h
  · (try wp_auto)
    have Hns : (format.drop (sint.nat i + 1)).head? ≠ some (W8 115) := by
      rw [List.drop_eq_nil_of_le (by word)]; simp
    wp_apply wp_intVerb format i Hi as %w %next %ok ⟨%Hv1, %Hv2⟩
    cases ok
    · wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro h; cases h
      · ipureintro; intro _ hp args
        exact not_simpleDirective _ _ _ hp (.inl Hns) (.inl (Hv2 rfl))
    · obtain ⟨Hparse, Hw1, Hw2, Hn1, Hn2⟩ := Hv1 rfl
      wp_auto
      wp_apply wp_intArg x Hx as %neg %mag %ok2 ⟨%Ha1, %Ha2⟩
      cases ok2
      · wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _ hp args
          exact not_simpleDirective _ _ _ hp (.inl Hns) (.inr (Ha2 rfl))
      · obtain ⟨ii, rfl, Hval, Hmag⟩ := Ha1 rfl
        wp_auto
        wp_apply wp_formatInt neg mag w Hmag ⟨Hw1, Hw2⟩
        iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨Hn1, Hn2, fun args r hr => SprintfOut.int _ _ _ _ _ _ _ Hparse Hval hr⟩
        · ipureintro; intro h; cases h

end wps

end fmt

end Perennial
