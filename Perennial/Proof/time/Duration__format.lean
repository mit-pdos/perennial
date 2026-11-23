/-
The proof of `time.Duration.format`.
-/
module

public import Perennial.Spec.time.Duration__format
public import Perennial.Spec.time.fmtFrac
public import Perennial.Spec.time.fmtInt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- A byte stored at index `i` of the array at `buf`, owned as the slice of the whole array. -/
theorem time.wp_store_buf (buf : Loc) (ys : List w8) (i : Int) (c : w8) (hi : 0 ≤ i ∧ i < 32)
    (hl : ys.length = 32) :
    {{ (slice.mk buf (W64 32) (W64 32) ↦* ys : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.byte))) (Val (PairV #(arrayIndexRef w8 i buf) #c)))
    {{ RET #(); slice.mk buf (W64 32) (W64 32) ↦* ys.set i.toNat c }} := by
  iintro %Φ Hb HΦ
  obtain ⟨v0, hv0⟩ : ∃ v, ys[i.toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases ownSlice_elem_acc (V := w8) i v0 _ _ _ hi.1 hv0 $$ Hb with ⟨H0, Hb⟩
  rw [show arrayIndexRef w8 i buf = sliceIndexRef w8 i (slice.mk buf (W64 32) (W64 32)) from rfl]
  iapply (IntoValTyped.wp_store (t := go.byte) _ v0 c) $$ H0
  inext
  iintro H0
  iapply HΦ
  iapply Hb $$ H0

/-- The prefix `buf[:w]` of the array at `buf`, owned as the slice `S` of the whole array, split off
`S` for a callee and joined back: what the callee keeps of its length is all `S` needs. -/
theorem time.buf_prefix_split (buf : Loc) (ys : List w8) (w : w64) (hl : ys.length = 32)
    (hw : 0 ≤ sint.Z w ∧ sint.Z w ≤ 32) :
    (slice.mk buf (W64 32) (W64 32) ↦* ys : IProp GF) ⊢
      slice.slice (slice.mk buf (W64 32) (W64 32)) w8 (W64 0) w ↦* ys.take (sint.nat w) ∗
        (∀ zs : List w8, ⌜zs.length = sint.nat w⌝ -∗
          slice.slice (slice.mk buf (W64 32) (W64 32)) w8 (W64 0) w ↦* zs -∗
          ∃ ys' : List w8, slice.mk buf (W64 32) (W64 32) ↦* ys' ∗ ⌜ys'.length = 32⌝) := by
  iintro Hb
  ihave ⟨Hpre, Hsuf⟩ := (ownSlice_split_all (V := w8) w (slice.mk buf (W64 32) (W64 32)) _ ys
    ⟨hw.1, by show sint.Z w ≤ sint.Z (W64 32); rw [show sint.Z (W64 32) = 32 from rfl]; exact hw.2⟩).1 $$ Hb
  iframe Hpre
  iintro %zs %hzs Hz
  iexists (zs ++ ys.drop (sint.nat w))
  isplitl
  · iapply (ownSlice_split_all (V := w8) w (slice.mk buf (W64 32) (W64 32)) _ _
      ⟨hw.1, by show sint.Z w ≤ sint.Z (W64 32); rw [show sint.Z (W64 32) = 32 from rfl]; exact hw.2⟩).2
    rw [List.take_left' hzs, List.drop_left' hzs]
    iframe
  · ipureintro; simp [hzs, hl]; word

theorem time.wp_fmtFrac_buf (wp_fmtFrac : time.fmtFrac.spec (GF := GF) (hG := hG)) (buf : Loc)
    (ys : List w8) (w u prec : w64) (hl : ys.length = 32)
    (hw : sint.Z prec < sint.Z w ∧ sint.Z w ≤ 32) (hp : 0 ≤ sint.Z prec) :
    {{ (slice.mk buf (W64 32) (W64 32) ↦* ys : IProp GF) }}
      (App (App (App (Val (@! time.fmtFrac))
        (Val #(slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) buf) (w - W64 0) (W64 32 - W64 0))))
        (Val #u)) (Val #prec))
    {{ (nw nv : w64), RET (PairV #nw #nv);
        ⌜sint.Z w - sint.Z prec - 1 ≤ sint.Z nw ∧ sint.Z nw ≤ sint.Z w ∧
          uint.Z nv = uint.Z u / 10 ^ sint.nat prec⌝ ∗
        ∃ ys' : List w8, slice.mk buf (W64 32) (W64 32) ↦* ys' ∗ ⌜ys'.length = 32⌝ }} := by
  iintro %Φ Hb HΦ
  rw [show slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) buf) (w - W64 0) (W64 32 - W64 0) =
    slice.slice (slice.mk buf (W64 32) (W64 32)) w8 (W64 0) w from rfl]
  ihave ⟨Hpre, Hback⟩ := time.buf_prefix_split buf ys w hl ⟨by omega, hw.2⟩ $$ Hb
  have hlt : (ys.take (sint.nat w)).length = sint.nat w := by simp; word
  iapply wp_fmtFrac _ _ u prec hp (by rw [hlt]; word) $$ Hpre
  inext
  iintro %nw %nv ⟨%Hn, %zs, Hz, %Hzs⟩
  iapply HΦ
  rw [hlt] at Hn
  isplitr
  · ipureintro; refine ⟨by word, by word, Hn.2.2⟩
  iapply Hback $$ %zs %(by rw [Hzs, hlt]) Hz

theorem time.wp_fmtInt_buf (wp_fmtInt : time.fmtInt.spec (GF := GF) (hG := hG)) (buf : Loc)
    (ys : List w8) (w u : w64) (k : Nat) (hl : ys.length = 32) (hk1 : 1 ≤ k)
    (hw : k ≤ sint.Z w ∧ sint.Z w ≤ 32) (hu : uint.Z u < 10 ^ k) :
    {{ (slice.mk buf (W64 32) (W64 32) ↦* ys : IProp GF) }}
      (App (App (Val (@! time.fmtInt))
        (Val #(slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) buf) (w - W64 0) (W64 32 - W64 0))))
        (Val #u))
    {{ (nw : w64), RET #nw; ⌜sint.Z w - k ≤ sint.Z nw ∧ sint.Z nw ≤ sint.Z w⌝ ∗
        ∃ ys' : List w8, slice.mk buf (W64 32) (W64 32) ↦* ys' ∗ ⌜ys'.length = 32⌝ }} := by
  iintro %Φ Hb HΦ
  rw [show slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) buf) (w - W64 0) (W64 32 - W64 0) =
    slice.slice (slice.mk buf (W64 32) (W64 32)) w8 (W64 0) w from rfl]
  ihave ⟨Hpre, Hback⟩ := time.buf_prefix_split buf ys w hl ⟨by omega, hw.2⟩ $$ Hb
  have hlt : (ys.take (sint.nat w)).length = sint.nat w := by simp; word
  iapply wp_fmtInt _ _ u k hk1 (by rw [hlt]; word) hu $$ Hpre
  inext
  iintro %nw ⟨%Hn, %zs, Hz, %Hzs⟩
  iapply HΦ
  rw [hlt] at Hn
  isplitr
  · ipureintro; refine ⟨by word, by word⟩
  iapply Hback $$ %zs %(by rw [Hzs, hlt]) Hz

theorem time.Duration.format.wp_proof
    (wp_fmtFrac : time.fmtFrac.spec (GF := GF) (hG := hG))
    (wp_fmtInt : time.fmtInt.spec (GF := GF) (hG := hG)) :
    time.Duration.format.spec (GF := GF) (hG := hG) := by
  intro d buf xs hxs
  haveI : go.NotInterface go.int64 := ⟨by simp [go.int64]⟩
  wp_start as Hb
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_join iprop(∃ U : w64, "u" ∷ u_ptr ↦ U) with [u] as ⟨%U, u⟩
  by_cases hU0 : U = W64 0
  · subst hU0
    wp_if_destruct
    · wp_apply time.wp_store_buf buf xs _ _ (by decide) hxs $$ Hb as Hb
      wp_apply time.wp_store_buf buf _ _ _ (by decide) (by simp [hxs]) $$ Hb as Hb
      iapply HΦ
      isplitr
      · ipureintro; decide
      iexists _
      iframe Hb
      ipureintro; simp [hxs]
    · exfalso; exact Hif (by decide)
  · wp_if_destruct
    · -- `u < Second`: `s` and a smaller unit
      wp_apply time.wp_store_buf buf xs _ _ (by decide) hxs $$ Hb as Hb
      wp_join iprop(∃ (w p : w64) (ys : List w8), "u" ∷ u_ptr ↦ U ∗ "buf" ∷ buf_ptr ↦ buf ∗
          "w" ∷ w_ptr ↦ w ∗ "prec" ∷ prec_ptr ↦ p ∗
          "Hb" ∷ slice.mk buf (W64 32) (W64 32) ↦* ys ∗
          "%Hj" ∷ ⌜ys.length = 32 ∧ 29 ≤ sint.Z w ∧ sint.Z w ≤ 30 ∧ 0 ≤ sint.Z p ∧ sint.Z p ≤ 6⌝)
        with [u buf w prec Hb] as ⟨%w, %p, %ys, u, buf, w, prec, Hb, %Hj⟩
      · exfalso; exact hU0 (of_decide_eq_true Hif.symm)
      · wp_if_destruct
        · -- nanoseconds
          wp_apply time.wp_store_buf buf _ _ _ (by decide) (by simp [hxs]) $$ Hb as Hb
          wp_join_done
          iexists (W64 32 - W64 1 - W64 1), (W64 0), _
          iframe
          ipureintro; refine ⟨by simp [hxs], by decide, by decide, by decide, by decide⟩
        · wp_if_destruct
          · -- microseconds: `µ` (two bytes) at `w - 1`
            wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
            have hl1 : (xs.set (sint.Z (W64 32 - W64 1)).toNat (W8 115)).length = 32 := by simp [hxs]
            have h29 : sint.nat (W64 32 - W64 1 - W64 1 - W64 1) = 29 := by decide
            have hb29 : 0 ≤ sint.Z (W64 32 - W64 1 - W64 1 - W64 1) ∧
                sint.Z (W64 32 - W64 1 - W64 1 - W64 1) ≤ sint.Z (slice.mk buf (W64 32) (W64 32)).len :=
              ⟨by decide, by show sint.Z (W64 32 - W64 1 - W64 1 - W64 1) ≤ sint.Z (W64 32); decide⟩
            ihave ⟨Hpre, Hsuf⟩ := (ownSlice_split_all (V := w8) (W64 32 - W64 1 - W64 1 - W64 1)
              (slice.mk buf (W64 32) (W64 32)) _ _ hb29).1 $$ Hb
            rw [show slice.mk (arrayIndexRef w8 (sint.Z (W64 32 - W64 1 - W64 1 - W64 1)) buf)
                (W64 32 - (W64 32 - W64 1 - W64 1 - W64 1)) (W64 32 - (W64 32 - W64 1 - W64 1 - W64 1)) =
              slice.slice (slice.mk buf (W64 32) (W64 32)) w8 (W64 32 - W64 1 - W64 1 - W64 1)
                (slice.mk buf (W64 32) (W64 32)).len from rfl]
            wp_apply wp_slice_copy _ _ sl _ (DFrac.own 1) $$ [$Hsuf $Hsl] as %n ⟨%Hn, Hsuf, Hsl⟩
            wp_join_done
            iexists (W64 32 - W64 1 - W64 1 - W64 1), (W64 3), _
            iframe
            have htl : (List.take (sint.nat (W64 32 - W64 1 - W64 1 - W64 1))
                (xs.set (sint.Z (W64 32 - W64 1)).toNat (W8 115))).length =
                sint.nat (W64 32 - W64 1 - W64 1 - W64 1) := by
              rw [List.length_take, hl1, h29]; decide
            isplitl [Hpre Hsuf]
            · iapply (ownSlice_split_all (V := w8) (W64 32 - W64 1 - W64 1 - W64 1)
                (slice.mk buf (W64 32) (W64 32)) _ (List.take (sint.nat (W64 32 - W64 1 - W64 1 - W64 1))
                  (xs.set (sint.Z (W64 32 - W64 1)).toNat (W8 115)) ++ _) hb29).2
              rw [List.take_left' htl, List.drop_left' htl]
              iframe
            · ipureintro
              refine ⟨?_, by decide, by decide, by decide, by decide⟩
              simp only [List.length_append, List.length_take, List.length_drop, hl1, h29]
              simp
          · -- milliseconds
            wp_apply time.wp_store_buf buf _ _ _ (by decide) (by simp [hxs]) $$ Hb as Hb
            wp_join_done
            iexists (W64 32 - W64 1 - W64 1), (W64 6), _
            iframe
            ipureintro; refine ⟨by simp [hxs], by decide, by decide, by decide, by decide⟩
      -- the fraction and the integer part
      obtain ⟨hys, hw29, hw30, hp0, hp6⟩ := Hj
      rw [if_pos ⟨by decide, by word, by word⟩]
      wp_auto
      wp_apply time.wp_fmtFrac_buf wp_fmtFrac buf ys w U p hys ⟨by word, by word⟩ hp0 $$ Hb
        as %nw %nv ⟨%Hn, %ys1, Hb, %hys1⟩
      rw [if_pos ⟨by decide, by word, by word⟩]
      wp_auto
      have hnv : uint.Z nv < 10 ^ 9 := by
        rw [Hn.2.2]
        have : uint.Z U < 10 ^ 9 := by word
        exact Int.lt_of_le_of_lt (Int.ediv_le_self _ (by word)) this
      wp_apply time.wp_fmtInt_buf wp_fmtInt buf ys1 nw nv 9 hys1 (by decide) ⟨by word, by word⟩ hnv $$ Hb
        as %nw2 ⟨%Hn2, %ys2, Hb, %hys2⟩
      wp_if_destruct
      · rw [if_pos ⟨by word, by word⟩]
        wp_apply time.wp_store_buf buf ys2 _ _ ⟨by word, by word⟩ hys2 $$ Hb as Hb
        iapply HΦ
        isplitr
        · ipureintro; constructor <;> word
        iexists _
        iframe Hb
        ipureintro; simp [hys2]
      · iapply HΦ
        isplitr
        · ipureintro; constructor <;> word
        iexists _
        iframe Hb
        ipureintro; exact hys2
    · -- `u ≥ Second`: `s`, the fraction, seconds, minutes, hours
      wp_apply time.wp_store_buf buf xs _ _ (by decide) hxs $$ Hb as Hb
      have hl1 : (xs.set (sint.Z (W64 32 - W64 1)).toNat (W8 115)).length = 32 := by simp [hxs]
      wp_apply time.wp_fmtFrac_buf wp_fmtFrac buf _ (W64 32 - W64 1) U (W64 9) hl1 ⟨by decide, by decide⟩
          (by decide) $$ Hb as %nw %nv ⟨%Hn, %ys1, Hb, %hys1⟩
      rw [if_pos ⟨by decide, by word, by word⟩]
      wp_auto
      wp_apply time.wp_fmtInt_buf wp_fmtInt buf ys1 nw (nv % W64 60) 2 hys1 (by decide)
          ⟨by word, by word⟩ (by word) $$ Hb as %nw2 ⟨%Hn2, %ys2, Hb, %hys2⟩
      have hnv : uint.Z nv < 2 ^ 64 / 10 ^ 9 + 1 := by
        have e9 : (10 : Int) ^ sint.nat (W64 9) = 1000000000 := by decide
        rw [Hn.2.2, e9]
        have : uint.Z U < 2 ^ 64 := by word
        omega
      wp_join iprop(∃ (w : w64) (uc : w64) (ys : List w8), "u" ∷ u_ptr ↦ uc ∗ "buf" ∷ buf_ptr ↦ buf ∗
          "w" ∷ w_ptr ↦ w ∗ "Hb" ∷ slice.mk buf (W64 32) (W64 32) ↦* ys ∗
          "%Hj" ∷ ⌜ys.length = 32 ∧ 8 ≤ sint.Z w ∧ sint.Z w ≤ 32⌝)
        with [u buf w Hb] as ⟨%w, %uc, %ys, u, buf, w, Hb, %Hj⟩
      · -- minutes
        rw [if_pos ⟨by word, by word⟩]
        wp_apply time.wp_store_buf buf ys2 _ _ ⟨by word, by word⟩ hys2 $$ Hb as Hb
        have hl3 : (ys2.set (sint.Z (nw2 - W64 1)).toNat (W8 109)).length = 32 := by simp [hys2]
        rw [if_pos ⟨by decide, by word, by word⟩]
        wp_auto
        wp_apply time.wp_fmtInt_buf wp_fmtInt buf _ (nw2 - W64 1) (nv / W64 60 % W64 60) 2 hl3
            (by decide) ⟨by word, by word⟩ (by word) $$ Hb as %nw3 ⟨%Hn3, %ys3, Hb, %hys3⟩
        wp_if_destruct
        · -- hours
          rw [if_pos ⟨by word, by word⟩]
          wp_apply time.wp_store_buf buf ys3 _ _ ⟨by word, by word⟩ hys3 $$ Hb as Hb
          have hl4 : (ys3.set (sint.Z (nw3 - W64 1)).toNat (W8 104)).length = 32 := by simp [hys3]
          rw [if_pos ⟨by decide, by word, by word⟩]
          wp_auto
          wp_apply time.wp_fmtInt_buf wp_fmtInt buf _ (nw3 - W64 1) (nv / W64 60 / W64 60) 7 hl4
              (by decide) ⟨by word, by word⟩ (by word) $$ Hb as %nw4 ⟨%Hn4, %ys4, Hb, %hys4⟩
          wp_join_done
          iexists nw4, _, ys4
          iframe
          ipureintro; refine ⟨hys4, by word, by word⟩
        · wp_join_done
          iexists nw3, _, ys3
          iframe
          ipureintro; refine ⟨hys3, by word, by word⟩
      · iexists nw2, _, ys2
        iframe
        ipureintro; refine ⟨hys2, by word, by word⟩
      obtain ⟨hys, hw8, hw32⟩ := Hj
      wp_if_destruct
      · rw [if_pos ⟨by word, by word⟩]
        wp_apply time.wp_store_buf buf ys _ _ ⟨by word, by word⟩ hys $$ Hb as Hb
        iapply HΦ
        isplitr
        · ipureintro; constructor <;> word
        iexists _
        iframe Hb
        ipureintro; simp [hys]
      · iapply HΦ
        isplitr
        · ipureintro; constructor <;> word
        iexists _
        iframe Hb
        ipureintro; exact hys


end proof

end Perennial
