/-
The proof of `slices.Repeat`.
-/
module

public import Perennial.Spec.slices.Repeat
public import Perennial.Spec.math.bits.Mul

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

theorem slices.repeat_length {V : Type} (xs : List V) (c : Nat) :
    (List.replicate c xs).flatten.length = c * xs.length := by
  simp [List.length_flatten]

theorem slices.repeat_take_of_le {V : Type} (xs : List V) (j c m : Nat) (hj : j ≤ c)
    (hm : m ≤ j * xs.length) :
    (List.replicate c xs).flatten.take m = (List.replicate j xs).flatten.take m := by
  rw [show c = j + (c - j) by omega, ← List.replicate_append_replicate, List.flatten_append,
    List.take_append_of_le_length (by rw [slices.repeat_length]; exact hm)]

theorem slices.repeat_drop {V : Type} (xs : List V) (k c : Nat) (hk : k ≤ c) :
    (List.replicate c xs).flatten.drop (k * xs.length) = (List.replicate (c - k) xs).flatten := by
  rw [show c = k + (c - k) by omega, ← List.replicate_append_replicate, List.flatten_append,
    List.drop_left' (slices.repeat_length xs k), Nat.add_sub_cancel_left]

theorem slices.repeat_take_step {V : Type} (xs : List V) (k c m : Nat) (hk : k ≤ c)
    (hm : m ≤ k * xs.length) (hnm : k * xs.length + m ≤ c * xs.length) :
    (List.replicate c xs).flatten.take (k * xs.length) ++
        ((List.replicate c xs).flatten.take (k * xs.length)).take m =
      (List.replicate c xs).flatten.take (k * xs.length + m) := by
  rw [List.take_add, List.take_take, Nat.min_eq_left hm, slices.repeat_drop xs k c hk]
  congr 1
  have hm' : m ≤ (c - k) * xs.length := by rw [Nat.sub_mul]; omega
  by_cases h : k ≤ c - k
  · rw [slices.repeat_take_of_le xs k c m hk hm,
      slices.repeat_take_of_le xs k (c - k) m h hm]
  · rw [slices.repeat_take_of_le xs (c - k) c m (by omega) hm',
      slices.repeat_take_of_le xs (c - k) (c - k) m (Nat.le_refl _) hm']

/-- One round of `Repeat`'s loop, `n += copy(newslice[n:], newslice[:n])` with `n = k * len(x)`: the
first `n + m` elements of the result are in place (`m = min(L - n, n)`, `L = count * len(x)`). -/
theorem slices.repeat_copy_step {V : Type} (xs : List V) (z : V) (k c : Nat) (hk : k ≤ c) :
    ((List.replicate c xs).flatten.take (k * xs.length) ++
        List.replicate (c * xs.length - k * xs.length) z).take (k * xs.length) ++
      ((subslice 0 (k * xs.length) ((List.replicate c xs).flatten.take (k * xs.length) ++
          List.replicate (c * xs.length - k * xs.length) z)).take (c * xs.length - k * xs.length) ++
        (subslice (k * xs.length) (c * xs.length) ((List.replicate c xs).flatten.take (k * xs.length) ++
          List.replicate (c * xs.length - k * xs.length) z)).drop (k * xs.length - 0)) ++
      ((List.replicate c xs).flatten.take (k * xs.length) ++
        List.replicate (c * xs.length - k * xs.length) z).drop (c * xs.length) =
    (List.replicate c xs).flatten.take (k * xs.length + min (c * xs.length - k * xs.length) (k * xs.length)) ++
      List.replicate (c * xs.length - (k * xs.length + min (c * xs.length - k * xs.length) (k * xs.length))) z := by
  have hkp : k * xs.length ≤ c * xs.length := Nat.mul_le_mul_right _ hk
  have hlen : ((List.replicate c xs).flatten.take (k * xs.length)).length = k * xs.length := by
    rw [List.length_take, slices.repeat_length]; omega
  have hstep := slices.repeat_take_step xs k c (min (c * xs.length - k * xs.length) (k * xs.length))
    hk (Nat.min_le_right _ _) (by omega)
  generalize hN : k * xs.length = N at *
  generalize hL : c * xs.length = L at *
  rw [← hstep]
  generalize (List.replicate c xs).flatten.take N = r at *
  simp only [subslice, Nat.sub_zero, List.drop_zero, List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
    List.take_of_length_le (Nat.le_of_eq hlen), List.take_of_length_le (show (r ++ List.replicate (L - N) z).length ≤ L by simp; omega),
    List.drop_left' hlen, List.drop_replicate, List.drop_of_length_le (show (r ++ List.replicate (L - N) z).length ≤ L by simp; omega),
    List.append_nil, List.append_assoc]
  congr 2
  · rw [← List.take_take, List.take_of_length_le (show r.length ≤ N by omega)]
  · congr 1; omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.Repeat.wp_proof
    (wp_Mul : math.bits.Mul.spec (GF := GF) (hG := hG)) :
    slices.Repeat.spec (GF := GF) (hG := hG) := by
  intro V _ _ Et _ S _ x dq xs count Hcount Hbound
  wp_start as Hx
  ihave %Hxlen := ownSlice_len _ _ _ $$ Hx
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z count < sint.Z (W64 0) by word)]
  wp_auto
  wp_apply wp_Mul
  have hxu : uint.Z x.len = xs.length := by word
  have hcu : uint.Z count = sint.Z count := by word
  have hprod : uint.Z x.len * uint.Z count < 2 ^ 63 := by rw [hxu, hcu]; exact Hbound
  have hprod0 : 0 ≤ uint.Z x.len * uint.Z count :=
    Int.mul_nonneg (by word) (by word)
  have hhi : ¬ uint.Z (W64 0) < uint.Z (W64 (uint.Z x.len * uint.Z count / 2 ^ 64)) := by
    rw [Int.ediv_eq_zero_of_lt hprod0 (by omega)]; word
  have hlo : uint.Z (x.len * count) = uint.Z x.len * uint.Z count := by
    have h := hprod
    simp only [uint.Z, BitVec.toNat_mul] at h ⊢
    rw [← Int.natCast_mul] at h ⊢
    generalize x.len.toNat * count.toNat = P at *
    omega
  rw [decide_eq_false hhi]
  wp_auto
  rw [decide_eq_false (show ¬ uint.Z (W64 9223372036854775807) < uint.Z (x.len * count) by
    rw [hlo]; word)]
  wp_auto
  have hL := slices.repeat_length xs (sint.nat count)
  have hLz : sint.Z (x.len * count) = ((sint.nat count * xs.length : Nat) : Int) := by
    have h1 : uint.Z (x.len * count) = ((sint.nat count * xs.length : Nat) : Int) := by
      rw [hlo, hxu, hcu, Int.natCast_mul, Int.toNat_of_nonneg Hcount, Int.mul_comm]
    have h2 : uint.Z (x.len * count) < 2 ^ 63 := by rw [hlo]; exact hprod
    word
  wp_apply wp_slice_make2 (V := V) (x.len * count) $$ [] as %ns ⟨Hns, Hcap⟩
  · ipureintro; word
  wp_apply wp_slice_copy_int ns _ x xs dq $$ [Hns Hx] as %n0 ⟨%Hn0Z, Hns, Hx⟩
  · iframe
  have hnsL : sint.nat (x.len * count) = sint.nat count * xs.length := by
    simp only [sint.nat, hLz]; rfl
  simp only [List.length_replicate, List.drop_replicate, hnsL] at Hn0Z ⊢
  have Hn0pos : 0 ≤ sint.Z n0 := by rw [Hn0Z]; omega
  have Hn0 : sint.nat n0 = min (sint.nat count * xs.length) xs.length := by
    simp only [sint.nat, Hn0Z]; omega
  ihave %Hnslen := ownSlice_len _ _ _ $$ Hns
  simp only [List.length_append, List.length_take, List.length_replicate] at Hnslen
  -- the loop: `ns` holds the first `n` elements of the result, `n` a whole number `k` of copies
  -- (at least one once the result is not empty)
  have hbnd : sint.nat count * xs.length < 2 ^ 63 := by
    have hc : ((sint.nat count : Nat) : Int) = sint.Z count := Int.toNat_of_nonneg Hcount
    have : ((sint.nat count * xs.length : Nat) : Int) < 2 ^ 63 := by
      rw [Int.natCast_mul, hc, Int.mul_comm]; exact Hbound
    omega
  ihave IH : iprop(∃ (n : w64) (k : Nat), "n" ∷ n_ptr ↦ n ∗ "newslice" ∷ newslice_ptr ↦ ns ∗
      "Hns" ∷ ns ↦* ((List.replicate (sint.nat count) xs).flatten.take (sint.nat n) ++
        List.replicate (sint.nat count * xs.length - sint.nat n) (zero_val V)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n = k * xs.length ∧ k ≤ sint.nat count ∧
        (0 < k ∨ sint.nat count = 0)⌝) $$ [n newslice Hns]
  · by_cases hc0 : sint.nat count = 0
    · iexists n0, 0
      have hn0 : sint.nat n0 = 0 := by rw [Hn0, hc0]; simp
      rw [hn0, hc0]
      simp only [Nat.zero_mul, List.replicate_zero, List.flatten_nil, List.take_nil, List.take_zero,
        Nat.zero_sub, List.nil_append] at Hn0 ⊢
      iframe
      ipureintro
      refine ⟨Hn0pos, by simp, by simp, by simp⟩
    · iexists n0, 1
      have hle : xs.length ≤ sint.nat count * xs.length :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc0)
      have hn0 : sint.nat n0 = xs.length := by rw [Hn0, Nat.min_eq_right hle]
      have htake : (List.replicate (sint.nat count) xs).flatten.take xs.length = xs := by
        rw [slices.repeat_take_of_le xs 1 _ xs.length (Nat.pos_of_ne_zero hc0) (by simp)]
        simp
      rw [hn0, htake, List.take_of_length_le hle]
      iframe
      ipureintro
      refine ⟨Hn0pos, by simp, Nat.pos_of_ne_zero hc0, Or.inl Nat.one_pos⟩
  wp_for IH
  wp_if_destruct
  · ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
    ihave %Hnslen' := ownSlice_len _ _ _ $$ Hns
    have h00 : sint.Z (W64 0) = 0 := rfl
    have Hif' : sint.Z n < sint.Z ns.len := by simpa using Hif
    have hnl : sint.Z n ≤ sint.Z ns.len := Int.le_of_lt Hif'
    have hnc : sint.Z n ≤ sint.Z ns.cap := Int.le_trans hnl Hcapwf.2
    rw [ite_eq_left ⟨Hn.1, hnl, Hcapwf.2⟩]
    wp_auto
    rw [ite_eq_left ⟨by rw [h00]; exact Int.le_refl _, by rw [h00]; exact Hn.1, hnc⟩]
    wp_auto
    wp_apply wp_slice_copy_within ns _ n ns.len (W64 0) n ⟨Hn.1, hnl, Int.le_refl _⟩
      ⟨by rw [h00]; exact Int.le_refl _, by rw [h00]; exact Hn.1, hnl⟩ $$ [Hns] as %cnt ⟨%Hcnt, Hns⟩
    · iframe
    obtain ⟨Hn1, hN, hk, hk0⟩ := Hn
    have hkp : k * xs.length ≤ sint.nat count * xs.length := Nat.mul_le_mul_right _ hk
    have hnsl : sint.nat ns.len = sint.nat count * xs.length := by
      rw [← Hnslen'.1, List.length_append, List.length_take, List.length_replicate,
        slices.repeat_length]; omega
    rw [hnsl, show sint.nat (W64 0) = 0 from rfl, hN] at Hcnt
    rw [hnsl, hN, slices.repeat_copy_step xs _ k _ hk]
    have hlt : k * xs.length < sint.nat count * xs.length := by
      rw [← hN, ← hnsl]; have h1 := Hn1; have h2 := Hif'
      simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
    have hp : 0 < xs.length := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hlt; simp at hlt)
    have hk1 : 0 < k := by
      rcases hk0 with h | h
      · exact h
      · rw [h] at hlt; simp at hlt
    have hN1 : xs.length ≤ k * xs.length := Nat.le_mul_of_pos_left _ hk1
    have hsumZ : sint.Z (n + cnt) =
        ((k * xs.length + min (sint.nat count * xs.length - k * xs.length) (k * xs.length) : Nat) : Int) := by
      generalize sint.nat count * xs.length = L at *
      generalize k * xs.length = N at *
      have hm : 1 ≤ min (L - N) N := by omega
      word
    have hsum : sint.nat (n + cnt) =
        k * xs.length + min (sint.nat count * xs.length - k * xs.length) (k * xs.length) := by
      simp only [sint.nat, hsumZ]; rfl
    wp_for_post
    iframe
    iexists (n + cnt),
      (if sint.nat count * xs.length - k * xs.length ≤ k * xs.length then sint.nat count else 2 * k)
    rw [hsum]
    iframe
    ipureintro
    refine ⟨by rw [hsumZ]; omega, ?_, ?_, ?_⟩
    · split
      · rename_i h; rw [Nat.min_eq_left h]; omega
      · rename_i h; rw [Nat.min_eq_right (by omega), Nat.mul_assoc]; omega
    · split
      · exact Nat.le_refl _
      · rename_i h
        have : 2 * k * xs.length < sint.nat count * xs.length := by rw [Nat.mul_assoc]; omega
        exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right this)
    · left; split <;> omega
  · -- the loop is done: `n` is the length of the result
    ihave %Hnslen' := ownSlice_len _ _ _ $$ Hns
    obtain ⟨Hn1, hN, hk, hk0⟩ := Hn
    have hkp : k * xs.length ≤ sint.nat count * xs.length := Nat.mul_le_mul_right _ hk
    have hnsl : sint.nat ns.len = sint.nat count * xs.length := by
      rw [← Hnslen'.1, List.length_append, List.length_take, List.length_replicate,
        slices.repeat_length]; omega
    have hnL : sint.nat n = sint.nat count * xs.length := by
      have Hif' : ¬ sint.Z n < sint.Z ns.len := by simpa using Hif
      have h1 := Hn1; have h3 := hnsl; have h4 := hkp
      simp only [sint.nat, sint.Z] at hN Hif' h1 h3 h4 ⊢; omega
    rw [hnL, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.take_of_length_le (Nat.le_of_eq hL)]
    iapply HΦ
    iframe

end proof

end Perennial
