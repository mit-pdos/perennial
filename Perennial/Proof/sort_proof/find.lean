/-
Port of `new/proof/sort_proof/find.v`: proof of `sort.Find`.

The specification for `sort.Find` is fairly complicated: it takes a comparison
function (`cmp : Int → Int`) and a number `n`, and it searches for an
`i ∈ [0, n)` such that `cmp i = 0` and `cmp (i-1) > 0`, assuming `cmp` goes from
positive to zero to negative.

See the Rocq file for a discussion of the key ideas: `0 ≤ n` is a precondition,
only the *sign* of `cmp` matters, `cmp` is only called on `[0, n)`, and the
user-provided `cmp` is "adapted" (`adapt_cmp`) so that `cmp (-1) = 1` and
`cmp n ≤ 0`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.sort
import Perennial.GeneratedProof.sort
import Perennial.Proof.sort_proof.sort_init

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

/-! ### Pure facts about comparison functions -/

def signum (cmp_r : Int) : Int :=
  if cmp_r < 0 then -1
  else if cmp_r = 0 then 0
  else 1

theorem signum_n1 : signum (-1) = (-1) := by decide
theorem signum_0 : signum 0 = 0 := by decide
theorem signum_1 : signum 1 = 1 := by decide
theorem signum_idemp (cmp_r : Int) : signum (signum cmp_r) = signum cmp_r := by
  unfold signum; (repeat' split) <;> omega
theorem signum_bound (cmp_r : Int) : -1 ≤ signum cmp_r ∧ signum cmp_r ≤ 1 := by
  unfold signum; (repeat' split) <;> omega

/-- "proper" monotonicity on only `[0, n)` - a sensible precondition for `Find`. -/
def is_mono_cmp (cmp : Int → Int) (n : Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < n → signum (cmp j) ≤ signum (cmp i)

def adapt_cmp (cmp : Int → Int) (n : Int) : Int → Int :=
  fun i => if i < 0 then 1 else
           if n ≤ i then
             if n = 0 then 0 else (-1)
           else cmp i

theorem adapt_cmp_bounded (cmp : Int → Int) (n : Int) :
    ∀ i, 0 ≤ i ∧ i < n → adapt_cmp cmp n i = cmp i := by
  intro i H
  unfold adapt_cmp
  (repeat' split) <;> omega

/-- "internal" monotonicity on `[-1, n]` by extending (adapting) `cmp`. -/
def is_valid_cmp (cmp : Int → Int) (n : Int) : Prop :=
  (∀ i j, -1 ≤ i ∧ i < j ∧ j ≤ n → signum (cmp j) ≤ signum (cmp i)) ∧
  cmp (-1) = 1 ∧
  cmp n ≤ 0

theorem is_valid_cmp_adapted (cmp : Int → Int) (n : Int) :
    0 ≤ n → is_mono_cmp cmp n → is_valid_cmp (adapt_cmp cmp n) n := by
  unfold is_mono_cmp is_valid_cmp
  intro Hnn Hmono
  refine ⟨?_, ?_, ?_⟩
  · intro i j Hij
    by_cases h : 0 ≤ i ∧ j < n
    · rw [adapt_cmp_bounded _ _ i (by omega), adapt_cmp_bounded _ _ j (by omega)]
      exact Hmono i j (by omega)
    · have hi := signum_bound (cmp i)
      have hj := signum_bound (cmp j)
      unfold adapt_cmp
      (repeat' split) <;> (try simp only [signum_n1, signum_0, signum_1]) <;> omega
  · unfold adapt_cmp; (repeat' split) <;> omega
  · unfold adapt_cmp; (repeat' split) <;> omega

theorem shiftr_1_eq_div (x : w64) : x >>> W64 1 = x / (2 : w64) := by
  simp only [W64]; bv_decide

/-- `word`, additionally normalizing constant `%`/`^` after preprocessing (the
`word` tactic leaves `x / (2 % 2 ^ 64)` as an atom for `omega`). -/
macro "word'" : tactic => `(tactic| (
  word_prep
  (try simp only [Nat.reduceMod, Nat.reducePow, Int.reduceMod, Int.reducePow, Int.reduceToNat] at *)
  omega))

theorem find_prefix (cmp : Int → Int) (n i : Int)
    (Hmono : ∀ i j, -1 ≤ i ∧ i < j ∧ j ≤ n →
      signum (adapt_cmp cmp n j) ≤ signum (adapt_cmp cmp n i))
    (Hb : 0 ≤ i ∧ i ≤ n) (Hi_prop : adapt_cmp cmp n (i - 1) > 0) :
    ∀ k, 0 ≤ k ∧ k < i → cmp k > 0 := by
  intro k Hk
  by_cases hk : k = i - 1
  · subst hk; rwa [adapt_cmp_bounded _ _ _ (by omega)] at Hi_prop
  · have Hm := Hmono k (i - 1) (by omega)
    rw [adapt_cmp_bounded _ _ _ (by omega), adapt_cmp_bounded _ _ _ (by omega)] at Hm
    rw [adapt_cmp_bounded _ _ _ (by omega)] at Hi_prop
    unfold signum at Hm
    (repeat' split at Hm) <;> omega

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- The comparison function must implement a pure function over in-bounds
indices, with an arbitrary invariant `I` that it requires and preserves. -/
def cmp_implements (cmp_code : func.t) (cmp : Int → Int) (n : Int) (I : IProp GF) : IProp GF :=
  iprop(∀ (i : w64),
    {{ I ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < n⌝ }}
      (App (Val #cmp_code) (Val #i))
    {{ (r : w64), RET #r; I ∗ ⌜sint.Z r = cmp (sint.Z i)⌝ }})

instance cmp_implements_persistent (cmp_code : func.t) (cmp : Int → Int) (n : Int)
    (I : IProp GF) : Persistent (cmp_implements cmp_code cmp n I) := by
  unfold cmp_implements; infer_instance

theorem cmp_implements_adapt (cmp_code : func.t) (cmp : Int → Int) (n : Int) (I : IProp GF) :
    cmp_implements cmp_code cmp n I ⊢ cmp_implements cmp_code (adapt_cmp cmp n) n I := by
  unfold cmp_implements
  iintro #H %i
  wp_start_folded as ⟨HI, %Hb⟩
  iapply H $$ [HI]
  · iframe HI; ipureintro; exact Hb
  inext
  iintro %r ⟨HI, %Hr⟩
  iapply HΦ
  iframe HI
  ipureintro
  rw [adapt_cmp_bounded _ _ _ Hb]
  exact Hr

theorem wp_Find (n : w64) (cmp_code : func.t) (cmp : Int → Int) (I : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sort ∗
        ⌜0 ≤ sint.Z n⌝ ∗
        cmp_implements cmp_code cmp (sint.Z n) I ∗
        I ∗
        ⌜is_mono_cmp cmp (sint.Z n)⌝ }}
      (App (App (Val (@! Find)) (Val #n)) (Val #cmp_code))
    {{ (i : w64) (found : Bool), RET (PairV #i #found);
        I ∗
        ⌜found = true ↔ sint.Z i < sint.Z n ∧ cmp (sint.Z i) = 0⌝ ∗
        ⌜(∀ i, 0 ≤ i ∧ i < sint.Z n → cmp i > 0) → sint.Z i = sint.Z n⌝ ∗
        ⌜∀ k, 0 ≤ k ∧ k < sint.Z i → cmp k > 0⌝ }} := by
  wp_start as ⟨%Hpos, #Hcmp0, I, %Hvalid⟩
  wp_auto
  ihave #Hcmp := cmp_implements_adapt cmp_code cmp (sint.Z n) I $$ Hcmp0
  iclear Hcmp0
  have Hvalid := is_valid_cmp_adapted cmp (sint.Z n) Hpos Hvalid
  obtain ⟨Hmono, Hneg, Hn⟩ := Hvalid
  unfold cmp_implements
  ihave HI : (∃ (i j : w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜adapt_cmp cmp (sint.Z n) (sint.Z i - 1) > 0⌝ ∗
      "%Hj_prop" ∷ ⌜adapt_cmp cmp (sint.Z n) (sint.Z j) ≤ 0⌝ : IProp GF) $$ [i j I]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, Hn⟩
    rw [show sint.Z (W64 0) - 1 = -1 by decide, Hneg]; decide
  wp_for HI
  wp_if_destruct
  · have Hj : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j := by
      rw [shiftr_1_eq_div]; word'
    wp_apply Hcmp $$ [I] with %r ⟨I, %Hcmp_result⟩
    · iframe I; ipureintro; omega
    generalize (i + j) >>> W64 1 = h at Hj Hcmp_result ⊢
    wp_if_destruct
    · -- cmp(h) > 0, so i = h + 1
      wp_for_post
      iframe
      iexists (h + W64 1), j
      iframe
      ipureintro
      refine ⟨by word, ?_, Hj_prop⟩
      have : sint.Z (h + W64 1) - 1 = sint.Z h := by word
      rw [this, ← Hcmp_result]; word
    · -- cmp(h) ≤ 0, so j = h
      wp_for_post
      iframe
      iexists i, h
      iframe
      ipureintro
      refine ⟨by word, Hi_prop, ?_⟩
      rw [← Hcmp_result]; word
  · have Hij : sint.Z i = sint.Z j := by omega
    wp_if_destruct
    · wp_apply Hcmp $$ [I] with %r ⟨I, %Hr⟩
      · iframe I; ipureintro; omega
      iapply HΦ
      iframe I
      ipureintro
      rw [adapt_cmp_bounded _ _ _ (by omega)] at Hr
      refine ⟨?_, ?_, find_prefix cmp _ _ Hmono (by omega) Hi_prop⟩
      · rw [decide_eq_true_iff]
        constructor
        · intro h; subst h; refine ⟨Hif, ?_⟩; rw [← Hr]; decide
        · intro ⟨_, h⟩; rw [h] at Hr; word
      · intro H
        have := H (sint.Z i) (by omega)
        rw [← Hij, adapt_cmp_bounded _ _ _ (by omega)] at Hj_prop
        omega
    · iapply HΦ
      iframe I
      ipureintro
      refine ⟨by simp only [Bool.false_eq_true, false_iff]; omega, fun _ => by omega,
        find_prefix cmp _ _ Hmono (by omega) Hi_prop⟩

end proof

/-- Direct translation of the specification text. However, this formulation
seems hard to work with for the common case of a monotonic comparison function,
as you'd get for a sorted list. -/
def real_valid_cmp (cmp : Int → Int) (n : Int) : Prop :=
  ∃ start end_,
    (0 ≤ start ∧ start ≤ end_ ∧ end_ < n) ∧
    (∀ i, 0 ≤ i ∧ i < start → cmp i > 0) ∧
    (∀ i, start ≤ i ∧ i < end_ → cmp i = 0) ∧
    (∀ i, end_ ≤ i ∧ i < n → cmp i < 0)

set_option linter.deprecated false in
theorem real_to_internal_cmp (cmp : Int → Int) (n : Int) :
    0 ≤ n → real_valid_cmp cmp n → is_valid_cmp (adapt_cmp cmp n) n := by
  intro Hnn ⟨start, end_, Hord, Hstart, Hmiddle, Hend⟩
  -- the sign of `adapt_cmp cmp n i` on `[-1, n]`, by region
  have hs : ∀ i, -1 ≤ i ∧ i ≤ n → signum (adapt_cmp cmp n i) =
      if i < start then 1 else if i < end_ then 0 else -1 := by
    intro i Hi
    unfold adapt_cmp
    by_cases h0 : i < 0
    · simp only [h0, ↓reduceIte, signum_1]; rw [if_pos (by omega)]
    by_cases hn : n ≤ i
    · simp only [h0, hn, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; decide
    simp only [h0, hn, ↓reduceIte]
    by_cases h1 : i < start
    · have := Hstart i (by omega); simp only [h1, ↓reduceIte]; unfold signum
      rw [if_neg (by omega), if_neg (by omega)]
    by_cases h2 : i < end_
    · have := Hmiddle i (by omega); simp only [h1, h2, ↓reduceIte, this]; decide
    · have := Hend i (by omega); simp only [h1, h2, ↓reduceIte]; unfold signum
      rw [if_pos this]
  refine ⟨?_, ?_, ?_⟩
  · intro i j Hij
    rw [hs i (by omega), hs j (by omega)]
    (repeat' split) <;> omega
  · unfold adapt_cmp; simp
  · unfold adapt_cmp
    simp only [show ¬ n < 0 by omega, Int.le_refl, ↓reduceIte]
    split <;> omega

end sort

end Perennial
end
