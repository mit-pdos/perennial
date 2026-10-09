/-
Specs of
`siftDownCmpFunc` and `heapSortCmpFunc`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.slices
public import Perennial.GeneratedProof.slices
public import Perennial.Proof.slices_proof.slices_init
public import Perennial.Proof.slices_proof.pdqSort.sort_basics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

/-- `rfl` or `word` (`word` now evaluates `W64 n` literals itself). -/
macro "hword" : tactic => `(tactic| first | rfl | word)

theorem sdiv2_nonneg (x : w64) (h : 0 ≤ sint.Z x) : BitVec.sdiv x (W64 2) = x / (2 : w64) := by
  have hmsb : x.msb = false := by
    rw [BitVec.msb_eq_toInt]; simp only [decide_eq_false_iff_not]; simp only [sint.Z] at h; omega
  rw [BitVec.sdiv_eq, hmsb]
  rfl

/-- `slice_index_if` with `hword`. -/
macro "hslice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> hword))]))

theorem sint_nat_toNat (x : w64) : sint.nat x = (sint.Z x).toNat := rfl

/-- `omega` after unfolding `sint.nat x` to `(sint.Z x).toNat` (so that `omega`
relates them); cheap, unlike `word`, which case-splits on the sign of every
`sint.Z` term in the context. -/
macro "iomega" : tactic => `(tactic| ((try simp only [sint_nat_toNat] at *); omega))

/-- `slice_index_if` with `iomega`. -/
macro "hslice_index_if'" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> iomega))]))

theorem lookup_idx_eq {T : Type} {l : List T} {n m : Nat} {x : T} (h : l[n]? = some x)
    (e : m = n) : l[m]? = some x := e ▸ h

set_option hygiene false in
/-- Load `data[i]` (bounds check, `wp_load_slice_index`) where `H : xs[n]? = some x`
and `n` is the index `i` as a `Nat` (proved with `hword`). -/
macro "load_at " H:ident : tactic => `(tactic| (
  hslice_index_if
  wp_apply wp_load_slice_index _ _ _ _ _ (by hword) $$ [Hxs] with Hxs
  all_goals try (iframe Hxs; ipureintro; exact lookup_idx_eq $H (by hword))))

set_option hygiene false in
/-- `load_at` with `iomega` (all index facts must be in the context). -/
macro "load_at' " H:ident : tactic => `(tactic| (
  hslice_index_if'
  wp_apply wp_load_slice_index _ _ _ _ _ (by iomega) $$ [Hxs] with Hxs
  all_goals try (iframe Hxs; ipureintro; exact lookup_idx_eq $H (by iomega))))

/-- `hslice_index_if` with an explicit proof `k` of a `heap_idx` fact. -/
macro "heap_slice_index_k " k:term:max : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true ($k).1)]))

set_option hygiene false in
/-- `load_at` with `word` instead of `hword` (whose `rfl` attempt is slow when it fails). -/
macro "heap_load_atw " H:ident : tactic => `(tactic| (
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]
  wp_apply wp_load_slice_index _ _ _ _ _ (by word) $$ [Hxs] with Hxs
  all_goals try (iframe Hxs; ipureintro; exact lookup_idx_eq $H (by word))))

set_option hygiene false in
/-- `load_at'` with an explicit `heap_idx` fact `k` for the index. -/
macro "heap_load_k " H:ident k:term:max : tactic => `(tactic| (
  heap_slice_index_k $k
  wp_apply wp_load_slice_index _ _ _ _ _ ($k).1.1 $$ [Hxs] with Hxs
  all_goals try (iframe Hxs; ipureintro; exact lookup_idx_eq $H ($k).2.1)))

-- (the lemmas below come after the macros: a `macro` declared after
-- asynchronously elaborated proofs waits for them)
theorem sift_arith1 (a lo root hi b : w64) (ha : 0 ≤ sint.Z a) (hlo : 0 ≤ sint.Z lo)
    (hr : sint.Z lo ≤ sint.Z root ∧ sint.Z root < sint.Z hi)
    (hb : sint.Z a + sint.Z hi ≤ sint.Z b) (hb2 : sint.Z b ≤ 2 ^ 62) :
    sint.Z (W64 2 * root + W64 1) = 2 * sint.Z root + 1 ∧
    sint.Z (a + root) = sint.Z a + sint.Z root ∧
    sint.Z (a + (W64 2 * root + W64 1)) = sint.Z a + 2 * sint.Z root + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> word

theorem sift_arith2 (a lo root hi b : w64) (ha : 0 ≤ sint.Z a) (hlo : 0 ≤ sint.Z lo)
    (hr : sint.Z lo ≤ sint.Z root ∧ 2 * sint.Z root + 1 < sint.Z hi)
    (hb : sint.Z a + sint.Z hi ≤ sint.Z b) (hb2 : sint.Z b ≤ 2 ^ 62) :
    sint.Z (W64 2 * root + W64 1 + W64 1) = 2 * sint.Z root + 2 ∧
    sint.Z (a + (W64 2 * root + W64 1) + W64 1) = sint.Z a + 2 * sint.Z root + 2 ∧
    sint.Z (a + (W64 2 * root + W64 1 + W64 1)) = sint.Z a + 2 * sint.Z root + 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> word

theorem heap_sint_nat_cast (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x :=
  Int.toNat_of_nonneg h

/-! Index facts of the `siftDown` proof, proved in a small context (`omega` in the
large context of the WP proof is slow). -/

theorem heap_idx (e lw : w64) (n L : Nat) (he : sint.Z e = (n : Int)) (hlw : sint.Z lw = (L : Int))
    (hn : n < L) :
    (0 ≤ sint.Z e ∧ sint.Z e < sint.Z lw) ∧ (sint.Z e).toNat = n ∧
      (0 ≤ sint.Z e ∧ sint.Z e < (L : Int)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega

theorem heap_nat_eq (e : w64) (n : Nat) (he : sint.Z e = (n : Int)) : sint.nat e = n := by
  show (sint.Z e).toNat = n
  omega

theorem heap_child_facts (a root : w64) (A RT : Nat) (ca : (A : Int) = sint.Z a)
    (cr : (RT : Int) = sint.Z root)
    (hchild : sint.Z (W64 2 * root + W64 1) = 2 * sint.Z root + 1)
    (hal : sint.Z (a + (W64 2 * root + W64 1)) = sint.Z a + 2 * sint.Z root + 1)
    (haroot : sint.Z (a + root) = sint.Z a + sint.Z root) :
    sint.Z (W64 2 * root + W64 1) = ((2 * RT + 1 : Nat) : Int) ∧
    sint.Z (a + (W64 2 * root + W64 1)) = ((A + (2 * RT + 1) : Nat) : Int) ∧
    sint.Z (a + root) = ((A + RT : Nat) : Int) := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem heap_rchild_facts (a root : w64) (A RT : Nat) (ca : (A : Int) = sint.Z a)
    (cr : (RT : Int) = sint.Z root)
    (hr2 : sint.Z (W64 2 * root + W64 1 + W64 1) = 2 * sint.Z root + 2)
    (halr : sint.Z (a + (W64 2 * root + W64 1) + W64 1) = sint.Z a + 2 * sint.Z root + 2)
    (har : sint.Z (a + (W64 2 * root + W64 1 + W64 1)) = sint.Z a + 2 * sint.Z root + 2) :
    sint.Z (W64 2 * root + W64 1 + W64 1) = ((2 * RT + 2 : Nat) : Int) ∧
    sint.Z (a + (W64 2 * root + W64 1) + W64 1) = ((A + (2 * RT + 2) : Nat) : Int) ∧
    sint.Z (a + (W64 2 * root + W64 1 + W64 1)) = ((A + (2 * RT + 2) : Nat) : Int) := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem heap_new_root_bounds {lo hi root c : w64} {cN : Nat} (clo : (sint.nat lo : Int) = sint.Z lo)
    (chi : (sint.nat hi : Int) = sint.Z hi) (cr : (sint.nat root : Int) = sint.Z root)
    (hcZ : sint.Z c = cN) (hcsel : cN = 2 * sint.nat root + 1 ∨ cN = 2 * sint.nat root + 2)
    (hcH : cN < sint.nat hi) (hLR : sint.nat lo ≤ sint.nat root) :
    sint.Z lo ≤ sint.Z c ∧ sint.Z c < sint.Z hi := by
  omega

section heap
variable {E : Type} (R : E → E → Prop)

def IsHeapSeg (xs : List E) (a b : Nat) (l r : Nat) : Prop :=
  ∀ (i : Nat) (xi xls xrs : E), l ≤ i ∧ i < r → xs[a + i]? = some xi →
    ((l ≤ 2 * i + 1 ∧ 2 * i + 1 < r → xs[a + 2 * i + 1]? = some xls → ¬ R xi xls) ∧
     (l ≤ 2 * i + 2 ∧ 2 * i + 2 < r → xs[a + 2 * i + 2]? = some xrs → ¬ R xi xrs))

theorem heap_seg_shrink (xs : List E) (a b l r : Nat) :
    IsHeapSeg R xs a b l (r + 1) → IsHeapSeg R xs a b l r := by
  intro H i xi xls xrs Hi Hxi
  obtain ⟨H1, H2⟩ := H i xi xls xrs ⟨Hi.1, by omega⟩ Hxi
  exact ⟨fun h => H1 ⟨h.1, by omega⟩, fun h => H2 ⟨h.1, by omega⟩⟩

theorem heap_top_greatest [StrictWeakOrder R] (xs : List E) (xtop xi : E) (a b i lim : Nat) :
    IsHeapSeg R xs a b 0 (lim + 1) →
    xs[a]? = some xtop →
    xs[a + i]? = some xi →
    (0 ≤ i ∧ i ≤ lim) →
    xs.length ≥ a + lim →
    ¬ R xtop xi := by
  intro Hheap Htop Hxi Hi Hlen
  induction i using Nat.strongRecOn generalizing xi with
  | _ i IH =>
    by_cases h0 : i = 0
    · subst h0
      rw [Nat.add_zero, Htop] at Hxi
      cases Hxi
      exact notR_refl R _
    · have hp : (i - 1) / 2 < i := by omega
      obtain ⟨xp, Hxp⟩ := list_lookup_lt xs (a + (i - 1) / 2) (by omega)
      have IHp := IH _ hp xp Hxp ⟨by omega, by omega⟩
      obtain ⟨Hl, Hr⟩ := Hheap ((i - 1) / 2) xp xi xi ⟨by omega, by omega⟩ Hxp
      have Hpi : ¬ R xp xi := by
        by_cases hodd : i = 2 * ((i - 1) / 2) + 1
        · exact Hl ⟨by omega, by omega⟩ (by rw [show a + 2 * ((i - 1) / 2) + 1 = a + i by omega]; exact Hxi)
        · exact Hr ⟨by omega, by omega⟩ (by rw [show a + 2 * ((i - 1) / 2) + 2 = a + i by omega]; exact Hxi)
      exact notR_trans R xi xp xtop IHp Hpi

/-! ### Invariant of the `siftDown` loop

`HeapExcept xs A L H r`: the heap property holds at every node of `[L, H)`
except possibly the current root `r`; `HeapParent xs A L H r`: the parent of
`r` (if in `[L, H)`) dominates the children of `r`. -/

def HeapExcept (xs : List E) (A L H r : Nat) : Prop :=
  ∀ (i c : Nat) (xi xc : E), L ≤ i → i < H → i ≠ r → (c = 2 * i + 1 ∨ c = 2 * i + 2) → c < H →
    xs[A + i]? = some xi → xs[A + c]? = some xc → ¬ R xi xc

def HeapParent (xs : List E) (A L H r : Nat) : Prop :=
  ∀ (p c : Nat) (xp xc : E), L ≤ p → p < H → (r = 2 * p + 1 ∨ r = 2 * p + 2) →
    (c = 2 * r + 1 ∨ c = 2 * r + 2) → c < H →
    xs[A + p]? = some xp → xs[A + c]? = some xc → ¬ R xp xc

theorem sift_inv_init (xs : List E) (A B L H : Nat) :
    IsHeapSeg R xs A B (L + 1) H → HeapExcept R xs A L H L ∧ HeapParent R xs A L H L := by
  intro Hh
  constructor
  · intro i c xi xc hLi hiH hir hc hcH hxi hxc
    obtain ⟨H1, H2⟩ := Hh i xi xc xc ⟨by omega, hiH⟩ hxi
    rcases hc with rfl | rfl
    · exact H1 ⟨by omega, hcH⟩ (by rw [show A + 2 * i + 1 = A + (2 * i + 1) by omega]; exact hxc)
    · exact H2 ⟨by omega, hcH⟩ (by rw [show A + 2 * i + 2 = A + (2 * i + 2) by omega]; exact hxc)
  · intro p c xp xc hLp _ hr; omega

/-- Closing the heap once the root dominates its children. -/
theorem sift_inv_close (xs : List E) (A B L H r : Nat) :
    HeapExcept R xs A L H r →
    (∀ (c : Nat) (xr xc : E), (c = 2 * r + 1 ∨ c = 2 * r + 2) → c < H →
      xs[A + r]? = some xr → xs[A + c]? = some xc → ¬ R xr xc) →
    IsHeapSeg R xs A B L H := by
  intro He Hr i xi xls xrs Hi Hxi
  have key : ∀ c xc, (c = 2 * i + 1 ∨ c = 2 * i + 2) → c < H → xs[A + c]? = some xc →
      ¬ R xi xc := by
    intro c xc hc hcH hxc
    by_cases hir : i = r
    · subst hir; exact Hr c xi xc hc hcH Hxi hxc
    · exact He i c xi xc Hi.1 Hi.2 hir hc hcH Hxi hxc
  refine ⟨fun h hx => key _ _ (Or.inl rfl) h.2 ?_, fun h hx => key _ _ (Or.inr rfl) h.2 ?_⟩
  · rw [show A + (2 * i + 1) = A + 2 * i + 1 by omega]; exact hx
  · rw [show A + (2 * i + 2) = A + 2 * i + 2 by omega]; exact hx

theorem swap_lookup (xs : List E) (i j k : Nat) (xi xj : E) (hi : i < xs.length)
    (hj : j < xs.length) :
    (<[i := xj]> (<[j := xi]> xs))[k]? =
      if k = i then some xj else if k = j then some xi else xs[k]? := by
  by_cases hki : k = i
  · subst hki; simp only [↓reduceIte]
    exact list_lookup_insert_eq _ (by rw [length_insert]; exact hi)
  · rw [list_lookup_insert_ne _ _ (Ne.symm hki)]
    simp only [hki, ↓reduceIte]
    by_cases hkj : k = j
    · subst hkj; simp only [↓reduceIte]; exact list_lookup_insert_eq _ hj
    · simp only [hkj, ↓reduceIte]; exact list_lookup_insert_ne _ _ (Ne.symm hkj)

/-- One step of `siftDown`: swap the root `r` with its greatest child `c`. -/
theorem sift_inv_step [StrictWeakOrder R] (xs : List E) (A L H r c : Nat) (xr xc : E)
    (HLr : L ≤ r) (HrH : r < H) (Hc : c = 2 * r + 1 ∨ c = 2 * r + 2) (HcH : c < H)
    (Hlen : A + H ≤ xs.length)
    (Hxr : xs[A + r]? = some xr) (Hxc : xs[A + c]? = some xc) (Hlt : R xr xc)
    (Hmax : ∀ c' xc', (c' = 2 * r + 1 ∨ c' = 2 * r + 2) → c' < H → xs[A + c']? = some xc' →
      ¬ R xc xc')
    (He : HeapExcept R xs A L H r) (Hp : HeapParent R xs A L H r) :
    HeapExcept R (<[A + c := xr]> (<[A + r := xc]> xs)) A L H c ∧
    HeapParent R (<[A + c := xr]> (<[A + r := xc]> xs)) A L H c := by
  have hl : ∀ k, (<[A + c := xr]> (<[A + r := xc]> xs))[A + k]? =
      if k = c then some xr else if k = r then some xc else xs[A + k]? := by
    intro k
    rw [swap_lookup xs (A + c) (A + r) (A + k) xc xr (by omega) (by omega)]
    by_cases hkc : k = c
    · simp [hkc]
    · by_cases hkr : k = r
      · simp [hkr, show ¬ (A + r = A + c) by omega]
      · simp [hkc, hkr, show ¬ (A + k = A + c) by omega, show ¬ (A + k = A + r) by omega]
  constructor
  · intro i c' xi xc' hLi hiH hic hc' hc'H hxi hxc'
    rw [hl] at hxi hxc'
    by_cases hir : i = r
    · subst hir
      simp only [show ¬ i = c by omega, ↓reduceIte] at hxi
      cases hxi
      by_cases hcc : c' = c
      · simp only [hcc, ↓reduceIte] at hxc'; cases hxc'
        exact R_antisym R _ _ Hlt
      · simp only [hcc, show ¬ c' = i by omega, ↓reduceIte] at hxc'
        exact Hmax c' xc' hc' hc'H hxc'
    · simp only [hic, hir, ↓reduceIte] at hxi
      have hc'c : c' ≠ c := by omega
      simp only [hc'c, ↓reduceIte] at hxc'
      by_cases hc'r : c' = r
      · simp only [hc'r, ↓reduceIte] at hxc'; cases hxc'
        exact Hp i c xi xc hLi hiH (by omega) Hc HcH hxi Hxc
      · simp only [hc'r, ↓reduceIte] at hxc'
        exact He i c' xi xc' hLi hiH hir hc' hc'H hxi hxc'
  · intro p c' xp xc' hLp hpH hp hc' hc'H hxp hxc'
    have hpr : p = r := by omega
    subst hpr
    rw [hl] at hxp hxc'
    simp only [show ¬ p = c by omega, ↓reduceIte] at hxp
    cases hxp
    simp only [show ¬ c' = c by omega, show ¬ c' = p by omega, ↓reduceIte] at hxc'
    exact He c c' xc xc' (by omega) HcH (by omega) hc' hc'H Hxc hxc'

def MaxChild (xs : List E) (A r H cN : Nat) : Prop :=
  ∀ c' xc xc', (c' = 2 * r + 1 ∨ c' = 2 * r + 2) → c' < H → xs[A + cN]? = some xc →
    xs[A + c']? = some xc' → ¬ R xc xc'

theorem maxChild_right [StrictWeakOrder R] (xs : List E) (A r H : Nat) (xl xr : E)
    (Hxl : xs[A + (2 * r + 1)]? = some xl) (Hxr : xs[A + (2 * r + 2)]? = some xr)
    (h : R xl xr) : MaxChild R xs A r H (2 * r + 2) := by
  intro c' xc xc' hc' _ hxc hxc'
  rw [Hxr] at hxc; cases hxc
  rcases hc' with h' | h' <;> subst h'
  · rw [Hxl] at hxc'; cases hxc'; exact R_antisym R _ _ h
  · rw [Hxr] at hxc'; cases hxc'; exact notR_refl R _

theorem maxChild_left [StrictWeakOrder R] (xs : List E) (A r H : Nat) (xl xr : E)
    (Hxl : xs[A + (2 * r + 1)]? = some xl) (Hxr : xs[A + (2 * r + 2)]? = some xr)
    (h : ¬ R xl xr) : MaxChild R xs A r H (2 * r + 1) := by
  intro c' xc xc' hc' _ hxc hxc'
  rw [Hxl] at hxc; cases hxc
  rcases hc' with h' | h' <;> subst h'
  · rw [Hxl] at hxc'; cases hxc'; exact notR_refl R _
  · rw [Hxr] at hxc'; cases hxc'; exact h

theorem maxChild_only [StrictWeakOrder R] (xs : List E) (A r H : Nat)
    (hH : H ≤ 2 * r + 2) : MaxChild R xs A r H (2 * r + 1) := by
  intro c' xc xc' hc' hc'H hxc hxc'
  rcases hc' with h' | h' <;> subst h'
  · rw [hxc] at hxc'; cases hxc'; exact notR_refl R _
  · omega

/-- `HeapExcept` only depends on the elements at `[A + L, A + H)`. -/
def SegSortedFrom (xs : List E) (A B j0 : Nat) : Prop :=
  ∀ (i j : Nat) (xi xj : E), i < j ∧ j0 ≤ j ∧ (A ≤ j ∧ j < B) ∧ (A ≤ i ∧ i < B) →
    xs[i]? = some xi → xs[j]? = some xj → ¬ R xj xi

theorem seg_sorted_swap (xs : List E) (A B j0 p q : Nat) (xp xq : E)
    (Hp : A ≤ p ∧ p < j0) (Hq : A ≤ q ∧ q < j0) (HB : j0 ≤ B) (Hlen : B ≤ xs.length)
    (Hxp : xs[p]? = some xp) (Hxq : xs[q]? = some xq) :
    SegSortedFrom R xs A B j0 → SegSortedFrom R (<[p := xq]> (<[q := xp]> xs)) A B j0 := by
  intro H i j xi xj Hij hxi hxj
  rw [swap_lookup xs p q _ xp xq (by omega) (by omega)] at hxi hxj
  simp only [show ¬ j = p by omega, show ¬ j = q by omega, ↓reduceIte] at hxj
  by_cases hip : i = p
  · simp only [hip, ↓reduceIte] at hxi; cases hxi
    exact H q j _ xj ⟨by omega, Hij.2.1, Hij.2.2.1, by omega⟩ Hxq hxj
  · by_cases hiq : i = q
    · subst hiq
      simp only [hip, ↓reduceIte] at hxi; cases hxi
      exact H p j _ xj ⟨by omega, Hij.2.1, Hij.2.2.1, by omega⟩ Hxp hxj
    · simp only [hip, hiq, ↓reduceIte] at hxi
      exact H i j xi xj Hij hxi hxj

/-! ### Facts for `heapSort` -/

theorem heap_seg_vacuous (xs : List E) (a b l r : Nat) (h : r ≤ 2 * l + 1) :
    IsHeapSeg R xs a b l r := by
  intro i xi xls xrs Hi _
  exact ⟨fun h' => by omega, fun h' => by omega⟩

/-- After moving the top `x0` of the heap `[0, i]` to position `A + i`, the
segment from `A + i` on is sorted relative to the whole `[A, B)`. -/
theorem heap_pop_seg [StrictWeakOrder R] (xs : List E) (A B i : Nat) (x0 xi : E)
    (Hheap : IsHeapSeg R xs A B 0 (i + 1)) (Hx0 : xs[A]? = some x0)
    (Hxi : xs[A + i]? = some xi) (HiB : A + i < B) (HB : B ≤ xs.length)
    (Hseg : SegSortedFrom R xs A B (A + i + 1)) :
    SegSortedFrom R (<[A + i := x0]> (<[A := xi]> xs)) A B (A + i) := by
  intro i' j xi' xj Hij hxi' hxj
  rw [swap_lookup xs (A + i) A _ xi x0 (by omega) (by omega)] at hxi' hxj
  by_cases hj : j = A + i
  · subst hj
    simp only [↓reduceIte] at hxj; cases hxj
    -- `xi'` is an element of the heap `[0, i]`
    have Hk : ∃ k, k ≤ i ∧ xs[A + k]? = some xi' := by
      by_cases h1 : i' = A
      · rw [h1] at hxi'
        simp only [show ¬ (A = A + i) by omega, ↓reduceIte] at hxi'; cases hxi'
        exact ⟨i, Nat.le_refl _, Hxi⟩
      · simp only [show ¬ (i' = A + i) by omega, h1, ↓reduceIte] at hxi'
        exact ⟨i' - A, by omega, by rw [show A + (i' - A) = i' by omega]; exact hxi'⟩
    obtain ⟨k, hk, hxk⟩ := Hk
    exact heap_top_greatest R xs x0 xi' A B k i Hheap Hx0 hxk ⟨by omega, hk⟩ (by omega)
  · have hjA : j ≠ A := by omega
    simp only [hj, hjA, ↓reduceIte] at hxj
    by_cases h1 : i' = A + i
    · rw [h1] at hxi'; simp only [↓reduceIte] at hxi'; cases hxi'
      exact Hseg A j _ xj ⟨by omega, by omega, Hij.2.2.1, by omega⟩ Hx0 hxj
    · by_cases h2 : i' = A
      · rw [h2] at hxi'
        simp only [show ¬ (A = A + i) by omega, ↓reduceIte] at hxi'; cases hxi'
        exact Hseg (A + i) j _ xj ⟨by omega, by omega, Hij.2.2.1, by omega⟩ Hxi hxj
      · simp only [h1, h2, ↓reduceIte] at hxi'
        exact Hseg i' j _ xj ⟨Hij.1, by omega, Hij.2.2.1, Hij.2.2.2⟩ hxi' hxj

theorem heap_pop_heap (xs : List E) (A B i : Nat) (x0 xi : E) (HB : A + i < xs.length)
    (Hheap : IsHeapSeg R xs A B 0 (i + 1)) :
    IsHeapSeg R (<[A + i := x0]> (<[A := xi]> xs)) A B 1 i := by
  intro k xk xl xr Hk hxk
  have hl : ∀ m, 1 ≤ m → m < i → (<[A + i := x0]> (<[A := xi]> xs))[A + m]? = xs[A + m]? := by
    intro m h1 h2
    rw [swap_lookup xs (A + i) A _ xi x0 (by omega) (by omega)]
    simp only [show ¬ (A + m = A + i) by omega, show ¬ (A + m = A) by omega, ↓reduceIte]
  rw [hl k Hk.1 Hk.2] at hxk
  obtain ⟨H1, H2⟩ := Hheap k xk xl xr ⟨by omega, by omega⟩ hxk
  refine ⟨fun h hx => H1 ⟨by omega, by omega⟩ ?_, fun h hx => H2 ⟨by omega, by omega⟩ ?_⟩
  · rw [show A + 2 * k + 1 = A + (2 * k + 1) by omega] at hx ⊢
    rwa [hl _ (by omega) h.2] at hx
  · rw [show A + 2 * k + 2 = A + (2 * k + 2) by omega] at hx ⊢
    rwa [hl _ (by omega) h.2] at hx

end heap

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

theorem wp_siftDownCmpFunc (data : GoSlice) (lo hi a b : w64) (cmp_code : GoFunc) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmpImplements R cmp_code ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z a + sint.Z lo ∧
                        sint.Z a + sint.Z lo < sint.Z a + sint.Z hi ∧
                        sint.Z a + sint.Z hi ≤ sint.Z b ∧
                        sint.Z b ≤ xs.length ∧
                        xs.length ≤ 2 ^ 62⌝ ∗
        "%HSegSorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                    (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                    (sint.nat a ≤ i ∧ i < sint.nat b) →
                    xs[i]? = some xi →
                    xs[j]? = some xj → ¬ R xj xi⌝ ∗
        "%Heap" ∷ ⌜IsHeapSeg R xs (sint.nat a) (sint.nat b) (sint.nat lo + 1) (sint.nat hi)⌝ }}
      (App (App (App (App (App (Val #(functions siftDownCmpFunc [Et])) (Val #data)) (Val #lo))
        (Val #hi)) (Val #a)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%HPermPost" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%HSegSortedPost" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                    (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                    (sint.nat a ≤ i ∧ i < sint.nat b) →
                    xs'[i]? = some xi →
                    xs'[j]? = some xj → ¬ R xj xi⌝ ∗
        "%Heap" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  unfold cmpImplements
  ihave %Hlen0 := ownSlice_len _ _ _ $$ Hxs
  have Hinit := sift_inv_init R xs (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi) Heap
  ihave HI : (∃ (root_val : w64) (xs' : List E),
      "root" ∷ root_ptr ↦ root_val ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Hbound1" ∷ ⌜sint.Z lo ≤ sint.Z root_val ∧ sint.Z root_val < sint.Z hi⌝ ∗
      "%HSeg1" ∷ ⌜SegSortedFrom R xs' (sint.nat a) (sint.nat b) (sint.nat a + sint.nat hi)⌝ ∗
      "%He" ∷ ⌜HeapExcept R xs' (sint.nat a) (sint.nat lo) (sint.nat hi) (sint.nat root_val)⌝ ∗
      "%Hp" ∷ ⌜HeapParent R xs' (sint.nat a) (sint.nat lo) (sint.nat hi) (sint.nat root_val)⌝ ∗
      "%Hout" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [root Hxs]
  · iexists lo, xs
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, ⟨by omega, by omega⟩, HSegSorted, Hinit.1, Hinit.2,
      outsideSame_refl _ _ _⟩
  wp_for HI
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  have HlenEq := HPerm1.length_eq
  obtain ⟨Hchild, Haroot, Hal⟩ := sift_arith1 a lo root_val hi b H_bounds.1 (by omega) Hbound1
    (by omega) (by omega)
  have h0 : sint.Z (W64 0) = 0 := by decide
  have hdl : sint.Z data.len = xs'.length := by iomega
  have ca := heap_sint_nat_cast a H_bounds.1
  have clo := heap_sint_nat_cast lo (by omega)
  have chi := heap_sint_nat_cast hi (by omega)
  have cb := heap_sint_nat_cast b (by omega)
  have croot := heap_sint_nat_cast root_val (by omega)
  have hHlen : sint.nat a + sint.nat hi ≤ xs'.length := by omega
  have hHB : sint.nat a + sint.nat hi ≤ sint.nat b := by omega
  have hBL : sint.nat b ≤ xs'.length := by omega
  have hLR : sint.nat lo ≤ sint.nat root_val := by omega
  have hrH : sint.nat root_val < sint.nat hi := by omega
  clear Hlen Hlen0 HlenEq Hinit HSegSorted Heap
  wp_if_destruct
  · -- `child ≥ hi`: break
    wp_for_post
    iapply HΦ
    iframe
    ipureintro
    refine ⟨HPerm1, HSeg1, ?_, Hout⟩
    exact sift_inv_close R xs' _ _ _ _ _ He (fun c _ _ hc hcH => by
      exfalso; omega)
  · have hrc : 2 * sint.nat root_val + 1 < sint.nat hi := by omega
    obtain ⟨Hr2, Halr, Har⟩ := sift_arith2 a lo root_val hi b H_bounds.1 (by omega)
      ⟨Hbound1.1, by omega⟩ (by omega) (by omega)
    obtain ⟨kc1, kal, karoot⟩ := heap_child_facts a root_val _ _ ca croot Hchild Hal Haroot
    obtain ⟨kc2, kalr, kar⟩ := heap_rchild_facts a root_val _ _ ca croot Hr2 Halr Har
    have hrA : sint.nat a + (2 * sint.nat root_val + 1) < xs'.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrc _) hHlen
    have hrtL : sint.nat a + sint.nat root_val < xs'.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrH _) hHlen
    have kxl := heap_idx _ _ _ _ kal hdl hrA
    have kxrt := heap_idx _ _ _ _ karoot hdl hrtL
    have hridx : (sint.Z (a + root_val)).toNat = sint.nat a + sint.nat root_val := kxrt.2.1
    obtain ⟨xl, Hxl⟩ := list_lookup_lt xs' _ hrA
    -- choose the greatest child `c` (three cases), joined at `Hsel`
    wp_join iprop(∃ (c : w64),
        "child" ∷ child_ptr ↦ c ∗
        "Hxs" ∷ data ↦* xs' ∗
        "cmp" ∷ cmp_ptr ↦ cmp_code ∗
        "first" ∷ first_ptr ↦ a ∗
        "data" ∷ data_ptr ↦ data ∗
        "%Hsel" ∷ ⌜∃ cN : Nat, sint.nat c = cN ∧ sint.Z c = cN ∧
          (cN = 2 * sint.nat root_val + 1 ∨ cN = 2 * sint.nat root_val + 2) ∧ cN < sint.nat hi ∧
          MaxChild R xs' (sint.nat a) (sint.nat root_val) (sint.nat hi) cN ∧
          sint.Z (a + c) = ((sint.nat a + cN : Nat) : Int)⌝)
      with [child Hxs cmp first data] as ⟨%c, child, Hxs, cmp, first, data, %Hsel⟩
    · -- the right child is in bounds: compare the children
      have hrc2 : 2 * sint.nat root_val + 2 < sint.nat hi := by omega
      have hrR : sint.nat a + (2 * sint.nat root_val + 2) < xs'.length :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrc2 _) hHlen
      have kxr := heap_idx _ _ _ _ kalr hdl hrR
      obtain ⟨xr', Hxr'⟩ := list_lookup_lt xs' (sint.nat a + (2 * sint.nat root_val + 2)) hrR
      heap_load_k Hxl kxl
      heap_load_k Hxr' kxr
      wp_apply Hcmp with %r1 %Hr1
      wp_if_destruct
      · -- the right child is greater
        wp_join_done
        iexists _
        iframe
        ipureintro
        exact ⟨2 * sint.nat root_val + 2, heap_nat_eq _ _ kc2, kc2, Or.inr rfl, hrc2,
          maxChild_right R xs' _ _ _ xl xr' Hxl Hxr' (Hr1.1 (by omega)), kar⟩
      · -- the left child is not smaller
        wp_join_done
        iexists _
        iframe
        ipureintro
        exact ⟨2 * sint.nat root_val + 1, heap_nat_eq _ _ kc1, kc1, Or.inl rfl, hrc,
          maxChild_left R xs' _ _ _ xl xr' Hxl Hxr' (fun h => Hif (by have := Hr1.2 h; omega)),
          kal⟩
    · -- the right child is out of bounds: only the left child
      iexists _
      iframe
      ipureintro
      exact ⟨2 * sint.nat root_val + 1, heap_nat_eq _ _ kc1, kc1, Or.inl rfl, hrc,
        maxChild_only R xs' _ _ _ (by omega), kal⟩
    clear Hr2 Halr Har Hal Hchild Hxl xl kc1 kal kc2 kalr kar kxl
    obtain ⟨cN, hcN, hcZ, hcsel, hcH, Hmax, hcidx⟩ := Hsel
    have hcL : sint.nat a + cN < xs'.length := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcH _) hHlen
    have kxc := heap_idx _ _ _ _ hcidx hdl hcL
    obtain ⟨xrt, Hxrt⟩ := list_lookup_lt xs' (sint.nat a + sint.nat root_val) hrtL
    obtain ⟨xc, Hxc⟩ := list_lookup_lt xs' (sint.nat a + cN) hcL
    heap_load_k Hxrt kxrt
    heap_load_k Hxc kxc
    wp_apply Hcmp with %r2 %Hr2'
    by_cases hlt : sint.Z r2 < sint.Z (W64 0)
    · -- the root is smaller than the child: swap and continue
      simp only [decide_eq_true hlt, Bool.not_true]
      wp_auto
      heap_load_k Hxc kxc
      heap_load_k Hxrt kxrt
      heap_slice_index_k kxrt
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ xs' xc $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact kxrt.2.2
      rw [hridx]
      heap_slice_index_k kxc
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ (xs'.set (sint.nat a + sint.nat root_val) xc) xrt $$ [Hxs]
        with Hxs
      · iframe Hxs; ipureintro; refine ⟨kxc.2.2.1, ?_⟩; rw [List.length_set]; exact kxc.2.2.2
      rw [kxc.2.1]
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      rw [hcN]
      have Hlt' : R xrt xc := Hr2'.1 (by omega)
      have Hstep := sift_inv_step R xs' (sint.nat a) (sint.nat lo) (sint.nat hi) (sint.nat root_val)
        cN xrt xc hLR hrH hcsel hcH hHlen Hxrt Hxc Hlt'
        (fun c' xc' h1 h2 h3 => Hmax c' xc xc' h1 h2 Hxc h3) He Hp
      have hAc : sint.nat a ≤ sint.nat a + cN := Nat.le_add_right _ _
      have hAr : sint.nat a ≤ sint.nat a + sint.nat root_val := Nat.le_add_right _ _
      have hrj : sint.nat a + sint.nat root_val < sint.nat a + sint.nat hi :=
        Nat.add_lt_add_left hrH _
      have hcj : sint.nat a + cN < sint.nat a + sint.nat hi := Nat.add_lt_add_left hcH _
      refine ⟨HPerm1.trans (swap_perm xs' _ _ xc xrt Hxc Hxrt), heap_new_root_bounds clo chi croot
          hcZ hcsel hcH hLR, ?_, Hstep.1, Hstep.2, ?_⟩
      · exact seg_sorted_swap R xs' _ _ _ _ _ xc xrt ⟨hAc, hcj⟩ ⟨hAr, hrj⟩
          hHB hBL Hxc Hxrt HSeg1
      · exact outsideSame_trans _ _ _ _ _ Hout
          (outsideSame_swap xs' _ _ xc xrt _ _ ⟨hAc, Nat.lt_of_lt_of_le hcj hHB⟩
            ⟨hAr, Nat.lt_of_lt_of_le hrj hHB⟩)
    · -- the root dominates its children: return
      simp only [decide_eq_false hlt, Bool.not_false]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      refine ⟨HPerm1, HSeg1, ?_, Hout⟩
      exact sift_inv_close R xs' _ _ _ _ _ He (fun c' x1 x2 hc' hc'H h1 h2 => by
        rw [Hxrt] at h1; cases h1
        have h3 : ¬ R xrt xc := fun h => hlt (by have := Hr2'.2 h; omega)
        exact notR_trans R x2 xc xrt h3 (Hmax c' xc x2 hc' hc'H Hxc h2))

theorem wp_siftDownCmpFunc_Trivial (data : GoSlice) (a b : w64) (cmp_code : GoFunc)
    (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmpImplements R cmp_code ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (App (Val #(functions siftDownCmpFunc [Et])) (Val #data))
        (Val #(W64 0))) (Val #(W64 0))) (Val #a)) (Val #cmp_code))
    {{ RET #(); "Hxs" ∷ data ↦* xs }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_for
  wp_for_post
  iapply HΦ
  iframe

theorem wp_heapSortCmpFunc (data : GoSlice) (a b : w64) (cmp_code : GoFunc) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmpImplements R cmp_code ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (Val #(functions heapSortCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat b)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  have hn : sint.Z (b - a) = sint.Z b - sint.Z a := by word
  have hnn : sint.nat (b - a) = sint.nat b - sint.nat a := by word
  have hi0 : sint.Z (BitVec.sdiv (b - a - W64 1) (W64 2)) = (sint.Z b - sint.Z a - 1) / 2 := by
    rw [sdiv2_nonneg _ (by word)]; word
  -- the outer (heapify) loop
  ihave HI1 : (∃ (i_val : w64) (xs' : List E),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%Hir" ∷ ⌜-1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b - sint.Z a - 1⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Heap1" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) (sint.nat (i_val + W64 1))
        (sint.nat (b - a))⌝ ∗
      "%HSeg1" ∷ ⌜SegSortedFrom R xs' (sint.nat a) (sint.nat b) (sint.nat a + sint.nat (b - a))⌝ ∗
      "%Hout1" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [i Hxs]
  · iexists _, xs
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, List.Perm.refl _, heap_seg_vacuous R _ _ _ _ _ (by word), ?_,
      outsideSame_refl _ _ _⟩
    intro i j xi xj Hij _ _; omega
  wp_for HI1
  wp_if_destruct
  · -- sift down from `i`
    have e1 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
    rw [e1] at Heap1
    have hl1 := HPerm1.length_eq
    wp_apply wp_siftDownCmpFunc R data i_val (b - a) a b cmp_code xs' $$ [Hxs]
      with %xs'' ⟨Hxs, %HPermPost, %HSegPost, %HeapPost, %HoutPost⟩
    · iframe Hxs; iframe #; ipureintro
      exact ⟨⟨by word, by word, by word, by word, by word, by word⟩, HSeg1, Heap1⟩
    wp_for_post
    iframe
    iexists (i_val - W64 1), xs''
    iframe
    ipureintro
    have e2 : sint.nat (i_val - W64 1 + W64 1) = sint.nat i_val := by word
    rw [e2]
    exact ⟨⟨by word, by word⟩, HPerm1.trans HPermPost, HeapPost, HSegPost,
      outsideSame_trans _ _ _ _ _ Hout1 HoutPost⟩
  · -- the heap is built
    have e1 : sint.nat (i_val + W64 1) = 0 := by word
    rw [e1] at Heap1
    have hl1 := HPerm1.length_eq
    -- the sorting loop
    ihave HI2 : (∃ (i_val : w64) (xs' : List E),
        "i" ∷ i_ptr ↦ i_val ∗
        "Hxs" ∷ data ↦* xs' ∗
        "%Hir" ∷ ⌜-1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b - sint.Z a - 1⌝ ∗
        "%HPerm2" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Heap2" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) 0 (sint.nat (i_val + W64 1))⌝ ∗
        "%HSeg2" ∷ ⌜SegSortedFrom R xs' (sint.nat a) (sint.nat b)
          (sint.nat a + sint.nat i_val + 1)⌝ ∗
        "%Hout2" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [i Hxs]
    · iexists _, xs'
      iframe
      ipureintro
      have e3 : sint.nat (b - a - W64 1 + W64 1) = sint.nat (b - a) := by word
      have e4 : sint.nat a + sint.nat (b - a - W64 1) + 1 = sint.nat a + sint.nat (b - a) := by word
      rw [e3, e4]
      exact ⟨⟨by word, by word⟩, HPerm1, Heap1, HSeg1, Hout1⟩
    wp_for HI2
    have hl2 := HPerm2.length_eq
    wp_if_destruct
    · ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
      obtain ⟨xi, Hxi⟩ := list_lookup_lt xs' (sint.nat a + sint.nat i_val) (by word)
      obtain ⟨x0, Hx0⟩ := list_lookup_lt xs' (sint.nat a) (by word)
      heap_load_atw Hxi
      heap_load_atw Hx0
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ xs' xi $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; constructor <;> word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ (xs'.set (sint.Z a).toNat xi) x0 $$ [Hxs]
        with Hxs
      · iframe Hxs; ipureintro; refine ⟨by word, ?_⟩; rw [List.length_set]; word
      rw [show (sint.Z (a + i_val)).toNat = sint.nat a + sint.nat i_val by word,
        show (sint.Z a).toNat = sint.nat a from rfl]
      by_cases hz : sint.Z i_val = 0
      · -- `i = 0`: the swap is trivial
        have hz' : i_val = W64 0 := BitVec.toInt_inj.mp (hz.trans (by decide))
        subst hz'
        have e0 : sint.nat (W64 0) = 0 := by decide
        rw [e0, Nat.add_zero] at Hxi
        rw [Hx0] at Hxi; cases Hxi
        rw [e0, Nat.add_zero, list_insert_id (list_lookup_insert_eq _ (by word)), list_insert_id Hx0]
        wp_apply wp_siftDownCmpFunc_Trivial R data a b cmp_code xs' $$ [Hxs] with Hxs
        · iframe Hxs; iframe #; ipureintro; exact ⟨by word, by word, by word⟩
        wp_for_post
        iframe
        iexists (W64 0 - W64 1), xs'
        iframe
        ipureintro
        have e5 : sint.nat (W64 0 - W64 1 + W64 1) = 0 := by decide
        have e6 : sint.nat (W64 0 - W64 1) = 0 := by decide
        rw [e5, e6]
        rw [e0] at HSeg2
        exact ⟨⟨by word, by word⟩, HPerm2, heap_seg_vacuous R _ _ _ _ _ (by omega), HSeg2, Hout2⟩
      · -- `i ≥ 1`: sift the new root down in `[0, i)`
        have e1 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
        rw [e1] at Heap2
        wp_apply wp_siftDownCmpFunc R data (W64 0) i_val a b cmp_code
          ((xs'.set (sint.nat a) xi).set (sint.nat a + sint.nat i_val) x0) $$ [Hxs]
          with %xs3 ⟨Hxs, %HP, %HS, %HH, %HO⟩
        · iframe Hxs; iframe #; ipureintro
          refine ⟨⟨by word, by word, by word, by word, by rw [List.length_set, List.length_set]; word,
            by rw [List.length_set, List.length_set]; word⟩, ?_, ?_⟩
          · exact heap_pop_seg R xs' _ _ _ x0 xi Heap2 Hx0 Hxi (by word) (by word) HSeg2
          · rw [show sint.nat (W64 0) + 1 = 1 from rfl]
            exact heap_pop_heap R xs' _ _ _ x0 xi (by word) Heap2
        wp_for_post
        iframe
        iexists (i_val - W64 1), xs3
        iframe
        ipureintro
        have e2 : sint.nat (i_val - W64 1 + W64 1) = sint.nat i_val := by word
        have e3 : sint.nat a + sint.nat (i_val - W64 1) + 1 = sint.nat a + sint.nat i_val := by word
        rw [e2, e3]
        refine ⟨⟨by word, by word⟩,
          HPerm2.trans ((swap_perm xs' _ _ xi x0 Hxi Hx0).trans HP), HH, HS, ?_⟩
        exact outsideSame_trans _ _ _ _ _ Hout2 (outsideSame_trans _ _ _ _ _
          (outsideSame_swap xs' _ _ xi x0 _ _ ⟨by omega, by word⟩ ⟨by omega, by word⟩) HO)
    · -- done
      iapply HΦ
      iframe
      ipureintro
      have e0 : sint.nat i_val = 0 := by word
      rw [e0] at HSeg2
      refine ⟨HPerm2, ?_, Hout2⟩
      intro i j xi xj Hij hxi hxj
      exact HSeg2 i j xi xj ⟨Hij.1.2, by omega, ⟨by omega, Hij.2⟩, ⟨Hij.1.1, by omega⟩⟩ hxi hxj

end proof

end slices

end Perennial
end

