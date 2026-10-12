/-
The heap lemmas and proof-script macros of the proofs of `siftDownCmpFunc` and
`heapSortCmpFunc` (reused by their `Ordered` copies).
-/
module

public import Perennial.Proof.slices.SortBasics

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

end proof

end slices

end Perennial
end

