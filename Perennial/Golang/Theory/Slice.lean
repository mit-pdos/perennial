/-
Port of `new/golang/theory/slice.v`: the slice points-to `s ↦*{dq} vs`
(`own_slice`), the capacity predicate `own_slice_cap V s dq`, lemmas for
splitting/combining slices, and specs for the slice built-ins (`len`, `cap`,
`make`, `copy`, `clear`, `append`, indexing, slice literals, `for range`).
-/
import Perennial.Golang.Theory.Array
import Perennial.Golang.Theory.Loop
import Perennial.Golang.Theory.Auto
import Perennial.Golang.Theory.Assume
import Perennial.Golang.Defn.Slice
import Perennial.GooseLang.IPersist
import Perennial.Std.List

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepL

/-! ## Definitions -/

noncomputable section defns
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]

/-- A nil slice has no backing array (its pointer is null), so it cannot satisfy
an array typed points-to. Thus `own_slice` is a disjunction: either the slice
is nil and the list is empty, or there is a backing array. `own_slice` is meant
to serve as precondition for slice-related built-in operations. This matches
Go's guarantee that nil slices are valid empty slices for all built-in
operations. -/
def own_slice_def {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : slice.t) (vs : List V) (dq : DFrac) : IProp GF :=
  iprop(⌜s = slice.nil ∧ vs = []⌝ ∨
    (typed_pointsto s.ptr (array.mk (sint.Z s.len) vs) dq ∗ ⌜sint.Z s.len ≤ sint.Z s.cap⌝))

@[irreducible] def own_slice {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : slice.t) (vs : List V) (dq : DFrac) : IProp GF :=
  own_slice_def s vs dq

theorem own_slice_unseal : @own_slice = @own_slice_def := by
  funext; with_unfolding_all rfl

/-- The capacity of a slice: the elements past its length up to its capacity,
with arbitrary values. -/
def own_slice_cap_def (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : slice.t) (dq : DFrac) : IProp GF :=
  iprop(⌜slice_index_ref V (sint.Z s.len) s = null ∧ 0 ≤ sint.Z s.len ∧ s.len = s.cap⌝ ∨
    (⌜0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝ ∗
    -- The capacity buffer has arbitrary values, which is often desirable, but
    -- there are some niche cases where code could be aware of the contents of
    -- the capacity (for example, when sub-slicing from a larger slice) -
    -- actually taking advantage of that seems questionable though.
     ∃ (a : array.t V (sint.Z s.cap - sint.Z s.len)),
       typed_pointsto (slice_index_ref V (sint.Z s.len) s) a dq))

@[irreducible] def own_slice_cap (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : slice.t) (dq : DFrac) : IProp GF :=
  own_slice_cap_def V s dq

theorem own_slice_cap_unseal : @own_slice_cap = @own_slice_cap_def := by
  funext; with_unfolding_all rfl

end defns

/-- `s ↦*{dq} vs`: the slice `s` holds the elements `vs`. -/
scoped notation:50 s:50 " ↦*{" dq "} " vs:50 => own_slice s vs dq
/-- `s ↦* vs`: the slice `s` holds `vs`, with full ownership. -/
scoped notation:50 s:50 " ↦* " vs:50 => own_slice s vs (DFrac.own 1)
/-- `s ↦*□ vs`: persistent slice points-to. -/
scoped notation:50 s:50 " ↦*□ " vs:50 => own_slice s vs DFrac.discard

/-! ## Pure lemmas about `slice.slice` -/

section pure
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]
variable {V : Type}

theorem slice_to_full_slice (s : slice.t) (low high : w64) :
    slice.slice s V low high = slice.full_slice s V low high s.cap := rfl

/-- Introduce a `slice.slice` for lemmas that require it. -/
theorem slice_slice_trivial (s : slice.t) :
    s = slice.slice s V (W64 0) s.len := by
  obtain ⟨p, l, c⟩ := s
  simp only [slice.slice, slice_index_ref]
  have : sint.Z (W64 0) = 0 := rfl
  rw [this, go.array_index_ref_0]
  congr 1 <;> simp

theorem slice_slice (s : slice.t) (low high low' high' : w64)
    (hoverflow : 0 ≤ sint.Z low + sint.Z low' ∧ sint.Z low + sint.Z low' < 2 ^ 63) :
    slice.slice (slice.slice s V low high) V low' high' =
      slice.slice s V (low + low') (low + high') := by
  simp only [slice.slice, slice_index_ref]
  rw [← go.array_index_ref_add]
  have : sint.Z (low + low') = sint.Z low + sint.Z low' := by word
  rw [this]
  congr 1 <;> bv_omega

end pure

/-! ## Lemmas -/

section lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

theorem own_slice_nil (dq : DFrac) : ⊢ (slice.nil ↦*{dq} ([] : List V) : IProp GF) := by
  rw [own_slice_unseal]; unfold own_slice_def
  ileft; ipureintro; exact ⟨rfl, rfl⟩

theorem own_slice_empty (dq : DFrac) (s : slice.t) (hlen : sint.Z s.len = 0)
    (hcap : 0 ≤ sint.Z s.cap) :
    typed_pointsto (GF := GF) s.ptr (array.mk 0 ([] : List V)) dq ⊢ s ↦*{dq} ([] : List V) := by
  rw [own_slice_unseal]; unfold own_slice_def
  iintro H
  iright
  rw [hlen]
  iframe H
  ipureintro; omega

include preSem in
theorem own_slice_cap_empty (s : slice.t) (hcap : s.len = s.cap) (hlen : 0 ≤ sint.Z s.len) :
    ⊢ own_slice_cap (GF := GF) V s (DFrac.own 1) := by
  rw [own_slice_cap_unseal]; unfold own_slice_cap_def
  by_cases h : slice_index_ref V (sint.Z s.len) s = null
  · ileft; ipureintro; exact ⟨h, hlen, hcap⟩
  · iright
    isplit
    · ipureintro; rw [hcap] at hlen ⊢; omega
    · have : sint.Z s.cap - sint.Z s.len = 0 := by rw [hcap]; omega
      rw [this]
      iexists array.mk 0 []
      iapply array_empty _ _ h

theorem own_slice_len (s : slice.t) (dq : DFrac) (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊢ ⌜vs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len⌝ := by
  rw [own_slice_unseal]; unfold own_slice_def
  iintro (%H | ⟨H, %_⟩)
  · obtain ⟨rfl, rfl⟩ := H
    ipureintro; simp [slice.nil]; rfl
  · icases array_len _ _ _ _ $$ H with %Hlen
    ipureintro; constructor <;> word

theorem own_slice_agree (s : slice.t) (dq1 dq2 : DFrac) (vs1 vs2 : List V) :
    (s ↦*{dq1} vs1 : IProp GF) ⊢ s ↦*{dq2} vs2 -∗ ⌜vs1 = vs2⌝ := by
  rw [own_slice_unseal]; unfold own_slice_def
  iintro (%H1 | ⟨Hs1, %_⟩) (%H2 | ⟨Hs2, %_⟩)
  · ipureintro; rw [H1.2, H2.2]
  · icases typed_pointsto_not_null _ _ _ $$ Hs2 with %Hnn
    exact absurd (by rw [H1.1]; rfl) Hnn
  · icases typed_pointsto_not_null _ _ _ $$ Hs1 with %Hnn
    exact absurd (by rw [H2.1]; rfl) Hnn
  · icombine Hs1 Hs2 gives %Heq
    ipureintro
    exact congrArg array.t.arr Heq

instance own_slice_persistent (s : slice.t) (vs : List V) :
    Persistent (s ↦*□ vs : IProp GF) := by
  rw [own_slice_unseal]; unfold own_slice_def; infer_instance

instance own_slice_timeless (s : slice.t) (dq : DFrac) (vs : List V) :
    Timeless (s ↦*{dq} vs : IProp GF) := by
  rw [own_slice_unseal]; unfold own_slice_def; infer_instance

instance own_slice_dfractional (s : slice.t) (vs : List V) :
    DFractional (fun dq => (s ↦*{dq} vs : IProp GF)) := by
  rw [own_slice_unseal]; unfold own_slice_def
  constructor
  · intro dq1 dq2
    constructor
    · iintro (%H | ⟨H, %Hl⟩)
      · isplitl [] <;> (ileft; ipureintro; exact H)
      · icases ((typed_pointsto_dfractional _ _).dfractional dq1 dq2).1 $$ H with ⟨H1, H2⟩
        isplitl [H1]
        · iright; iframe H1; ipureintro; exact Hl
        · iright; iframe H2; ipureintro; exact Hl
    · iintro ⟨(%H1 | ⟨H1, %Hl⟩), (%H2 | ⟨H2, %Hl2⟩)⟩
      · ileft; ipureintro; exact H1
      · icases typed_pointsto_not_null _ _ _ $$ H2 with %Hnn
        exact absurd (by rw [H1.1]; rfl) Hnn
      · icases typed_pointsto_not_null _ _ _ $$ H1 with %Hnn
        exact absurd (by rw [H2.1]; rfl) Hnn
      · iright
        isplitl [H1 H2]
        · iapply ((typed_pointsto_dfractional _ _).dfractional dq1 dq2).2
          iframe H1 H2
        · ipureintro; exact Hl
  · infer_instance
  · intro dq
    iintro (%H | ⟨H, %Hl⟩)
    · imodintro; ileft; ipureintro; exact H
    · imod (typed_pointsto_dfractional _ _).dfractional_persist dq $$ H with H
      imodintro; iright; iframe H; ipureintro; exact Hl

instance own_slice_as_dfractional (s : slice.t) (dq : DFrac) (vs : List V) :
    AsDFractional (s ↦*{dq} vs : IProp GF) (fun dq => s ↦*{dq} vs) dq :=
  ⟨.rfl, own_slice_dfractional s vs⟩

instance own_slice_fractional (s : slice.t) (vs : List V) :
    Fractional (fun q => (s ↦*{DFrac.own q} vs : IProp GF)) :=
  fractional_of_dfractional (fun dq => s ↦*{dq} vs)

instance own_slice_as_fractional (s : slice.t) (q : Qp) (vs : List V) :
    AsFractional (s ↦*{DFrac.own q} vs : IProp GF) ioΦ (fun q => s ↦*{DFrac.own q} vs) ioq q :=
  ⟨.rfl, own_slice_fractional s vs⟩

instance own_slice_combine_sep_gives (s : slice.t) (dq1 dq2 : DFrac) (vs1 vs2 : List V) :
    CombineSepGives (s ↦*{dq1} vs1 : IProp GF) (s ↦*{dq2} vs2) iprop(⌜vs1 = vs2⌝) where
  combine_sep_gives := by
    iintro ⟨H1, H2⟩
    icases own_slice_agree s dq1 dq2 vs1 vs2 $$ H1 H2 with %Heq
    imodintro; ipureintro; exact Heq

instance (priority := low) own_slice_combine_sep_as (s : slice.t) (dq1 dq2 : DFrac)
    (vs1 vs2 : List V) :
    CombineSepAs (s ↦*{dq1} vs1 : IProp GF) (s ↦*{dq2} vs2) (s ↦*{dq1 • dq2} vs1) where
  combine_sep_as := by
    iintro ⟨H1, H2⟩
    icases own_slice_agree s dq1 dq2 vs1 vs2 $$ H1 [H2] with %Heq
    · iexact H2
    subst Heq
    iapply ((own_slice_dfractional s vs1).dfractional dq1 dq2).2
    iframe H1 H2

instance own_slice_cap_persistent (s : slice.t) :
    Persistent (own_slice_cap (GF := GF) V s DFrac.discard) := by
  rw [own_slice_cap_unseal]; unfold own_slice_cap_def; infer_instance

instance own_slice_cap_dfractional (s : slice.t) :
    DFractional (fun dq => own_slice_cap (GF := GF) V s dq) := by
  rw [own_slice_cap_unseal]; unfold own_slice_cap_def
  constructor
  · intro dq1 dq2
    constructor
    · iintro (%H | ⟨%Hl, %a, H⟩)
      · isplitl [] <;> (ileft; ipureintro; exact H)
      · icases ((typed_pointsto_dfractional _ _).dfractional dq1 dq2).1 $$ H with ⟨H1, H2⟩
        isplitl [H1]
        · iright; isplit; · ipureintro; exact Hl
          iexists a; iexact H1
        · iright; isplit; · ipureintro; exact Hl
          iexists a; iexact H2
    · iintro ⟨(%H1 | ⟨%Hl, %a1, H1⟩), (%H2 | ⟨%Hl2, %a2, H2⟩)⟩
      · ileft; ipureintro; exact H1
      · icases typed_pointsto_not_null _ _ _ $$ H2 with %Hnn
        exact absurd H1.1 Hnn
      · icases typed_pointsto_not_null _ _ _ $$ H1 with %Hnn
        exact absurd H2.1 Hnn
      · icombine H1 H2 gives %Heq
        subst Heq
        iright
        isplit
        · ipureintro; exact Hl
        iexists a1
        iapply ((typed_pointsto_dfractional _ _).dfractional dq1 dq2).2
        iframe H1 H2
  · infer_instance
  · intro dq
    iintro (%H | ⟨%Hl, %a, H⟩)
    · imodintro; ileft; ipureintro; exact H
    · imod (typed_pointsto_dfractional _ _).dfractional_persist dq $$ H with H
      imodintro; iright; isplit
      · ipureintro; exact Hl
      iexists a; iexact H

instance own_slice_cap_as_dfractional (s : slice.t) (dq : DFrac) :
    AsDFractional (own_slice_cap (GF := GF) V s dq) (fun dq => own_slice_cap V s dq) dq :=
  ⟨.rfl, own_slice_cap_dfractional s⟩

theorem own_slice_persist (s : slice.t) (dq : DFrac) (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊢ |==> s ↦*□ vs :=
  (own_slice_dfractional s vs).dfractional_persist dq

instance own_slice_update_to_persistent (s : slice.t) (dq : DFrac) (vs : List V) :
    UpdateIntoPersistently (s ↦*{dq} vs : IProp GF) (s ↦*□ vs) :=
  dfractional_update_into_persistently _ (fun dq => s ↦*{dq} vs) dq

instance own_slice_cap_update_to_persistent (s : slice.t) (dq : DFrac) :
    UpdateIntoPersistently (own_slice_cap (GF := GF) V s dq) (own_slice_cap V s DFrac.discard) :=
  dfractional_update_into_persistently _ (fun dq => own_slice_cap V s dq) dq

theorem own_slice_cap_wf (s : slice.t) (dq : DFrac) :
    own_slice_cap (GF := GF) V s dq ⊢ ⌜0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝ := by
  rw [own_slice_cap_unseal]; unfold own_slice_cap_def
  iintro (%H | ⟨%H, _⟩)
  · ipureintro; obtain ⟨_, h1, h2⟩ := H; rw [← h2]; omega
  · ipureintro; exact H

/-- Only for backwards compatibility; the non-primed version is more precise
about signed length. -/
theorem own_slice_cap_wf' (s : slice.t) (dq : DFrac) :
    own_slice_cap (GF := GF) V s dq ⊢ ⌜uint.Z s.len ≤ uint.Z s.cap⌝ := by
  iintro H
  icases own_slice_cap_wf s dq $$ H with %H
  ipureintro; word

theorem own_slice_wf (s : slice.t) (dq : DFrac) (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊢ ⌜0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝ := by
  rw [own_slice_unseal]; unfold own_slice_def
  iintro (%H | ⟨H, %Hl⟩)
  · obtain ⟨rfl, _⟩ := H
    ipureintro; simp only [slice.nil]; decide
  · icases array_len _ _ _ _ $$ H with %Hlen
    ipureintro; constructor <;> omega

/-- Only for backwards compatibility; the non-primed version is more precise
about signed length. -/
theorem own_slice_wf' (s : slice.t) (dq : DFrac) (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊢ ⌜uint.Z s.len ≤ uint.Z s.cap⌝ := by
  iintro H
  icases own_slice_wf s dq vs $$ H with %H
  ipureintro; word

include preSem in
theorem own_slice_cap_nil : ⊢ own_slice_cap (GF := GF) V slice.nil (DFrac.own 1) := by
  rw [own_slice_cap_unseal]; unfold own_slice_cap_def
  ileft; ipureintro
  refine ⟨?_, by decide, rfl⟩
  simp only [slice_index_ref, slice.nil]
  have : sint.Z (0 : w64) = 0 := rfl
  rw [this, go.array_index_ref_0]

include preSem in
/-- A variant of `slice_slice_trivial` that's easier to use with `icases` and
more discoverable with search. -/
theorem own_slice_trivial_slice (s : slice.t) (dq : DFrac) (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊣⊢ slice.slice s V (W64 0) s.len ↦*{dq} vs := by
  rw [← slice_slice_trivial (V := V)]; exact .rfl

include preSem in
theorem own_slice_trivial_slice_2 (s : slice.t) (dq : DFrac) (vs : List V) :
    (slice.slice s V (W64 0) s.len ↦*{dq} vs : IProp GF) ⊢ s ↦*{dq} vs :=
  (own_slice_trivial_slice s dq vs).2

theorem own_slice_elem_acc (i : Int) (v : V) (s : slice.t) (dq : DFrac) (vs : List V)
    (hpos : 0 ≤ i) (hlookup : vs[i.toNat]? = some v) :
    (s ↦*{dq} vs : IProp GF) ⊢
      typed_pointsto (slice_index_ref V i s) v dq ∗
      (∀ v', typed_pointsto (slice_index_ref V i s) v' dq -∗ s ↦*{dq} (vs.set i.toNat v')) := by
  rw [own_slice_unseal]; unfold own_slice_def
  iintro (%H | ⟨Hsl, %Hl⟩)
  · rw [H.2] at hlookup; simp at hlookup
  · icases array_acc (V := V) s.ptr i dq _ (array.mk (sint.Z s.len) vs) v hpos hlookup $$ Hsl
      with ⟨Hv, Hsl⟩
    simp only [slice_index_ref]
    iframe Hv
    iintro %v' Hv'
    iright
    isplitl [Hsl Hv']
    · iapply Hsl $$ Hv'
    · ipureintro; exact Hl

/-- FIXME: maintain that owned array length doesn't overflow 64 bits? -/
theorem slice_array (l : loc) (n : Int) (a : array.t V n) (hlen : a.arr.length < 2 ^ 63) :
    (typed_pointsto l a (DFrac.own 1) : IProp GF) ⊢
      slice.mk l (W64 n) (W64 n) ↦* a.arr := by
  obtain ⟨arr⟩ := a
  iintro H
  icases array_len _ _ _ _ $$ H with %Hn
  rw [own_slice_unseal]; unfold own_slice_def
  iright
  have : sint.Z (W64 n) = n := by subst Hn; word
  simp only
  rw [this]
  iframe H
  ipureintro; omega

end lemmas

/-! ## List lemmas -/

theorem list_set_lookup_self {A : Type} (l : List A) (n : Nat) (v : A) (h : l[n]? = some v) :
    l.set n v = l := by
  apply List.ext_getElem?; intro j
  rw [List.getElem?_set]
  split
  · subst_vars; simp_all; exact (List.getElem?_eq_some_iff.1 h).1
  · rfl

theorem list_copy_step {A : Type} (vs vs' : List A) (n : Nat) (y : A) (h1 : n < vs.length)
    (hy : vs'[n]? = some y) :
    (vs'.take n ++ vs.drop n).set n y = vs'.take (n + 1) ++ vs.drop (n + 1) := by
  have h2 : n < vs'.length := (List.getElem?_eq_some_iff.1 hy).1
  have h3 : (vs'.take n).length = n := by simp; omega
  rw [List.set_append_right _ _ (by omega), h3, Nat.sub_self, List.take_add_one, hy,
    List.drop_eq_getElem_cons h1]
  simp only [List.append_assoc, List.set_cons_zero, Option.toList_some, List.singleton_append]

/-! ## Splitting and combining slices -/

theorem slice_mk_eq_nil (p : loc) (l c : w64) :
    slice.mk p l c = slice.nil ↔ p = null ∧ l = 0 ∧ c = 0 := by
  simp [slice.nil, slice.mk]

section lemmas2
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

include preSem in
theorem own_slice_split (k : w64) (s : slice.t) (dq : DFrac) (vs : List V) (low high : w64)
    (hle : 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z k ∧ sint.Z k ≤ sint.Z high) :
    (slice.slice s V low high ↦*{dq} vs : IProp GF) ⊣⊢
      slice.slice s V low k ↦*{dq} vs.take (sint.nat k - sint.nat low) ∗
      slice.slice s V k high ↦*{dq} vs.drop (sint.nat k - sint.nat low) := by
  obtain ⟨h0, h1, h2⟩ := hle
  have hkl : sint.Z (k - low) = sint.Z k - sint.Z low := by word
  have hhl : sint.Z (high - low) = sint.Z high - sint.Z low := by word
  have hhk : sint.Z (high - k) = sint.Z high - sint.Z k := by word
  have hn1 : sint.nat (k - low) = sint.nat k - sint.nat low := by word
  have hn2 : sint.Z (high - low) - sint.Z (k - low) = sint.Z (high - k) := by word
  have hp : array_index_ref V (sint.Z (k - low)) (array_index_ref V (sint.Z low) s.ptr) =
      array_index_ref V (sint.Z k) s.ptr := by
    rw [← go.array_index_ref_add]; congr 1; omega
  have e := array_split (GF := GF) (k - low) (array_index_ref V (sint.Z low) s.ptr) dq
    (sint.Z (high - low)) (array.mk _ vs) ⟨by omega, by omega⟩
  rw [hn1, hn2, hp] at e
  simp only [slice.slice, slice_index_ref]
  rw [own_slice_unseal]; unfold own_slice_def
  constructor
  · iintro (%Hnil | ⟨H, %Hcap⟩)
    · obtain ⟨Hs, rfl⟩ := Hnil
      rw [slice_mk_eq_nil] at Hs
      obtain ⟨Hp, Hl, Hc⟩ := Hs
      have hk : k = low := by word
      have hh : high = low := by word
      subst hk; subst hh
      isplitl [] <;> (ileft; ipureintro; simp [slice_mk_eq_nil, Hp, Hc])
    · icases e.1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iright; iframe H1; ipureintro; dsimp only at Hcap ⊢; word
      · iright; iframe H2; ipureintro; dsimp only at Hcap ⊢; word
  · iintro ⟨(%Hnil1 | ⟨H1, %Hcap1⟩), (%Hnil2 | ⟨H2, %Hcap2⟩)⟩
    · ileft; ipureintro
      obtain ⟨Hs1, Hv1⟩ := Hnil1
      obtain ⟨Hs2, Hv2⟩ := Hnil2
      rw [slice_mk_eq_nil] at Hs1 Hs2
      refine ⟨?_, ?_⟩
      · rw [slice_mk_eq_nil]; exact ⟨Hs1.1, by word, Hs1.2.2⟩
      · rw [← List.take_append_drop (sint.nat k - sint.nat low) vs, Hv1, Hv2]; rfl
    · icases typed_pointsto_not_null _ _ _ $$ H2 with %Hnn
      exfalso; apply Hnn
      obtain ⟨Hs1, _⟩ := Hnil1
      rw [slice_mk_eq_nil] at Hs1
      have hk : k = low := by word
      subst hk; exact Hs1.1
    · icases typed_pointsto_not_null _ _ _ $$ H1 with %Hnn
      exfalso; apply Hnn
      obtain ⟨Hs2, _⟩ := Hnil2
      rw [slice_mk_eq_nil, ← hp] at Hs2
      exact go.array_index_ref_null_inv _ _ _ Hs2.1
    · iright
      isplitl [H1 H2]
      · iapply e.2; iframe H1 H2
      · ipureintro; dsimp only at *; word

include preSem in
theorem own_slice_combine (k : w64) (s : slice.t) (dq : DFrac) (vs1 vs2 : List V) (low high : w64)
    (hwf : vs1.length = sint.nat k - sint.nat low ∧
      0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z k ∧ sint.Z k ≤ sint.Z high) :
    (slice.slice s V low k ↦*{dq} vs1 : IProp GF) ⊢
      slice.slice s V k high ↦*{dq} vs2 -∗ slice.slice s V low high ↦*{dq} (vs1 ++ vs2) := by
  iintro H1 H2
  iapply (own_slice_split k s dq (vs1 ++ vs2) low high hwf.2).2
  rw [← hwf.1, List.take_left, List.drop_left]
  iframe H1 H2

include preSem in
theorem own_slice_split_all (k : w64) (s : slice.t) (dq : DFrac) (vs : List V)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len) :
    (s ↦*{dq} vs : IProp GF) ⊣⊢
      slice.slice s V (W64 0) k ↦*{dq} vs.take (sint.nat k) ∗
      slice.slice s V k s.len ↦*{dq} vs.drop (sint.nat k) := by
  refine (own_slice_trivial_slice s dq vs).trans ?_
  refine (own_slice_split k s dq vs (W64 0) s.len ⟨by decide, by word, hk.2⟩).trans ?_
  have : sint.nat k - sint.nat (W64 0) = sint.nat k := by word
  rw [this]; exact .rfl

include preSem in
private theorem own_slice_cap_same_end (s s' : slice.t) (dq : DFrac)
    (hend : slice_index_ref V (sint.Z s.len) s = slice_index_ref V (sint.Z s'.len) s')
    (hcap : sint.Z s.cap - sint.Z s.len = sint.Z s'.cap - sint.Z s'.len)
    (hwf : 0 ≤ sint.Z s.len ∧ 0 ≤ sint.Z s'.len) :
    own_slice_cap (GF := GF) V s dq ⊣⊢ own_slice_cap V s' dq := by
  rw [own_slice_cap_unseal]; unfold own_slice_cap_def
  rw [hend, hcap]
  have e1 : s.len = s.cap ↔ s'.len = s'.cap := by
    constructor <;> intro h <;> word
  have e2 : (sint.Z s.len ≤ sint.Z s.cap) ↔ (sint.Z s'.len ≤ sint.Z s'.cap) := by omega
  simp only [e1, e2, hwf.1, hwf.2, true_and]
  exact .rfl

include preSem in
/-- `own_slice_cap` only depends on where the end of the slice is. -/
theorem own_slice_cap_slice_change_first (s : slice.t) (low low' high : w64) (dq : DFrac)
    (hb : sint.Z high ≤ sint.Z s.cap ∧ 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧
      0 ≤ sint.Z low' ∧ sint.Z low' ≤ sint.Z high) :
    own_slice_cap (GF := GF) V (slice.slice s V low high) dq ⊢
      own_slice_cap V (slice.slice s V low' high) dq := by
  refine (own_slice_cap_same_end _ _ dq ?_ ?_ ?_).1
  · simp only [slice.slice, slice_index_ref]
    rw [← go.array_index_ref_add, ← go.array_index_ref_add]; congr 1; word
  · simp only [slice.slice]; word
  · simp only [slice.slice]; constructor <;> word

include preSem in
theorem own_slice_cap_slice (s : slice.t) (low : w64) (dq : DFrac)
    (hb : 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap) :
    own_slice_cap (GF := GF) V s dq ⊣⊢ own_slice_cap V (slice.slice s V low s.len) dq := by
  refine own_slice_cap_same_end _ _ dq ?_ ?_ ?_
  · simp only [slice.slice, slice_index_ref]
    rw [← go.array_index_ref_add]; congr 1; word
  · simp only [slice.slice]; word
  · simp only [slice.slice]; constructor <;> word

include preSem in
/-- Divide ownership of `s ↦* vs` around a slice `slice.slice s V low high`.

This is not the only choice; see `own_slice_slice_with_cap` for a variation
that uses capacity. -/
theorem own_slice_slice (low high : w64) (s : slice.t) (dq : DFrac) (vs : List V)
    (hb : 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.len) :
    (s ↦*{dq} vs : IProp GF) ⊣⊢
      slice.slice s V (W64 0) low ↦*{dq} vs.take (sint.nat low) ∗
      slice.slice s V low high ↦*{dq} subslice (sint.nat low) (sint.nat high) vs ∗
      -- after the sliced part
      slice.slice s V high s.len ↦*{dq} vs.drop (sint.nat high) := by
  refine (own_slice_trivial_slice s dq vs).trans ?_
  refine (own_slice_split low s dq vs (W64 0) s.len ⟨by decide, by word, by omega⟩).trans ?_
  refine (sep_congr .rfl (own_slice_split high s dq _ low s.len ⟨by omega, by omega, by omega⟩)).trans ?_
  have h0 : sint.nat low - sint.nat (W64 0) = sint.nat low := by word
  have h1 : (vs.drop (sint.nat low)).take (sint.nat high - sint.nat low) =
      subslice (sint.nat low) (sint.nat high) vs := by
    simp only [subslice, List.drop_take]
  have h2 : (vs.drop (sint.nat low)).drop (sint.nat high - sint.nat low) =
      vs.drop (sint.nat high) := by
    rw [List.drop_drop]; congr 1; word
  rw [h0, h1, h2]; exact .rfl


include preSem in
theorem own_slice_slice_absorb_capacity (s : slice.t) (vs : List V) (low high : w64)
    (hb : 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.len) :
    (slice.slice s V high s.len ↦* vs ∗ own_slice_cap V s (DFrac.own 1) : IProp GF) ⊢
      own_slice_cap V (slice.slice s V low high) (DFrac.own 1) := by
  iintro ⟨Hvs, Hcap⟩
  ihave %Hlen := own_slice_len _ _ _ $$ Hvs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hvs
  ihave %Hwf' := own_slice_cap_wf _ _ $$ Hcap
  simp only [slice.slice] at Hlen Hwf
  iapply own_slice_cap_slice_change_first s (W64 0) low high _ ⟨by omega, by word, by word, hb.1, hb.2.1⟩
  have hs0 : slice.slice s V (W64 0) high = slice.mk s.ptr high s.cap := by
    simp only [slice.slice, slice_index_ref]
    rw [show sint.Z (W64 0) = 0 from rfl, go.array_index_ref_0]
    congr 1 <;> simp
  rw [hs0]
  simp only [slice.slice, slice_index_ref]
  rw [own_slice_cap_unseal, own_slice_unseal]; unfold own_slice_cap_def own_slice_def
  simp only [slice_index_ref]
  have hrl : array_index_ref V (sint.Z (s.len - high)) (array_index_ref V (sint.Z high) s.ptr) =
      array_index_ref V (sint.Z s.len) s.ptr := by
    rw [← go.array_index_ref_add]; congr 1; word
  icases Hcap with (%Hcn | ⟨%_, %a, Ha⟩)
  · icases Hvs with (%Hvn | ⟨Hvs, %_⟩)
    · -- `Hvs` also nil: `high = s.len = s.cap`, and the result capacity is nil
      obtain ⟨Hvn, _⟩ := Hvn
      rw [slice_mk_eq_nil] at Hvn
      ileft; ipureintro
      exact ⟨Hvn.1, by omega, by word⟩
    · -- `Hvs` non-nil: use its points-to as the result capacity buffer
      iright
      isplit
      · ipureintro; constructor <;> omega
      have : sint.Z s.cap - sint.Z high = sint.Z (s.len - high) := by rw [← Hcn.2.2]; word
      rw [this]
      iexists _
      iexact Hvs
  · icases Hvs with (%Hvn | ⟨Hvs, %_⟩)
    · -- `Hvs` nil contradicts the non-nil capacity
      icases typed_pointsto_not_null _ _ _ $$ Ha with %Hnn
      exfalso; apply Hnn
      obtain ⟨Hvn, _⟩ := Hvn
      rw [slice_mk_eq_nil] at Hvn
      rw [← hrl, Hvn.1, show s.len - high = 0 from Hvn.2.1]
      exact go.array_index_ref_0 _ _
    · obtain ⟨arr'⟩ := a
      ihave %Hlen' := array_len _ _ _ _ $$ Ha
      iright
      isplit
      · ipureintro; constructor <;> omega
      have e := array_split (GF := GF) (s.len - high) (array_index_ref V (sint.Z high) s.ptr)
        (DFrac.own 1) (sint.Z s.cap - sint.Z high) (array.mk _ (vs ++ arr')) ⟨by word, by word⟩
      have hl : vs.length = sint.nat (s.len - high) := Hlen.1
      rw [← hl, List.take_left, List.drop_left, hrl,
        show sint.Z s.cap - sint.Z high - sint.Z (s.len - high) = sint.Z s.cap - sint.Z s.len by
          word] at e
      iexists _
      iapply e.2
      iframe Hvs Ha

include preSem in
/-- Divide ownership of `s ↦* vs ∗ own_slice_cap V s` around a slice
`slice.slice s V low high`, moving ownership between `high` and `s.len` into
the capacity of the slice.

TODO: could generalize to `⊣⊢`; just need to generalize some deps. -/
theorem own_slice_slice_with_cap (low high : w64) (s : slice.t) (vs : List V)
    (hb : 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.len) :
    (s ↦* vs ∗ own_slice_cap V s (DFrac.own 1) : IProp GF) ⊢
      slice.slice s V (W64 0) low ↦* vs.take (sint.nat low) ∗
      slice.slice s V low high ↦* subslice (sint.nat low) (sint.nat high) vs ∗
      -- after the sliced part + capacity of original slice
      own_slice_cap V (slice.slice s V low high) (DFrac.own 1) := by
  iintro ⟨Hs, Hcap⟩
  icases (own_slice_slice low high s _ vs hb).1 $$ Hs with ⟨Hs1, Hs2, Hs3⟩
  iframe Hs1 Hs2
  iapply own_slice_slice_absorb_capacity s _ low high hb
  iframe Hs3 Hcap

include preSem in
theorem own_slice_cap_split (high : w64) (s : slice.t) :
    (own_slice_cap V s (DFrac.own 1) ∗
      ⌜sint.Z s.len ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.cap⌝ : IProp GF) ⊢
      ∃ vs' : List V, slice.slice s V s.len high ↦* vs' ∗
        own_slice_cap V (slice.slice s V s.len high) (DFrac.own 1) := by
  iintro ⟨Hcap, %Hb⟩
  simp only [slice.slice, slice_index_ref]
  rw [own_slice_unseal, own_slice_cap_unseal]; unfold own_slice_def own_slice_cap_def
  simp only [slice_index_ref]
  icases Hcap with (%Hcn | ⟨%Hwf, %a, Ha⟩)
  · obtain ⟨Hnull, _, Hlc⟩ := Hcn
    have hh : high = s.cap := by word
    subst hh
    iexists []
    rw [← Hlc, BitVec.sub_self]
    isplitl []
    · ileft; ipureintro; exact ⟨by rw [slice_mk_eq_nil]; exact ⟨Hnull, rfl, rfl⟩, rfl⟩
    · ileft; ipureintro
      refine ⟨?_, by decide, rfl⟩
      have h0 : sint.Z (0#64 : w64) = 0 := rfl
      rw [h0, go.array_index_ref_0]; exact Hnull
  · obtain ⟨arr⟩ := a
    ihave %Hlen := array_len _ _ _ _ $$ Ha
    have e := array_split (GF := GF) (high - s.len) (array_index_ref V (sint.Z s.len) s.ptr)
      (DFrac.own 1) (sint.Z s.cap - sint.Z s.len) (array.mk _ arr) ⟨by word, by word⟩
    rw [show sint.Z s.cap - sint.Z s.len - sint.Z (high - s.len) =
        sint.Z (s.cap - s.len) - sint.Z (high - s.len) by word,
      ← go.array_index_ref_add] at e
    dsimp only at e
    icases e.1 $$ Ha with ⟨H1, H2⟩
    iexists (arr.take (sint.nat (high - s.len)))
    isplitl [H1]
    · iright; iframe H1; ipureintro; word
    · iright
      isplit
      · ipureintro; constructor <;> word
      iexists _
      rw [← go.array_index_ref_add]
      iexact H2

include preSem in
/-- An unusual use case for slicing where in `s[low:high]` we have
`len(s) ≤ high`. This moves elements from the hidden capacity of `s` into its
actual contents. -/
theorem own_slice_slice_into_capacity (low high : w64) (s : slice.t) (vs : List V) :
    (s ↦* vs ∗ own_slice_cap V s (DFrac.own 1) ∗
      ⌜0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧
        sint.Z s.len ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.cap⌝ : IProp GF) ⊢
      ∃ vs_cap : List V,
        slice.slice s V (W64 0) low ↦* (vs ++ vs_cap).take (sint.nat low) ∗
        slice.slice s V low high ↦* (vs ++ vs_cap).drop (sint.nat low) ∗
        own_slice_cap V (slice.slice s V low high) (DFrac.own 1) := by
  iintro ⟨Hs, Hcap, %Hb⟩
  icases own_slice_cap_split high s $$ [Hcap] with ⟨%vs', Hs', Hcap⟩
  · iframe Hcap; ipureintro; exact ⟨Hb.2.2.1, Hb.2.2.2⟩
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  ihave %Hlen' := own_slice_len _ _ _ $$ Hs'
  ihave Hcap := own_slice_cap_slice_change_first s s.len low high _
    ⟨Hb.2.2.2, Hwf.1, Hb.2.2.1, Hb.1, Hb.2.1⟩ $$ Hcap
  iframe Hcap
  iexists vs'
  simp only [slice.slice] at Hlen'
  by_cases hl : sint.Z low ≤ sint.Z s.len
  · icases (own_slice_split_all low s _ vs ⟨Hb.1, hl⟩).1 $$ Hs with ⟨Hs1, Hs2⟩
    rw [List.take_append_of_le_length (by word), List.drop_append_of_le_length (by word)]
    iframe Hs1
    iapply own_slice_combine s.len s _ (vs.drop (sint.nat low)) vs' low high
      ⟨by simp only [List.length_drop]; word, Hb.1, hl, Hb.2.2.1⟩ $$ Hs2 Hs'
  · icases (own_slice_split low s _ vs' s.len high ⟨Hwf.1, by omega, Hb.2.1⟩).1 $$ Hs'
      with ⟨Hs1, Hs2⟩
    rw [List.take_append, List.drop_append,
      List.take_of_length_le (l := vs) (i := sint.nat low) (by word),
      List.drop_of_length_le (l := vs) (i := sint.nat low) (by word), List.nil_append,
      show sint.nat low - vs.length = sint.nat low - sint.nat s.len by word]
    iframe Hs2
    iapply own_slice_combine s.len s _ vs _ (W64 0) low
      ⟨by word, by decide, Hwf.1, by omega⟩ $$ [Hs] Hs1
    iapply (own_slice_trivial_slice s _ vs).1 $$ Hs

end lemmas2

/-! ## Instances with the `ZeroVal V` instance determined by `TypeRepr`

(see `go_zero_val_step'`) -/

instance (priority := high) index_ref_slice' [ffi_syntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.PreSemantics] (elem_type : go.type) (i : w64) (s : slice.t)
    {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦IndexRef (go.SliceType elem_type), (#s, #i)⟧ ⤳[under]
    (if 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len then
       #(slice_index_ref V (sint.Z i) s)
     else Panic "slice index out of bounds") :=
  go.index_ref_slice elem_type i s

instance (priority := high) slice_slice_step_pure' [ffi_syntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.PreSemantics] (elem_type : go.type) (s : slice.t) (low high : w64)
    {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦Slice (go.SliceType elem_type), (#s, #low, #high)⟧ ⤳[under]
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.cap then
       #(slice.slice s V low high)
     else Panic "slice bounds out of range") :=
  go.slice_slice_step_pure elem_type s low high

instance (priority := high) full_slice_slice_step_pure' [ffi_syntax] [GoLocalContext]
    [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics] (elem_type : go.type) (s : slice.t)
    (low high max : w64) {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦FullSlice (go.SliceType elem_type), (#s, #low, #high, #max)⟧ ⤳[under]
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ sint.Z max ∧
        sint.Z max ≤ sint.Z s.cap then
       #(slice.full_slice s V low high max)
     else Panic "slice bounds out of range") :=
  go.full_slice_slice_step_pure elem_type s low high max

/-! ## WPs -/

section pure_wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance pure_wp_slice_len {st t : go.type} [st ↓u go.SliceType t] (sl : slice.t) :
    PureWp (G := G) (L := L) True (App (Val #(functions go.len [st])) (Val #sl)) (Val #sl.len) :=
  pure_wp_val True (App (Val #(functions go.len [st])) (Val #sl)) #sl.len fun s E Φ _ => by
    rw [func_unfold]
    iintro HΦ
    wp_auto_lc 1
    iapply HΦ $$ Hlc1

instance pure_wp_slice_cap {st t : go.type} [st ↓u go.SliceType t] (sl : slice.t) :
    PureWp (G := G) (L := L) True (App (Val #(functions go.cap [st])) (Val #sl)) (Val #sl.cap) :=
  pure_wp_val True (App (Val #(functions go.cap [st])) (Val #sl)) #sl.cap fun s E Φ _ => by
    rw [func_unfold]
    iintro HΦ
    wp_auto_lc 1
    iapply HΦ $$ Hlc1

instance pure_wp_slice_for_range (sl : slice.t) (body : val) (t : go.type) :
    PureWp (G := G) (L := L) True (App (App (Val (slice.for_range t)) (Val #sl)) (Val body))
      gl(let: "i" := GoAlloc go.int #(W64 0) in
        for: (λ: <>, (![go.int] "i") <⟨go.int⟩ (FuncResolve go.len [go.SliceType t]) #() #sl) ;
             (λ: <>, "i" <-[go.int] (![go.int] "i") +⟨go.int⟩ #(W64 1)) :=
          (λ: <>, body (![go.int] "i")
            (![t] (IndexRef (go.SliceType t) (#sl, (![go.int] "i")))))) where
  pure_wp_wp s E Φ K _ := by
    unfold slice.for_range
    iintro H
    wp_call_lc Hlc
    iapply H $$ Hlc

end pure_wps

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

theorem wp_slice_make3 {st t : go.type} [st ↓u go.SliceType t] [IntoValTyped (GF := GF) V t]
    (len cap : w64) (hle : 0 ≤ sint.Z len ∧ sint.Z len ≤ sint.Z cap) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.make3 [st])) (Val #len)) (Val #cap)) @ s; E
    {{ (sl : slice.t), RET #sl;
        sl ↦* (List.replicate (sint.nat len) (zero_val V)) ∗
        own_slice_cap V sl (DFrac.own 1) ∗ ⌜sl.cap = cap⌝ }} := by
  wp_start
  wp_if_destruct
  · exfalso; omega
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · -- cap = 0 case: no allocation, need nil slice
    -- TODO: model should return slice.nil when cap=0; currently
    -- wp_ArbitraryInt gives arbitrary ptr with no pointsto
    wp_apply wp_ArbitraryInt as %x _
    have hlen : len = W64 0 := by word
    subst hlen
    iapply HΦ
    have hnn : (loc.mk 1 0 +ₗ sint.Z x) ≠ null := by
      simp [null, loc.add]
    isplitl []
    · have : sint.nat (W64 0) = 0 := rfl
      rw [this, List.replicate_zero]
      iapply own_slice_empty _ _ (by rfl) (by word)
      iapply array_empty _ _ hnn
    isplitl []
    · iapply own_slice_cap_empty _ rfl (by word)
    · ipureintro; rfl
  · iapply HΦ
    have hz : (zero_val (array.t V (sint.Z cap))).arr =
        List.replicate (sint.Z cap).toNat (zero_val V) := rfl
    have e := array_split (GF := GF) len p_ptr (DFrac.own 1) _ (zero_val (array.t V (sint.Z cap)))
      ⟨by omega, by omega⟩
    rw [hz, List.take_replicate, List.drop_replicate,
      show min (sint.nat len) (sint.Z cap).toNat = sint.nat len by word] at e
    icases e.1 $$ p with ⟨Hsl, Hcap⟩
    rw [own_slice_unseal, own_slice_cap_unseal]; unfold own_slice_def own_slice_cap_def
    isplitl [Hsl]
    · iright; iframe Hsl; ipureintro; dsimp only; omega
    isplitl [Hcap]
    · iright
      isplit
      · ipureintro; dsimp only; omega
      iexists _
      simp only [slice_index_ref]
      iexact Hcap
    · ipureintro; rfl

theorem wp_slice_make2 {st t : go.type} [st ↓u go.SliceType t] [IntoValTyped (GF := GF) V t]
    (len : w64) :
    {{ (⌜0 ≤ sint.Z len⌝ : IProp GF) }}
      (App (Val #(functions go.make2 [st])) (Val #len)) @ s; E
    {{ (sl : slice.t), RET #sl;
        sl ↦* (List.replicate (sint.nat len) (zero_val V)) ∗ own_slice_cap V sl (DFrac.own 1) }} := by
  wp_start as %Hlen
  wp_apply wp_slice_make3 len len ⟨Hlen, Int.le_refl _⟩ as %sl ⟨Hsl, Hcap, _⟩
  iapply HΦ
  iframe

theorem wp_load_slice_index {t : go.type} [IntoValTyped (GF := GF) V t] (sl : slice.t) (i : Int)
    (vs : List V) (dq : DFrac) (v : V) (hpos : 0 ≤ i) :
    {{ (sl ↦*{dq} vs ∗ ⌜vs[i.toNat]? = some v⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoLoad t))) (Val #(slice_index_ref V i sl))) @ s; E
    {{ RET #v; sl ↦*{dq} vs }} := by
  iintro %Φ ⟨Hs, %Hlookup⟩ HΦ
  icases own_slice_elem_acc i v sl dq vs hpos Hlookup $$ Hs with ⟨Hv, Hs⟩
  wp_apply IntoValTyped.wp_load (t := t) _ _ _ $$ Hv as Hv
  iapply HΦ
  ihave Hs := Hs $$ Hv
  rw [list_set_lookup_self vs i.toNat v Hlookup]
  iexact Hs

theorem wp_store_slice_index {t : go.type} [IntoValTyped (GF := GF) V t] (sl : slice.t) (i : Int)
    (vs : List V) (v' : V) :
    {{ (sl ↦* vs ∗ ⌜0 ≤ i ∧ i < vs.length⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #(slice_index_ref V i sl) #v'))) @ s; E
    {{ RET #(); sl ↦* vs.set i.toNat v' }} := by
  iintro %Φ ⟨Hs, %Hb⟩ HΦ
  obtain ⟨v, Hv⟩ : ∃ v, vs[i.toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases own_slice_elem_acc i v sl _ vs Hb.1 Hv $$ Hs with ⟨Hv, Hs⟩
  wp_apply IntoValTyped.wp_store (t := t) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Hs $$ Hv

theorem wp_slice_copy {st t : go.type} [st ↓u go.SliceType t] [IntoValTyped (GF := GF) V t]
    (sl : slice.t) (vs : List V) (sl2 : slice.t) (vs' : List V) (dq : DFrac) :
    {{ (sl ↦* vs ∗ sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.copy [st])) (Val #sl)) (Val #sl2)) @ s; E
    {{ (n : w64), RET #n; ⌜sint.nat n = min vs.length vs'.length⌝ ∗
        sl ↦* (vs'.take vs.length ++ vs.drop vs'.length) ∗ sl2 ↦*{dq} vs' }} := by
  wp_start as ⟨Hs1, Hs2⟩
  ihave %Hlen1 := own_slice_len _ _ _ $$ Hs1
  ihave %Hlen2 := own_slice_len _ _ _ $$ Hs2
  wp_auto
  ihave IH : (∃ i : w64,
      "Hs1" ∷ sl ↦* (vs'.take (sint.nat i) ++ vs.drop (sint.nat i)) ∗
      "Hs2" ∷ sl2 ↦*{dq} vs' ∗
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧ sint.Z i ≤ sint.Z sl2.len⌝ : IProp GF)
    $$ [Hs1 Hs2 i]
  · iexists (zero_val w64)
    have h0 : sint.nat (zero_val w64 : w64) = 0 := rfl
    simp only [h0, List.take_zero, List.drop_zero, List.nil_append]
    iframe
    ipureintro; simp only [zero_val, ZeroVal.zero_val_def]; word
  wp_for IH
  wp_if_destruct
  · rename_i Hif1
    wp_if_destruct
    · rename_i Hif2
      rw [ite_eq_left ⟨Hi.1, Hif2⟩]
      wp_auto
      rw [ite_eq_left ⟨Hi.1, Hif⟩]
      list_elem vs' (sint.nat i) as y
      wp_apply wp_load_slice_index sl2 (sint.Z i) vs' dq y Hi.1 $$ [Hs2] with Hs2
      · isplitl [Hs2]
        · iexact Hs2
        · ipureintro; exact Hy_lookup
      wp_apply wp_store_slice_index sl (sint.Z i) _ y $$ [Hs1] with Hs1
      · iframe Hs1; ipureintro; simp only [List.length_append, List.length_take, List.length_drop]; word
      wp_for_post
      iframe
      iexists (i + W64 1)
      have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      have hz : (sint.Z i).toNat = sint.nat i := rfl
      rw [hn, ← list_copy_step vs vs' (sint.nat i) y (by word) Hy_lookup, ← hz]
      iframe
      ipureintro; word
    · iapply HΦ
      have heq : vs'.take (sint.nat i) ++ vs.drop (sint.nat i) =
          vs'.take vs.length ++ vs.drop vs'.length := by
        have h1 : sint.nat i = vs'.length := by word
        rw [h1, List.take_length, List.take_of_length_le (by word)]
      rw [heq]
      iframe
      ipureintro; word
  · iapply HΦ
    have heq : vs'.take (sint.nat i) ++ vs.drop (sint.nat i) =
        vs'.take vs.length ++ vs.drop vs'.length := by
      have h1 : sint.nat i = vs.length := by word
      rw [h1, List.drop_length, List.drop_of_length_le (by word)]
    rw [heq]
    iframe
    ipureintro; word

theorem wp_slice_clear {st t : go.type} [st ↓u go.SliceType t] [IntoValTyped (GF := GF) V t]
    (sl : slice.t) (vs : List V) :
    {{ (sl ↦* vs : IProp GF) }}
      (App (Val #(functions go.clear [st])) (Val #sl)) @ s; E
    {{ RET #(); sl ↦* List.replicate vs.length (zero_val V) }} := by
  wp_start as Hs
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  wp_apply wp_slice_make2 (V := V) sl.len $$ %(Hlen.2) with %zsl ⟨Hz, _⟩
  wp_apply wp_slice_copy sl vs zsl (List.replicate (sint.nat sl.len) (zero_val V)) (DFrac.own 1) $$ [Hs Hz] with %n ⟨%Hn, Hs, _⟩
  · iframe Hs Hz
  iapply HΦ
  have heq : (List.replicate (sint.nat sl.len) (zero_val V)).take vs.length ++
      vs.drop (List.replicate (sint.nat sl.len) (zero_val V)).length =
      List.replicate vs.length (zero_val V) := by
    rw [List.length_replicate, ← Hlen.1, List.drop_length, List.append_nil, List.take_replicate,
      Nat.min_self]
  rw [heq]
  iexact Hs

theorem own_slice_update_to_dfrac (dq : DFrac) (sl : slice.t) (vs : List V) (hvalid : ✓ dq) :
    (sl ↦* vs : IProp GF) ⊢ |==> sl ↦*{dq} vs :=
  dfractional_update_to_dfrac (fun dq => sl ↦*{dq} vs) dq hvalid

set_option linter.iris.style.nameCheck false in
theorem wp__new_cap (l : w64) :
    {{ (True : IProp GF) }} (App (Val slice._new_cap) (Val #l)) @ s; E
    {{ (cap : w64), RET #cap; ⌜sint.Z l ≤ sint.Z cap⌝ }} := by
  iintro %Φ _ HΦ
  wp_call
  wp_apply wp_ArbitraryInt with %x _
  wp_if_destruct
  · iapply HΦ; ipureintro; word
  · iapply HΦ; ipureintro; word

theorem wp_slice_append {st t : go.type} [st ↓u go.SliceType t] [IntoValTyped (GF := GF) V t]
    (sl : slice.t) (vs : List V) (sl2 : slice.t) (vs' : List V) (dq : DFrac) :
    {{ (sl ↦* vs ∗ own_slice_cap V sl (DFrac.own 1) ∗ sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.append [st])) (Val #sl)) (Val #sl2)) @ s; E
    {{ (s' : slice.t), RET #s';
        s' ↦* (vs ++ vs') ∗ own_slice_cap V s' (DFrac.own 1) ∗ sl2 ↦*{dq} vs' }} := by
  wp_start as ⟨Hs, Hcap, Hs2⟩
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  ihave %Hlen2 := own_slice_len _ _ _ $$ Hs2
  ihave %Hwf1 := own_slice_wf _ _ _ $$ Hs
  ihave %Hwf2 := own_slice_wf _ _ _ $$ Hs2
  wp_apply wp_sum_assume_no_overflow_signed with %Hoverflow
  wp_if_destruct
  · rw [ite_eq_left ⟨by word, by word, Hif⟩]
    wp_auto
    rw [ite_eq_left (by simp only [slice.slice]; word)]
    wp_auto
    rw [slice_slice sl (W64 0) (sl.len + sl2.len) sl.len (sl.len + sl2.len) (by word)]
    have h0 : ∀ x : w64, W64 0 + x = x := fun x => by word
    simp only [h0]
    icases own_slice_slice_into_capacity sl.len (sl.len + sl2.len) sl vs $$ [Hs Hcap]
      with ⟨%vs'', Hs, Hs_new, Hcap⟩
    · iframe Hs Hcap; ipureintro; word
    ihave %Hlen3 := own_slice_len _ _ _ $$ Hs_new
    wp_apply wp_slice_copy _ _ sl2 vs' dq $$ [Hs_new Hs2] with %n ⟨%Hn, Hs_new, Hs2⟩
    · iframe Hs_new Hs2
    have hd : (List.drop (sint.nat sl.len) (vs ++ vs'')).length = vs'.length := by
      rw [Hlen3.1]; simp only [slice.slice]; word
    have ht : (vs ++ vs'').take (sint.nat sl.len) = vs := by
      rw [show sint.nat sl.len = vs.length from Hlen.1.symm, List.take_left]
    rw [hd, List.take_length, List.drop_of_length_le (l := List.drop (sint.nat sl.len) (vs ++ vs''))
      (i := vs'.length) (by omega), List.append_nil, ht]
    iapply HΦ
    iframe Hs2
    isplitl [Hs Hs_new]
    · iapply own_slice_combine sl.len sl _ vs vs' (W64 0) (sl.len + sl2.len)
        ⟨by word, by word, by word, by word⟩ $$ Hs Hs_new
    · iapply own_slice_cap_slice_change_first sl sl.len (W64 0) (sl.len + sl2.len) _
        ⟨Hif, by word, by word, by word, by word⟩ $$ Hcap
  · wp_apply wp__new_cap with %cap %Hcap_ge
    wp_apply wp_slice_make3 (V := V) (sl.len + sl2.len) cap ⟨by word, Hcap_ge⟩
      with %nsl ⟨Hnew, Hnew_cap, %Hcap⟩
    ihave %Hsl_wf := own_slice_wf _ _ _ $$ Hnew
    ihave %Hsl_len := own_slice_len _ _ _ $$ Hnew
    simp only [List.length_replicate] at Hsl_len
    wp_apply wp_slice_copy nsl _ sl vs (DFrac.own 1) $$ [Hnew Hs] with %n' ⟨%Hn', Hnew, Hs⟩
    · iframe Hnew Hs
    rw [ite_eq_left ⟨by word, by word, by rw [Hcap]; exact Hcap_ge⟩]
    wp_auto
    icases (own_slice_slice sl.len (sl.len + sl2.len) nsl _ _ ⟨by word, by word, by word⟩).1 $$ Hnew
      with ⟨Hnew1, Hnew2, _⟩
    wp_apply wp_slice_copy _ _ sl2 vs' dq $$ [Hnew2 Hs2] with %n'' ⟨%Hn'', Hnew2, Hs2⟩
    · iframe Hnew2 Hs2
    iapply HΦ
    iframe Hs2 Hnew_cap
    have hN : sint.nat (sl.len + sl2.len) = vs.length + vs'.length := by word
    have ha : (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
        (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length).take
          (sint.nat sl.len) = vs := by
      rw [List.length_replicate, List.take_of_length_le (l := vs) (i := sint.nat (sl.len + sl2.len)) (by omega),
        show sint.nat sl.len = vs.length from Hlen.1.symm, List.take_left]
    have hb : (subslice (sint.nat sl.len) (sint.nat (sl.len + sl2.len))
        (vs.take (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).length ++
          (List.replicate (sint.nat (sl.len + sl2.len)) (zero_val V)).drop vs.length)).length =
        vs'.length := by
      simp only [subslice, List.length_drop, List.length_take, List.length_append,
        List.length_replicate]
      omega
    rw [ha, hb, List.take_length, List.drop_of_length_le (i := vs'.length) (by omega),
      List.append_nil]
    have hnl : nsl.len = sl.len + sl2.len := by word
    have hs : slice.slice nsl V (W64 0) (sl.len + sl2.len) = nsl := by
      rw [← hnl]; exact (slice_slice_trivial nsl).symm
    ihave H := own_slice_combine sl.len nsl _ vs vs' (W64 0) (sl.len + sl2.len)
      ⟨by word, by word, by word, by word⟩ $$ Hnew1 Hnew2
    rw [hs]
    iexact H


theorem wp_slice_literal {st t : go.type} [IntoValTyped (GF := GF) V t] [st ↓u go.SliceType t]
    (l : List V) (kvs : List keyed_element) (Φ : val → IProp GF) :
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType (go.array_literal_size kvs) t))))
          (Val (LiteralValueV kvs))) @ s; E
      {{ v, ⌜v = #(array.mk (go.array_literal_size kvs) l)⌝ ∗
        (∀ sl_ptr : loc,
          (slice.mk sl_ptr (W64 (go.array_literal_size kvs)) (W64 (go.array_literal_size kvs)) ↦* l ∗
            own_slice_cap V (slice.mk sl_ptr (W64 (go.array_literal_size kvs))
              (W64 (go.array_literal_size kvs))) (DFrac.own 1)) -∗
          Φ #(slice.mk sl_ptr (W64 (go.array_literal_size kvs)) (W64 (go.array_literal_size kvs)))) }} ⊢
    WP (App (Val (GoInstruction (CompositeLiteral st))) (Val (LiteralValueV kvs))) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_pures
  by_cases hlen : go.array_literal_size kvs < 2 ^ 63
  · rw [ite_eq_left hlen]
    wp_pures
    wp_alloc_auto
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.ArrayType _ t)))) (Val (LiteralValueV kvs)))
    wp_apply_core wp_wand $$ HΦ
    iintro %v ⟨%Hv, HΦ⟩
    subst Hv
    wp_auto
    have h0 : 0 ≤ go.array_literal_size kvs := by
      unfold go.array_literal_size; split; omega
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    have hz : W64 (go.array_literal_size kvs) - W64 0 = W64 (go.array_literal_size kvs) := by word
    simp only [show sint.Z (W64 0) = 0 from rfl, go.array_index_ref_0, hz]
    wp_pures
    ihave %Hlen := array_len _ _ _ _ $$ tmp
    iapply HΦ
    isplitl [tmp]
    · iapply slice_array tmp_ptr _ (array.mk (go.array_literal_size kvs) l) (by simp only; omega)
      iexact tmp
    · iapply own_slice_cap_empty _ rfl (by simp only; word)
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

end wps

end Perennial
