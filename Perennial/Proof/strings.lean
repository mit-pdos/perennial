/-
Specs for the Go `strings` package.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.strings
public import Perennial.GeneratedProof.strings
public import Perennial.Proof.internal.abi
public import Perennial.Proof.internal.bytealg
public import Perennial.Proof.internal.stringslite
public import Perennial.Proof.unicode.utf8
public import Perennial.Proof.unsafe

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strings

/-- Model for Go's `unicode.IsSpace` for ASCII-range bytes. Based on
https://cs.opensource.google/go/go/+/refs/tags/go1.26.1:src/strings/strings.go;l=377 -/
def isAsciiSpace (b : w8) : Bool :=
  [9#8,    -- \t  (0x09)
   10#8,   -- \n  (0x0A)
   11#8,   -- \v  (0x0B)
   12#8,   -- \f  (0x0C)
   13#8,   -- \r  (0x0D)
   32#8    -- space (0x20)
  ].contains b

def splitFieldsAux : GoString → Option GoString → List GoString
  | [], w => match w with | none => [] | some w => [w]
  | x :: s, w =>
    if isAsciiSpace x then
      match w with
      | none => splitFieldsAux s none
      | some w => w :: splitFieldsAux s none
    else splitFieldsAux s (some (w.getD [] ++ [x]))

def splitFields (s : GoString) : List GoString := splitFieldsAux s none

/-! Tests of `splitFields`, which is part of the `wp_Fields` axiom. -/

example : splitFields go!"hello" = [go!"hello"] := by decide

example : splitFields go!"   hello world" = [go!"hello", go!"world"] := by decide

example : splitFields go!"hello world" = [go!"hello", go!"world"] := by decide

example : splitFields go!"" = [] := by decide

def bsTab : w8 := 9#8
def bsNl : w8 := 10#8
def bsCr : w8 := 13#8
def bsSp : w8 := 32#8

def helloWorldWs : GoString :=
  [bsSp, bsTab] ++ go!"hello" ++ [bsNl] ++ go!"world" ++ [bsCr, bsSp]

example : splitFields helloWorldWs = [go!"hello", go!"world"] := by decide

example : splitFields go!"  hello\tthere\ngeneral\rkenobi " =
    [go!"hello", go!"there", go!"general", go!"kenobi"] := by decide

/-! ## `Count` and `Split` -/

open internal.bytealg (firstOcc firstOcc_eq_some_iff firstOcc_eq_none_iff)

/-- The first occurrence of `sep` ends within `s`. -/
theorem firstOcc_end_le (s sep : GoString) (k : Nat) (h : firstOcc s sep = some k) :
    k + sep.length ≤ s.length := by
  obtain ⟨hk, hp, -⟩ := (firstOcc_eq_some_iff s sep k).1 h
  have := hp.length_le
  simp only [List.length_drop] at this
  omega

/-- The number of non-overlapping occurrences of `sep` in `s`, found left to right, for a
non-empty `sep` (what Go's `Count(s, sep)` returns then). -/
def countOcc (s sep : GoString) : Nat :=
  if hsep : sep = [] then 0 else
  match h : firstOcc s sep with
  | none => 0
  | some k => countOcc (s.drop (k + sep.length)) sep + 1
termination_by s.length
decreasing_by
  have := firstOcc_end_le s sep k h
  have := List.length_pos_iff.2 hsep
  simp only [List.length_drop]
  omega

/-- What `strings.Split(s, sep)` returns, for a non-empty `sep`: the substrings of `s` between
the occurrences of `sep`, found left to right without overlap. `split "" sep = [""]`, and a
trailing `sep` gives a trailing empty field. -/
def split (s sep : GoString) : List GoString :=
  if hsep : sep = [] then [s] else
  match h : firstOcc s sep with
  | none => [s]
  | some k => s.take k :: split (s.drop (k + sep.length)) sep
termination_by s.length
decreasing_by
  have := firstOcc_end_le s sep k h
  have := List.length_pos_iff.2 hsep
  simp only [List.length_drop]
  omega

theorem split_none (s sep : GoString) (hsep : sep ≠ []) (h : firstOcc s sep = none) :
    split s sep = [s] := by
  rw [split]; simp only [hsep, ↓reduceDIte]
  split <;> simp_all

theorem split_some (s sep : GoString) (hsep : sep ≠ []) (k : Nat) (h : firstOcc s sep = some k) :
    split s sep = s.take k :: split (s.drop (k + sep.length)) sep := by
  rw [split]; simp only [hsep, ↓reduceDIte]
  split <;> simp_all

theorem countOcc_none (s sep : GoString) (hsep : sep ≠ []) (h : firstOcc s sep = none) :
    countOcc s sep = 0 := by
  rw [countOcc]; simp only [hsep, ↓reduceDIte]
  split <;> simp_all

theorem countOcc_some (s sep : GoString) (hsep : sep ≠ []) (k : Nat)
    (h : firstOcc s sep = some k) :
    countOcc s sep = countOcc (s.drop (k + sep.length)) sep + 1 := by
  rw [countOcc]; simp only [hsep, ↓reduceDIte]
  split <;> simp_all

/-! Tests of `split`. -/

example : split go!"a/b" go!"/" = [go!"a", go!"b"] := by
  rw [split_some _ _ (by simp) 1 (by decide), split_none _ _ (by simp) (by decide)]; rfl
example : split go!"" go!"/" = [go!""] := split_none _ _ (by simp) (by decide)
example : split go!"a/" go!"/" = [go!"a", go!""] := by
  rw [split_some _ _ (by simp) 1 (by decide), split_none _ _ (by simp) (by decide)]; rfl
example : split go!"x//ab///" go!"//" = [go!"x", go!"ab", go!"/"] := by
  rw [split_some _ _ (by simp) 1 (by decide), split_some _ _ (by simp) 2 (by decide),
    split_none _ _ (by simp) (by decide)]; rfl

/-- `strings.Split` returns at least one field. -/
theorem split_ne_nil (s sep : GoString) : split s sep ≠ [] := by
  rw [split]
  split
  · simp
  · split <;> simp

/-- `strings.Split` returns `Count + 1` fields. -/
theorem split_length (s sep : GoString) (hsep : sep ≠ []) :
    (split s sep).length = countOcc s sep + 1 := by
  rcases h : firstOcc s sep with _ | k
  · rw [split_none s sep hsep h, countOcc_none s sep hsep h]; rfl
  · rw [split_some s sep hsep k h, countOcc_some s sep hsep k h, List.length_cons,
      split_length (s.drop (k + sep.length)) sep hsep]
termination_by s.length
decreasing_by
  have := firstOcc_end_le s sep k h
  have := List.length_pos_iff.2 hsep
  simp only [List.length_drop]
  omega

/-- At most one occurrence per byte. -/
theorem countOcc_le (s sep : GoString) (hsep : sep ≠ []) : countOcc s sep ≤ s.length := by
  rcases h : firstOcc s sep with _ | k
  · rw [countOcc_none s sep hsep h]; omega
  · rw [countOcc_some s sep hsep k h]
    have := countOcc_le (s.drop (k + sep.length)) sep hsep
    have := firstOcc_end_le s sep k h
    have := List.length_pos_iff.2 hsep
    simp only [List.length_drop] at *
    omega
termination_by s.length
decreasing_by
  have := firstOcc_end_le s sep k h
  have := List.length_pos_iff.2 hsep
  simp only [List.length_drop]
  omega

/-- The occurrences of a single byte are its copies. -/
theorem countOcc_singleton (s : GoString) (c : w8) : countOcc s [c] = s.count c := by
  rcases h : firstOcc s [c] with _ | k
  · rw [countOcc_none s [c] (by simp) h, eq_comm, List.count_eq_zero]
    intro hc
    obtain ⟨i, hi, hsi⟩ := List.getElem_of_mem hc
    exact (firstOcc_eq_none_iff s [c]).1 h i (by omega)
      ((internal.bytealg.occ_singleton_iff s c i).2 (by rw [List.getElem?_eq_getElem hi, hsi]))
  · rw [countOcc_some s [c] (by simp) k h, List.length_singleton,
      countOcc_singleton (s.drop (k + 1)) c]
    obtain ⟨hk, hp, hmin⟩ := (firstOcc_eq_some_iff s [c] k).1 h
    have hsk := (internal.bytealg.occ_singleton_iff s c k).1 hp
    have hkl : k < s.length := by
      rcases Nat.lt_or_ge k s.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hsk; cases hsk
    have hsk' : s[k] = c := by rw [List.getElem?_eq_getElem hkl] at hsk; cases hsk; rfl
    have htake : (s.take k).count c = 0 := by
      rw [List.count_eq_zero]
      intro hc
      obtain ⟨i, hi, hsi⟩ := List.getElem_of_mem hc
      simp only [List.length_take] at hi
      apply hmin i (by omega)
      rw [internal.bytealg.occ_singleton_iff, ← hsi, List.getElem_take]
      exact List.getElem?_eq_getElem (by omega)
    have hsplit : s.count c = (s.take k).count c + (s.drop k).count c := by
      rw [← List.count_append, List.take_append_drop]
    rw [hsplit, htake, List.drop_eq_getElem_cons hkl, hsk', List.count_cons_self]
    omega
termination_by s.length
decreasing_by
  have := firstOcc_end_le s [c] k h
  simp only [List.length_drop, List.length_singleton] at *
  omega

/-- The fields of `split s sep` joined by `sep` (as `strings.Join` joins them) give `s` back. -/
theorem intercalate_split (s sep : GoString) (hsep : sep ≠ []) :
    sep.intercalate (split s sep) = s := by
  rcases h : firstOcc s sep with _ | k
  · rw [split_none s sep hsep h]; simp
  · rw [split_some s sep hsep k h, List.intercalate_cons_of_ne_nil (split_ne_nil _ _),
      intercalate_split (s.drop (k + sep.length)) sep hsep]
    obtain ⟨-, ⟨t, ht⟩, -⟩ := (firstOcc_eq_some_iff s sep k).1 h
    have : s.drop (k + sep.length) = t := by
      rw [← List.drop_drop, ← ht, List.drop_left]
    rw [this, List.append_assoc, ht, List.take_append_drop]
termination_by s.length
decreasing_by
  have := firstOcc_end_le s sep k h
  have := List.length_pos_iff.2 hsep
  simp only [List.length_drop]
  omega

/-- No field of `split s sep` contains `sep`, for a non-empty `sep`. -/
theorem split_no_infix (s sep : GoString) (hsep : sep ≠ []) :
    ∀ f ∈ split s sep, ¬ sep <:+: f := by
  rcases h : firstOcc s sep with _ | k
  · rw [split_none s sep hsep h]
    intro f hf ⟨u, v, huv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    apply (firstOcc_eq_none_iff f sep).1 h u.length (by rw [← huv]; simp <;> omega)
    rw [← huv]
    simp
  · rw [split_some s sep hsep k h]
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · rintro ⟨u, v, huv⟩
      obtain ⟨hk, -, hmin⟩ := (firstOcc_eq_some_iff s sep k).1 h
      have hlen : u.length + sep.length ≤ k := by
        have := congrArg List.length huv
        simp only [List.length_append, List.length_take] at this
        omega
      apply hmin u.length (by have := List.length_pos_iff.2 hsep; omega)
      rw [← List.take_append_drop k s, List.drop_append_of_le_length (by simp; omega), ← huv]
      simp only [List.append_assoc, List.drop_left]
      exact List.prefix_append _ _
    · exact split_no_infix (s.drop (k + sep.length)) sep hsep f hf
termination_by s.length
decreasing_by
  have := firstOcc_end_le s sep k h
  have := List.length_pos_iff.2 hsep
  simp only [List.length_drop]
  omega

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.strings :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strings :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.strings get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.strings }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) asciiSpace (go.ArrayType 256 go.uint8) with H
  wp_apply internal.stringslite.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown
    as ⟨Hown, #Hstringslite⟩
  wp_apply «unsafe».wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hunsafe⟩
  wp_apply unicode.utf8.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hutf8⟩
  wp_apply internal.bytealg.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hbytealg⟩
  wp_apply internal.abi.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Habi⟩
  iframe Hown
  is_pkg_init_finish

/-! ## `strings.Builder` -/

/-- `b` points to a `strings.Builder` that holds the bytes `s` and is used through `b` (its
`addr`, which `copyCheck` sets to the receiver on first use, is `b` or not yet set). -/
def ownBuilder (b : Loc) (s : GoString) : IProp GF :=
  iprop(∃ (addr : Loc) (buf : GoSlice),
    b ↦ ({ addr' := addr, buf' := buf } : Builder) ∗ ⌜addr = null ∨ addr = b⌝ ∗
    buf ↦* s ∗ ownSliceCap w8 buf (DFrac.own 1))

/-- `b.copyCheck()`, for a builder not copied by value (its `addr` is unset or `b`): sets `addr`
to `b`. -/
theorem Builder.wp_copyCheck (b addr : Loc) (buf : GoSlice) (Haddr : addr = null ∨ addr = b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        b ↦ ({ addr' := addr, buf' := buf } : Builder) }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"copyCheck")) (Val #()))
    {{ RET #(); b ↦ ({ addr' := b, buf' := buf } : Builder) }} := by
  wp_start as Hb
  wp_auto
  by_cases hnull : addr = null
  · rw [decide_eq_true hnull]
    wp_auto
    wp_apply internal.abi.wp_NoEscape
    iapply HΦ
    iexact Hb
  · rw [decide_eq_false hnull]
    have hb : addr = b := Haddr.resolve_left hnull
    subst hb
    wp_auto
    iapply HΦ
    iexact Hb

/-- The receiver's type in the model of `Builder.String` (`TrustedCode/strings.lean`), which is
below `Builder.ty`'s definition. -/
theorem Builder_ty_eq : (go.GoType.Named go!"strings.Builder" [] : go.GoType) = Builder.ty := by
  unfold Builder.ty; rfl

/-- A zero `strings.Builder` (`var b strings.Builder`) holds no bytes. -/
theorem ownBuilder_zero (b : Loc) :
    b ↦ zero_val Builder ⊢ ownBuilder (GF := GF) b [] := by
  iintro Hb
  unfold ownBuilder
  iexists null, slice.nil
  iframe Hb
  isplitl []
  · ipureintro; exact Or.inl rfl
  isplitl []
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil

/-- `b.WriteString(t)` appends `t`, returning `len(t)` and a nil error. -/
theorem Builder.wp_WriteString (b : Loc) (s t : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ ownBuilder b s }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"WriteString")) (Val #t))
    {{ RET (PairV #(W64 t.length) #interface.nil); ownBuilder b (s ++ t) }} := by
  wp_start as Hb
  unfold ownBuilder
  icases Hb with ⟨%addr, %buf, Hb, %Haddr, Hs, Hcap⟩
  wp_auto
  wp_apply Builder.wp_copyCheck b addr buf Haddr $$ [$Hb] as Hb
  wp_apply wp_string_to_bytes as %tsl ⟨Htsl, -⟩
  wp_apply wp_slice_append (V := w8) (t := go.byte) buf s tsl t (DFrac.own 1)
    $$ [Hs Hcap Htsl] as %buf' ⟨Hs', Hcap', -⟩
  · iframe
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  iapply HΦ
  iexists b, buf'
  iframe
  ipureintro
  exact Or.inr rfl

/-- `b.grow(n)` moves the bytes to a new buffer of `2 * cap + n` bytes, which must not exceed
`maxAlloc` (`MakeNoZero` panics there). -/
theorem Builder.wp_grow (b addr : Loc) (buf : GoSlice) (s : GoString) (n : w64)
    (Hn : 0 ≤ sint.Z n ∧ 2 * sint.Z buf.cap + sint.Z n ≤ internal.bytealg.maxAlloc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        b ↦ ({ addr' := addr, buf' := buf } : Builder) ∗
        buf ↦* s ∗ ownSliceCap w8 buf (DFrac.own 1) }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"grow")) (Val #n))
    {{ RET #(); ∃ buf' : GoSlice, b ↦ ({ addr' := addr, buf' := buf' } : Builder) ∗
        buf' ↦* s ∗ ownSliceCap w8 buf' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hs, Hcap⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  have Hmax := Hn.2
  unfold internal.bytealg.maxAlloc at Hmax
  wp_auto
  have Hm : sint.Z (W64 2 * buf.cap + n) = 2 * sint.Z buf.cap + sint.Z n := by word
  wp_apply internal.bytealg.wp_MakeNoZero (W64 2 * buf.cap + n)
    ⟨by rw [Hm]; omega, by rw [Hm]; exact Hn.2⟩ as %sl ⟨Hsl, Hslcap⟩
  ihave %Hsllen := ownSlice_len $$ Hsl
  ihave %Hslwf := ownSlice_wf $$ Hsl
  simp only [List.length_replicate] at Hsllen
  have Hk : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z buf.len ∧ sint.Z buf.len ≤ sint.Z sl.len :=
    ⟨by word, by word, by word⟩
  rw [ite_eq_left ⟨Hk.1, Hk.2.1, by omega⟩]
  icases ownSlice_slice_with_cap (W64 0) buf.len sl _ Hk $$ [Hsl Hslcap] with ⟨-, Hnew, Hnewcap⟩
  · iframe
  wp_auto
  wp_apply wp_slice_copy (V := w8) (t := go.byte) _ _ buf s (DFrac.own 1) $$ [Hnew Hs]
    as %m ⟨-, Hnew, Hs⟩
  · iframe
  wp_auto
  iapply HΦ
  iexists _
  iframe
  have Hsub : (subslice (sint.nat (W64 0)) (sint.nat buf.len)
      (List.replicate (sint.nat (W64 2 * buf.cap + n)) (W8 0))).length = s.length := by
    simp only [subslice, List.length_take, List.length_drop, List.length_replicate]; word
  rw [Hsub, List.take_length, List.drop_eq_nil_of_le (Nat.le_of_eq Hsub), List.append_nil]
  iexact Hnew

/-- `b.Grow(n)`, for `n ≥ 0`. When the buffer has fewer than `n` free bytes, `grow` allocates
`2 * cap + n` bytes, which must not exceed `maxAlloc` (Go panics there). -/
theorem Builder.wp_Grow (b addr : Loc) (buf : GoSlice) (s : GoString) (n : w64)
    (Haddr : addr = null ∨ addr = b) (Hn : 0 ≤ sint.Z n)
    (Hgrow : sint.Z buf.cap - sint.Z buf.len < sint.Z n →
      2 * sint.Z buf.cap + sint.Z n ≤ internal.bytealg.maxAlloc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        b ↦ ({ addr' := addr, buf' := buf } : Builder) ∗
        buf ↦* s ∗ ownSliceCap w8 buf (DFrac.own 1) }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"Grow")) (Val #n))
    {{ RET #(); ownBuilder b s }} := by
  wp_start as ⟨Hb, Hs, Hcap⟩
  ihave %Hwf := ownSlice_wf $$ Hs
  wp_auto
  wp_apply Builder.wp_copyCheck b addr buf Haddr $$ [$Hb] as Hb
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by word)]
  wp_auto
  by_cases hg : sint.Z (buf.cap - buf.len) < sint.Z n
  · rw [decide_eq_true hg]
    wp_auto
    wp_apply Builder.wp_grow b b buf s n ⟨Hn, Hgrow (by word)⟩ $$ [Hb Hs Hcap]
      as ⟨%buf', Hb, Hs, Hcap⟩
    · iframe
    iapply HΦ
    unfold ownBuilder
    iexists b, buf'
    iframe
    ipureintro
    exact Or.inr rfl
  · rw [decide_eq_false hg]
    wp_auto
    iapply HΦ
    unfold ownBuilder
    iexists b, buf
    iframe
    ipureintro
    exact Or.inr rfl

/-- A byte's points-to, as a heap points-to. -/
theorem typedPointsto_w8_heap (l : Loc) (v : w8) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ heapPointsto l dq #v := by
  rw [typedPointsto_unseal_eq]
  simp only [typedPointstoDef_heap]
  iintro ⟨H, -⟩
  iexact H

/-- `lockBytes buf i` (`TrustedCode/strings.lean`), given the bytes of `buf` from index `i` on,
read-locks them and keeps them. -/
theorem Builder.wp_lockBytes (buf : GoSlice) (dq : DFrac) :
    ∀ (k : Nat) (i : w64) (vs : List w8), vs.length = k → 0 ≤ sint.Z i →
    sint.Z i + vs.length = sint.Z buf.len →
    {{ (arrayElems (GF := GF) (arrayIndexRef w8 (sint.Z i) buf.ptr) vs dq) }}
      (App (App (Val Builder.String.lockBytes) (Val #buf)) (Val #i))
    {{ RET #(); True }} := by
  intro k
  induction k with
  | zero =>
    intro i vs hk hi hlen
    iintro %Φ _ HΦ
    wp_call
    rw [decide_eq_false (by rw [List.length_eq_zero_iff.1 hk] at hlen; simp at hlen; omega)]
    wp_pures
    iapply HΦ; itrivial
  | succ k ih =>
    intro i vs hk hi hlen
    iintro %Φ Hl HΦ
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hk
      | cons v vs' => exact ⟨v, vs', rfl⟩
    simp only [List.length_cons] at hk hlen
    have hlt : sint.Z i < sint.Z buf.len := by omega
    wp_call
    rw [decide_eq_true hlt]
    wp_pures
    rw [ite_eq_left ⟨hi, hlt⟩]
    icases (arrayElems_cons _ v vs' _).1 $$ Hl with ⟨Hv, Hl⟩
    rw [go.arrayIndexRef_0]
    ihave Hv := typedPointsto_w8_heap _ _ _ $$ Hv
    simp only [sliceIndexRef]
    have hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
    have hrec := ih (i + W64 1) vs' (by omega) (by omega) (by push_cast at hlen; omega)
    rw [hi1, go.arrayIndexRef_add] at hrec
    wp_apply_core wp_start_read _ _ _ $$ Hv
    iintro ⟨-, -⟩
    wp_pures
    iapply hrec $$ Hl HΦ

/-- The bytes of `sl`, as element points-tos from its start. -/
theorem ownSlice_arrayElems (sl : GoSlice) (vs : List w8) (dq : DFrac) :
    (sl ↦*{dq} vs : IProp GF) ⊢ arrayElems (arrayIndexRef w8 0 sl.ptr) vs dq := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · obtain ⟨-, rfl⟩ := H
    unfold arrayElems; iapply BigSepL.bigSepL_nil.2; iempintro
  · rw [go.arrayIndexRef_0, typedPointsto_unseal]; unfold typedPointstoWrap
    simp only [TypedPointsto.typedPointstoDef]
    icases H with ⟨⟨-, H⟩, -⟩
    iexact H

/-- `b.String()` returns the bytes written. The model leaves them read-locked (so that a write
to them through a copy of the builder is stuck), so the builder is used up. -/
theorem Builder.wp_String (b : Loc) (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ ownBuilder b s }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"String")) (Val #()))
    {{ RET #s; True }} := by
  wp_start as Hb
  unfold ownBuilder
  icases Hb with ⟨%addr, %buf, Hb, %Haddr, Hs, Hcap⟩
  rw [Builder_ty_eq]
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave Hs' : iprop(buf ↦*{.own (1 : Qp).half} s ∗ buf ↦*{.own (1 : Qp).half} s) $$ [Hs]
  · iapply ((ownSlice_dfractional buf s).dfractional _ _).1
    rw [DFrac.op_own, Qp.half_add_half]; iexact Hs
  icases Hs' with ⟨Hs1, Hs2⟩
  ihave Hs1 := ownSlice_arrayElems _ _ _ $$ Hs1
  wp_apply Builder.wp_lockBytes buf _ s.length (W64 0) s rfl (by decide) (by word) $$ [Hs1]
  · rw [show sint.Z (W64 0) = 0 from rfl]; iexact Hs1
  wp_apply wp_bytes_to_string $$ Hs2 as -
  iapply HΦ; itrivial

/-- A join with one more element at the end. -/
theorem intercalate_snoc (sep : GoString) :
    ∀ (ys : List GoString) (x : GoString), ys ≠ [] →
      sep.intercalate (ys ++ [x]) = sep.intercalate ys ++ sep ++ x
  | [], _, h => absurd rfl h
  | [y], x, _ => by simp [List.intercalate]
  | y :: y' :: ys, x, _ => by
    have ih := intercalate_snoc sep (y' :: ys) x (List.cons_ne_nil _ _)
    simp only [List.cons_append, List.intercalate_cons_cons] at ih ⊢
    rw [ih]; simp only [List.append_assoc]

/-- One more element of a join: the first alone, then after a separator. -/
theorem intercalate_take_succ (sep : GoString) (xs : List GoString) (n : Nat) (x : GoString)
    (hn : n < xs.length) (hx : xs[n] = x) :
    sep.intercalate (xs.take (n + 1)) =
      if n = 0 then x else sep.intercalate (xs.take n) ++ sep ++ x := by
  rw [List.take_succ, List.getElem?_eq_getElem hn, hx]
  split
  · subst_vars
    cases xs with
    | nil => simp at hn
    | cons y ys => simp [List.intercalate]
  · have : xs.take n ≠ [] := by
      simp only [ne_eq, List.take_eq_nil_iff, not_or]
      exact ⟨by omega, List.ne_nil_of_length_pos (by omega)⟩
    simp only [Option.toList_some]
    exact intercalate_snoc sep _ x this

/-- The lengths of the first `j + 1` strings: those of the first `j`, and the next one's. -/
theorem sum_take_succ (xs : List GoString) (j : Nat) (h : j < xs.length) :
    ((xs.take (j + 1)).map List.length).sum = ((xs.take j).map List.length).sum + xs[j].length := by
  rw [List.take_succ, List.getElem?_eq_getElem h, List.map_append, List.sum_append]
  simp

theorem sum_take_le (xs : List GoString) (j : Nat) :
    ((xs.take j).map List.length).sum ≤ (xs.map List.length).sum := by
  conv => rhs; rw [← List.take_append_drop j xs]
  simp only [List.map_append, List.sum_append]
  omega

/-- The length of a join: the elements' lengths and one separator between each two. -/
theorem intercalate_length (sep : GoString) :
    ∀ xs : List GoString, xs ≠ [] →
      (sep.intercalate xs).length = sep.length * (xs.length - 1) + (xs.map List.length).sum
  | [], h => absurd rfl h
  | [x], _ => by simp [List.intercalate]
  | x :: y :: ys, _ => by
    have ih := intercalate_length sep (y :: ys) (List.cons_ne_nil _ _)
    simp only [List.intercalate_cons_cons, List.length_append, List.length_cons,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- When `strings.Join(xs, sep)` returns instead of panicking: at most one element, or a join
of at most `maxAlloc` bytes (`internal/bytealg.maxAlloc`, Go's largest allocation on 64-bit
Linux). For two or more elements Go sums the lengths and allocates the result at once
(`Builder.Grow`, then `bytealg.MakeNoZero`), so it panics otherwise: "strings: Join output
length overflow" when the sum overflows `int`, "makeslice: len out of range" when it exceeds
`maxAlloc`. Both happen before anything is allocated, so a program can reach them (with many
aliased elements). The bound implies that the overflow checks pass, so this is exactly Go's
condition. -/
def JoinFits (xs : List GoString) (sep : GoString) : Prop :=
  xs.length ≤ 1 ∨ ((sep.intercalate xs).length : Int) ≤ internal.bytealg.maxAlloc

/-- `strings.Join(elems, sep)`: the elements of `elems` separated by `sep`, when the result fits
(`JoinFits`; Go panics otherwise). Proved from goose's translation of Go's `Join` and of the
`strings.Builder` methods it calls, with `Builder.String`, `internal/bytealg.MakeNoZero` and
`internal/abi.NoEscape` trusted (`Perennial/TrustedCode`). -/
theorem wp_Join (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString)
    (Hfits : JoinFits xs sep) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs }}
      (App (App (Val (@! Join)) (Val #elems)) (Val #sep))
    {{ RET #(sep.intercalate xs); elems ↦*{dq} xs }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  by_cases H0 : xs = []
  · subst H0
    rw [decide_eq_true (show elems.len = W64 0 by simp at Hlen; word)]
    wp_auto
    rw [show sep.intercalate ([] : List GoString) = [] from rfl]
    iapply HΦ
    iexact Hs
  rw [decide_eq_false (show ¬ elems.len = W64 0 by
    intro h; apply H0; apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, h]; rfl)]
  wp_auto
  obtain ⟨x0, xs', rfl⟩ : ∃ x0 xs', xs = x0 :: xs' := List.exists_cons_of_ne_nil H0
  by_cases H1 : xs' = []
  · subst H1
    rw [decide_eq_true (show elems.len = W64 1 by simp at Hlen; word)]
    wp_auto
    rw [ite_eq_left ⟨by word, by simp at Hlen; word⟩]
    wp_apply wp_load_slice_index elems (sint.Z (W64 0)) _ dq x0 (by word) $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    wp_auto
    rw [show sep.intercalate [x0] = x0 by simp [List.intercalate]]
    iapply HΦ
    iexact Hs
  rw [decide_eq_false (show ¬ elems.len = W64 1 by
    intro h; apply H1; apply List.eq_nil_of_length_eq_zero; simp at Hlen; word)]
  wp_auto
  unfold maxInt
  -- the join's length: `sep` between each two of the `k ≥ 2` elements, and the elements
  have Hk : 2 ≤ (x0 :: xs').length := by
    obtain ⟨x1, xs'', rfl⟩ := List.exists_cons_of_ne_nil H1; simp
  have HL := intercalate_length sep (x0 :: xs') H0
  have Hfits' : ((sep.intercalate (x0 :: xs')).length : Int) ≤ 2 ^ 48 := by
    rcases Hfits with h | h
    · omega
    · exact h
  have Hsepk : sep.length * ((x0 :: xs').length - 1) ≤ 2 ^ 48 := by omega
  have Hsum : ((x0 :: xs').map List.length).sum ≤ 2 ^ 48 := by omega
  obtain ⟨m, Hm⟩ : ∃ m : Nat, (x0 :: xs').length - 1 = m := ⟨_, rfl⟩
  rw [Hm] at Hsepk
  have Hmi : ((x0 :: xs').length : Int) - 1 = (m : Int) := by omega
  have Hm1 : sint.Z (elems.len - W64 1) = (m : Int) := by have := Hlen.1; word
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hseplen
  wp_if_destruct
  focus
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    -- `len(sep) < maxInt / (len(elems) - 1)`: `sep` occurs `k - 1 ≤ 2^48` times in the join
    have Hsep1 : 1 ≤ sep.length := by have := Hif; word
    have Hsl : sint.Z (W64 (sep.length : Nat)) = (sep.length : Int) := by word
    have Hm_le : m ≤ sep.length * m := Nat.le_mul_of_pos_left m Hsep1
    have Hlt : ((sep.length : Int) + 1) * (m : Int) ≤ 2 ^ 63 - 1 := by
      have h1 : ((sep.length * m : Nat) : Int) = (sep.length : Int) * (m : Int) := Int.natCast_mul _ _
      have h2 : ((sep.length : Int) + 1) * (m : Int) = (sep.length : Int) * (m : Int) + m := by
        rw [Int.add_mul, Int.one_mul]
      omega
    have Hq : (sep.length : Int) + 1 ≤ (2 ^ 63 - 1) / (m : Int) :=
      (Int.le_ediv_iff_mul_le (by omega)).2 Hlt
    have Hdiv : sint.Z (BitVec.sdiv (W64 9223372036854775807) (elems.len - W64 1)) =
        (2 ^ 63 - 1) / (m : Int) := by
      rcases sdiv_cases (W64 9223372036854775807) (elems.len - W64 1)
          (by show 0 < sint.Z (elems.len - W64 1); omega) with ⟨-, h⟩ | ⟨h, -⟩
      · show (BitVec.sdiv _ _).toInt = _
        rw [h, show (W64 9223372036854775807).toInt = 2 ^ 63 - 1 from rfl]
        rw [show (elems.len - W64 1).toInt = (m : Int) by show sint.Z _ = _; omega]
      · exact absurd h (by decide)
    rw [if_neg (show ¬ sint.Z (elems.len - W64 1) = 0 by omega)]
    wp_auto
    rw [decide_eq_false (by rw [Hdiv, Hsl]; omega)]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    -- `n` is `len(sep) * (k - 1)`
    have Hn0 : sint.Z (zero_val w64 + W64 (sep.length : Nat) * (elems.len - W64 1)) =
        ((sep.length * m : Nat) : Int) := by
      have h1 : ((sep.length * m : Nat) : Int) = (sep.length : Int) * (m : Int) := Int.natCast_mul _ _
      have hmul : sint.Z (W64 (sep.length : Nat) * (elems.len - W64 1)) = (sep.length : Int) * m :=
        word.toInt_mul_eq _ _ Hsl Hm1 (by omega)
      rw [h1]
      show (0#64 + W64 (sep.length : Nat) * (elems.len - W64 1)).toInt = _
      rw [BitVec.zero_add]
      exact hmul
  rotate_left
  focus
    have Hsep0 : sep.length = 0 := by have := Hif; word
    have Hn0 : sint.Z (zero_val w64) = ((sep.length * m : Nat) : Int) := by rw [Hsep0]; simp; rfl
  rotate_left
  all_goals
    -- the lengths of the elements, summed (with the separators') in `n`
    ihave IH : iprop(∃ (j nv : w64) (ev : GoString),
        "i" ∷ i_ptr ↦ j ∗
        "elem" ∷ elem_ptr ↦ ev ∗
        "n" ∷ n_ptr ↦ nv ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ((x0 :: xs').length : Int)⌝ ∗
        "%Hnv" ∷ ⌜sint.Z nv = (sep.length * m : Nat) +
          ((((x0 :: xs').take (sint.Z j).toNat).map List.length).sum : Nat)⌝) $$ [i elem n]
    · iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [Hn0]; simp
    wp_for IH
    cleanup_bool_decide
    wp_if_destruct
    · have Hlt : (sint.Z j).toNat < (x0 :: xs').length := by word
      obtain ⟨x, Hx⟩ : ∃ x, (x0 :: xs')[(sint.Z j).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hx' : (x0 :: xs')[(sint.Z j).toNat] = x := by
        rw [List.getElem?_eq_getElem Hlt] at Hx; exact Option.some.inj Hx
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z elems.len from ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index elems (sint.Z j) _ dq x Hj.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hx
      have Hpre := sum_take_le (x0 :: xs') ((sint.Z j).toNat + 1)
      rw [sum_take_succ _ _ Hlt, Hx'] at Hpre
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hxl
      rw [decide_eq_false (by word)]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have Hsucc : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
      rw [Hsucc, sum_take_succ _ _ Hlt, Hx']
      word
    -- `n` is the join's length
    have Htake : (sint.Z j).toNat = (x0 :: xs').length := by word
    rw [Htake, List.take_length, ← Hm] at Hnv
    replace Hnv : sint.Z nv = ((sep.intercalate (x0 :: xs')).length : Int) := by omega
    rw [show zero_val Builder = ({ addr' := null, buf' := slice.nil } : Builder) from rfl]
    ihave Hnil := ownSlice_nil (V := w8) (DFrac.own 1)
    ihave Hnilcap := ownSliceCap_nil (V := w8)
    wp_apply Builder.wp_Grow b_ptr null slice.nil [] nv (Or.inl rfl) (by word)
      (fun _ => by unfold internal.bytealg.maxAlloc; simp only [slice.nil]; word) $$ [b Hnil Hnilcap]
      as Hb
    · iframe
      isplitl []
      · iexact Hnil
      · iexact Hnilcap
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index elems (sint.Z (W64 0)) _ dq x0 (by word) $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    wp_apply Builder.wp_WriteString b_ptr [] x0 $$ [$Hb] as Hb
    -- `elems[1:]`
    ihave %Hwf := ownSlice_wf $$ Hs
    have Hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z elems.len ∧ sint.Z elems.len ≤ sint.Z elems.len :=
      ⟨by word, by simp at Hlen; word, by word⟩
    rw [ite_eq_left ⟨Hb1.1, Hb1.2.1, Hwf.2⟩]
    icases (ownSlice_slice (W64 1) elems.len elems dq _ Hb1).1 $$ Hs with ⟨Hs0, Hs1, Hs2⟩
    have Hsub : subslice (sint.nat (W64 1)) (sint.nat elems.len) (x0 :: xs') = xs' := by
      have : sint.nat elems.len = (x0 :: xs').length := by simp at Hlen ⊢; word
      rw [this, show sint.nat (W64 1) = 1 from rfl]
      simp [subslice]
    rw [Hsub]
    ihave %Hlen1 := ownSlice_len $$ Hs1
    wp_auto
    ihave IH : iprop(∃ (j : w64) (sv : GoString),
        "i" ∷ i_ptr ↦ j ∗
        "s" ∷ s_ptr ↦ sv ∗
        "Hb" ∷ ownBuilder b_ptr (sep.intercalate (x0 :: xs'.take (sint.Z j).toNat)) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (xs'.length : Int)⌝) $$ [i s Hb]
    · iexists _, _
      iframe
      rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.take_zero,
        show sep.intercalate [x0] = [] ++ x0 by simp [List.intercalate]]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    cleanup_bool_decide
    wp_if_destruct
    · have Hlt : (sint.Z j).toNat < xs'.length := by simp at Hlen; word
      obtain ⟨x, Hx⟩ : ∃ x, xs'[(sint.Z j).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      rw [ite_eq_left ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index (slice.slice elems GoString (W64 1) elems.len) (sint.Z j) xs' dq x
        Hj.1 $$ [Hs1] as Hs1
      · iframe; ipureintro; exact Hx
      wp_apply Builder.wp_WriteString b_ptr _ sep $$ [$Hb] as Hb
      wp_apply Builder.wp_WriteString b_ptr _ x $$ [$Hb] as Hb
      wp_for_post
      iframe
      iexists _, _
      iframe
      have Hsucc : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
      have Heq : sep.intercalate (x0 :: xs'.take ((sint.Z j).toNat + 1)) =
          sep.intercalate (x0 :: xs'.take (sint.Z j).toNat) ++ sep ++ x := by
        rw [List.take_succ, Hx, Option.toList_some, ← List.cons_append]
        exact intercalate_snoc sep _ x (List.cons_ne_nil _ _)
      rw [Hsucc, Heq]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    rw [List.take_of_length_le (show xs'.length ≤ (sint.Z j).toNat by
      simp only [List.length_cons] at Hm; omega)]
    wp_apply Builder.wp_String b_ptr _ $$ [$Hb]
    iapply HΦ
    iapply (ownSlice_slice (W64 1) elems.len elems dq _ Hb1).2
    rw [Hsub]
    iframe

/-! ## `HasPrefix`, `TrimPrefix`, `Compare`, `Index`, `IndexByte` -/

/-- `strings.HasPrefix(s, prefix)`: whether `s` begins with `prefix`. -/
theorem wp_HasPrefix (s pfx : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! HasPrefix)) (Val #s)) (Val #pfx))
    {{ RET #(decide (pfx <+: s)); True }} := by
  wp_start
  wp_auto
  wp_apply internal.stringslite.wp_HasPrefix
  iapply HΦ; itrivial

/-- `strings.TrimPrefix(s, prefix)`: `s` without the prefix `prefix` if it has it, else `s`. -/
theorem wp_TrimPrefix (s pfx : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! TrimPrefix)) (Val #s)) (Val #pfx))
    {{ RET #(internal.stringslite.trimPrefix s pfx); True }} := by
  wp_start
  wp_auto
  wp_apply internal.stringslite.wp_TrimPrefix
  iapply HΦ; itrivial

/-- `strings.Compare(a, b)`: `-1`, `0` or `+1` as `a` is lexicographically less than, equal to
or greater than `b`. -/
theorem wp_Compare (a b : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Compare)) (Val #a)) (Val #b))
    {{ RET #(internal.bytealg.compareResult a b); True }} := by
  wp_start
  wp_auto
  wp_apply internal.bytealg.wp_CompareString
  iapply HΦ; itrivial

/-- `strings.Index(s, substr)`: the index of the first occurrence of `substr` in `s`, or `-1`. -/
theorem wp_Index (s sub : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Index')) (Val #s)) (Val #sub))
    {{ RET #(internal.bytealg.indexResult s sub); True }} := by
  wp_start
  wp_auto
  wp_apply internal.stringslite.wp_Index
  iapply HΦ; itrivial

/-- `strings.IndexByte(s, c)`: the index of the first `c` in `s`, or `-1`. -/
theorem wp_IndexByte (s : GoString) (c : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! IndexByte)) (Val #s)) (Val #c))
    {{ RET #(internal.bytealg.indexResult s [c]); True }} := by
  wp_start
  wp_auto
  wp_apply internal.stringslite.wp_IndexByte
  iapply HΦ; itrivial


/-- `strings.Count(s, sep)`, for a non-empty `sep`: the number of non-overlapping occurrences of
`sep` in `s`. (For an empty `sep` Go counts the UTF-8 sequences of `s`, plus one, with
`unicode/utf8.RuneCountInString`, which goose does not translate.) -/
theorem wp_Count (s sep : GoString) (Hsep : sep ≠ []) (Hs : s.length < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Count)) (Val #s)) (Val #sep))
    {{ RET #(W64 (countOcc s sep)); True }} := by
  wp_start
  wp_auto
  have Hpos := List.length_pos_iff.2 Hsep
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hsepl
  rw [decide_eq_false (show ¬ W64 sep.length = W64 0 by word)]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  wp_if_destruct
  · -- one byte: `bytealg.CountString(s, sep[0])`
    obtain ⟨c, rfl⟩ : ∃ c, sep = [c] := List.length_eq_one_iff.1 (by word)
    simp only [show (0 : Int) ≤ sint.Z (W64 0) by decide, ↓reduceIte, List.getElem?_cons_zero]
    wp_auto
    wp_apply internal.bytealg.wp_CountString
    rw [countOcc_singleton]
    iapply HΦ; itrivial
  ihave IH : iprop(∃ (cur : GoString) (k : Nat),
      "s" ∷ s_ptr ↦ cur ∗
      "n" ∷ n_ptr ↦ W64 k ∗
      "%Hk" ∷ ⌜countOcc s sep = k + countOcc cur sep ∧ cur.length ≤ s.length⌝) $$ [s n]
  · iexists s, 0
    iframe
    ipureintro
    omega
  wp_for IH
  wp_apply wp_Index
  rcases internal.bytealg.indexResult_cases cur sep with ⟨j, hj, hres, hjle⟩ | ⟨hj, hres⟩
  · -- an occurrence at `j`: count it and go on after it
    have Hend := firstOcc_end_le cur sep j hj
    rw [hres, decide_eq_false (show ¬ W64 j = W64 (-1) by word)]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hcur
    rw [ite_eq_left ⟨by word, by word, by word⟩,
      show sint.nat (W64 j + W64 sep.length) = j + sep.length by word,
      List.take_of_length_le (by simp; word)]
    wp_auto
    wp_for_post
    iframe
    iexists _, k + 1
    rw [show W64 k + W64 1 = W64 (k + 1 : Nat) by word]
    iframe
    ipureintro
    rw [countOcc_some cur sep Hsep j hj] at Hk
    exact ⟨by omega, by simp; omega⟩
  · -- no more occurrences: `n` is the count
    rw [hres]
    wp_auto
    wp_for_post
    rw [Hk.1, countOcc_none cur sep Hsep hj, Nat.add_zero]
    iapply HΦ; itrivial

/-- `strings.genSplit(s, sep, 0, -1)` (`Split`'s case of `genSplit`, which keeps no part of the
separator and splits at every occurrence), for a non-empty `sep`: a new slice of the fields
`split s sep`. -/
theorem wp_genSplit (s sep : GoString) (Hsep : sep ≠ []) (Hs : s.length < 2 ^ 63 - 1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (App (App (Val (@! genSplit)) (Val #s)) (Val #sep)) (Val #(W64 0)))
        (Val #(W64 (-1))))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* split s sep ∗ ownSliceCap GoString sl (DFrac.own 1) }} := by
  wp_start
  wp_auto
  rw [decide_eq_false Hsep]
  wp_auto
  have Hc := countOcc_le s sep Hsep
  wp_apply wp_Count s sep Hsep (by omega)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  rw [decide_eq_false (show ¬ sint.Z (W64 s.length + W64 1) <
    sint.Z (W64 (countOcc s sep) + W64 1) by word)]
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) (W64 (countOcc s sep) + W64 1) as %a ⟨Ha, Hacap⟩
  · ipureintro; word
  rw [show sint.nat (W64 (countOcc s sep) + W64 1) = countOcc s sep + 1 by word,
    show (zero_val GoString) = ([] : GoString) from rfl]
  ihave %Halen := ownSlice_len $$ Ha
  simp only [List.length_replicate] at Halen
  ihave IH : iprop(∃ (i : w64) (cur : GoString) (fields : List GoString),
      "i" ∷ i_ptr ↦ i ∗
      "s" ∷ s_ptr ↦ cur ∗
      "Ha" ∷ a ↦* (fields ++ List.replicate (countOcc s sep + 1 - fields.length) ([] : GoString)) ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i = fields.length ∧ fields.length ≤ countOcc s sep ∧
        split s sep = fields ++ split cur sep ∧
        countOcc cur sep = countOcc s sep - fields.length ∧ cur.length ≤ s.length⌝) $$ [i s Ha]
  · iexists (W64 0), s, []
    iframe
    ipureintro
    exact ⟨by decide, rfl, by simp, by simp, by simp, Nat.le_refl _⟩
  wp_for IH
  obtain ⟨Hi0, Hi, Hfl, Hsplit, Hcnt, Hcur⟩ := Hinv
  wp_if_destruct
  · -- a field before the next occurrence of `sep`
    wp_apply wp_Index
    rcases internal.bytealg.indexResult_cases cur sep with ⟨j, hj, hres, hjle⟩ | ⟨hj, hres⟩
    · have Hend := firstOcc_end_le cur sep j hj
      rw [hres, decide_eq_false (show ¬ sint.Z (W64 j) < sint.Z (W64 0) by word)]
      wp_auto
      rw [ite_eq_left ⟨by word, by word, by word⟩,
        show sint.nat (W64 j + W64 0) - 0 = j by word, List.drop_zero]
      wp_auto
      ihave %Halen' := ownSlice_len $$ Ha
      simp only [List.length_append, List.length_replicate] at Halen'
      rw [ite_eq_left ⟨by word, by word⟩]
      wp_apply wp_store_slice_index (V := GoString) a (sint.Z i) _ (cur.take j) $$ [Ha] as Ha
      · iframe; ipureintro; simp only [List.length_append, List.length_replicate]; word
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hcurl
      rw [ite_eq_left ⟨by word, by word, by word⟩,
        show sint.nat (W64 j + W64 sep.length) = j + sep.length by word,
        show (cur.drop (j + sep.length)).take (sint.nat (W64 cur.length) - (j + sep.length)) =
          cur.drop (j + sep.length) from List.take_of_length_le (by rw [List.length_drop]; word)]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, fields ++ [cur.take j]
      have Hset :
          (fields ++ List.replicate (countOcc s sep + 1 - fields.length) ([] : GoString)).set
          (sint.Z i).toNat (cur.take j) =
          (fields ++ [cur.take j]) ++
            List.replicate (countOcc s sep + 1 - (fields ++ [cur.take j]).length) [] := by
        rw [show (sint.Z i).toNat = fields.length by word,
          List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
        obtain ⟨m', hm'⟩ : ∃ m', countOcc s sep + 1 - fields.length = m' + 1 :=
          ⟨countOcc s sep - fields.length, by omega⟩
        rw [hm', List.replicate_succ, List.set_cons_zero, List.length_append,
          List.length_singleton, show countOcc s sep + 1 - (fields.length + 1) = m' by omega]
        simp
      rw [Hset]
      iframe
      ipureintro
      rw [countOcc_some cur sep Hsep j hj] at Hcnt
      refine ⟨by word, by simp; word, by simp; omega, ?_, by simp; omega, by simp; omega⟩
      rw [Hsplit, split_some cur sep Hsep j hj]
      simp
    · rw [countOcc_none cur sep Hsep hj] at Hcnt
      have := Hif
      exfalso; word
  · -- the last field: `a[i] = s`, return `a[:i+1]`
    have Hic : fields.length = countOcc s sep := by word
    rw [Hic, Nat.sub_self] at Hcnt
    have Hnone : firstOcc cur sep = none := by
      rcases h : firstOcc cur sep with _ | k
      · rfl
      · rw [countOcc_some cur sep Hsep k h] at Hcnt; omega
    ihave %Halen' := ownSlice_len $$ Ha
    ihave %Hawf := ownSlice_wf $$ Ha
    simp only [List.length_append, List.length_replicate] at Halen'
    rw [ite_eq_left ⟨Hi0, by word⟩]
    wp_apply wp_store_slice_index (V := GoString) a (sint.Z i) _ cur $$ [Ha] as Ha
    · iframe; ipureintro; simp only [List.length_append, List.length_replicate]; word
    wp_auto
    rw [ite_eq_left ⟨by decide, by word, by word⟩,
      show slice.slice a GoString (W64 0) (i + W64 1) = a by
        rw [show i + W64 1 = a.len by word]; exact (slice_slice_trivial a).symm]
    wp_auto
    iapply HΦ
    iframe
    rw [Hsplit, split_none cur sep Hsep Hnone, Hic, Nat.add_sub_cancel_left,
      show (sint.Z i).toNat = fields.length by word,
      List.replicate_one, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
    simp
    iexact Ha

/-- `strings.Split(s, sep)`, for a non-empty `sep` and `s` shorter than `2^63 - 1` bytes: a new
slice of the fields `split s sep`. (For an empty `sep` Go splits `s` into its UTF-8 sequences,
which this spec does not cover.) -/
theorem wp_Split (s sep : GoString) (Hsep : sep ≠ []) (Hs : s.length < 2 ^ 63 - 1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Split)) (Val #s)) (Val #sep))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* split s sep ∗ ownSliceCap GoString sl (DFrac.own 1) }} := by
  wp_start
  wp_auto
  wp_apply wp_genSplit s sep Hsep Hs as %sl ⟨Hsl, Hcap⟩
  iapply HΦ
  iframe

/-- FIXME: this is wrong (unsound) for strings with non-ASCII
runes. Simplest solution might be to add a precondition for the string to be
all ASCII. -/
axiom wp_Fields [package_sem : strings.Assumptions] (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! Fields)) (Val #s))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* (splitFields s) ∗ ownSliceCap w8 sl (DFrac.own 1) }}

/-! Unit tests for `wp_Fields`. -/

example :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! Fields)) (Val #(go!"  hello\tthere\ngeneral\rkenobi ")))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* [go!"hello", go!"there", go!"general", go!"kenobi"] ∗
        ownSliceCap w8 sl (DFrac.own 1) }} := by
  iintro %Φ #Hinit HΦ
  wp_apply +noauto wp_Fields with %sl ⟨Hsl, Hcap⟩
  have h : splitFields go!"  hello\tthere\ngeneral\rkenobi " =
      [go!"hello", go!"there", go!"general", go!"kenobi"] := by decide
  rw [h]
  iapply HΦ
  iframe

example :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! Fields)) (Val #(go!"hello world")))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* [go!"hello", go!"world"] ∗
        ownSliceCap w8 sl (DFrac.own 1) }} := by
  iintro %Φ #Hinit HΦ
  wp_apply +noauto wp_Fields go!"hello world" with %sl ⟨Hsl, Hcap⟩
  have h : splitFields go!"hello world" = [go!"hello", go!"world"] := by decide
  rw [h]
  iapply HΦ
  iframe

end wps

end strings

end Perennial
end
