/-
Specs for the Go `strings` package.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.strings
public import Perennial.GeneratedProof.strings
public import Perennial.Proof.internal.abi
public import Perennial.Proof.internal.bytealg
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
  wp_apply «unsafe».wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hunsafe⟩
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

/-- `b.String()` returns the bytes written. -/
theorem Builder.wp_String (b : Loc) (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ ownBuilder b s }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"String")) (Val #()))
    {{ RET #s; ownBuilder b s }} := by
  wp_start as Hb
  unfold ownBuilder
  icases Hb with ⟨%addr, %buf, Hb, %Haddr, Hs, Hcap⟩
  rw [Builder_ty_eq]
  wp_auto
  dsimp only
  wp_apply wp_bytes_to_string $$ Hs as Hs
  iapply HΦ
  iexists addr, buf
  iframe
  ipureintro
  exact Haddr

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
    wp_apply Builder.wp_String b_ptr _ $$ [$Hb] as -
    iapply HΦ
    iapply (ownSlice_slice (W64 1) elems.len elems dq _ Hb1).2
    rw [Hsub]
    iframe

/-- `strings.HasPrefix(s, prefix)`: whether `s` begins with `prefix`. Proved from the model of
`HasPrefix` (`Perennial/TrustedCode/strings.lean`). -/
theorem wp_HasPrefix (s pfx : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! HasPrefix)) (Val #s)) (Val #pfx))
    {{ RET #(decide (pfx <+: s)); True }} := by
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp
  wp_if_destruct
  · rw [decide_eq_false (fun h => by have := h.length_le; word)]
    iapply HΦ; itrivial
  ihave IH : iprop(∃ n : w64,
      "i" ∷ i_ptr ↦ n ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (pfx.length : Int)⌝ ∗
      "%Heq" ∷ ⌜pfx.take (sint.nat n) = s.take (sint.nat n)⌝) $$ [i]
  · iexists _
    iframe
    ipureintro
    rw [show zero_val w64 = W64 0 from rfl]
    exact ⟨⟨by word, by word⟩, by simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]⟩
  -- the Go variable `prefix` is a keyword in cases patterns
  irename «prefix» => Hpfx
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < pfx.length := by word
    have Hlt' : sint.nat n < s.length := by word
    rw [List.getElem?_eq_getElem Hlt']
    wp_auto
    rw [List.getElem?_eq_getElem Hlt]
    wp_auto
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one,
        List.take_add_one, Heq, List.getElem?_eq_getElem Hlt', List.getElem?_eq_getElem Hlt, Hif]
    · wp_for_post
      rw [decide_eq_false]
      · iapply HΦ; itrivial
      intro h
      apply Hif
      obtain ⟨t, rfl⟩ := h
      simp [List.getElem_append_left Hlt]
  · have Hnot : ¬ sint.Z n < sint.Z (W64 pfx.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    rw [decide_eq_true]
    · iapply HΦ; itrivial
    rw [show sint.nat n = pfx.length by word, List.take_length] at Heq
    rw [Heq]
    exact List.take_prefix _ _

/-- What `strings.Compare(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically less
than, equal to or greater than `b` (Go's `<` on strings, `GoStringLt`), as `bytes.compareResult`. -/
def compareResult (a b : GoString) : w64 :=
  if go.GoStringLt a b then W64 (-1) else if a = b then W64 0 else W64 1

/-- `strings.Compare(a, b)`: `compareResult a b`. Proved from the model of `Compare`
(`Perennial/TrustedCode/strings.lean`). -/
theorem wp_Compare (a b : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Compare)) (Val #a)) (Val #b))
    {{ RET #(compareResult a b); True }} := by
  wp_start
  unfold compareResult
  by_cases hlt : go.GoStringLt a b
  · simp only [hlt, decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  · simp only [hlt, decide_false, ↓reduceIte]
    wp_auto
    by_cases heq : a = b
    · simp only [heq, decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
    · simp only [heq, decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial

/-- What `strings.TrimPrefix(s, pfx)` returns: `s` without the prefix `pfx` if it has it,
else `s`. -/
def trimPrefix (s pfx : GoString) : GoString :=
  if pfx <+: s then s.drop pfx.length else s

/-- `strings.TrimPrefix(s, pfx)`: `trimPrefix s pfx`. Proved from the model of `TrimPrefix`
(`Perennial/TrustedCode/strings.lean`). -/
theorem wp_TrimPrefix (s pfx : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! TrimPrefix)) (Val #s)) (Val #pfx))
    {{ RET #(trimPrefix s pfx); True }} := by
  wp_start as #Hinit
  wp_auto
  -- the model calls `HasPrefix` by its name (the trusted code is below `Code.strings`)
  rw [show (go!"strings.HasPrefix" : GoString) = HasPrefix from rfl]
  wp_apply wp_HasPrefix
  unfold trimPrefix
  by_cases h : pfx <+: s
  · simp only [h, decide_true, ↓reduceIte]
    wp_auto
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, Hcap⟩
    ihave %Hlen := ownSlice_len $$ Hsl
    ihave %Hwf := ownSlice_wf $$ Hsl
    have Hp : pfx.length ≤ s.length := h.length_le
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp'
    have Hk : 0 ≤ sint.Z (W64 pfx.length) ∧ sint.Z (W64 pfx.length) ≤ sint.Z sl.len := by word
    rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
    icases (ownSlice_split_all (W64 pfx.length) sl _ s Hk).1 $$ Hsl with ⟨-, Hsl⟩
    rw [show sint.nat (W64 pfx.length) = pfx.length by word]
    wp_apply wp_bytes_to_string $$ Hsl as -
    iapply HΦ; itrivial
  · simp only [h, decide_false, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

/-- The fields that Go's `strings.Split` makes of the rest `r` of a string when the current field
is `field`: at an occurrence of `sep` the field ends and the next one starts after the
occurrence; any other byte goes to the current field. For an empty `sep` it keeps all of `r` in
the field (Go splits into UTF-8 sequences instead; `wp_Split` requires `sep` non-empty). -/
def splitAux (sep : GoString) : GoString → GoString → List GoString
  | [], field => [field]
  | c :: r, field =>
    if sep ≠ [] ∧ sep <+: c :: r then field :: splitAux sep ((c :: r).drop sep.length) []
    else splitAux sep r (field ++ [c])
termination_by r => r.length
decreasing_by
  · obtain ⟨hne, -⟩ := ‹sep ≠ [] ∧ sep <+: c :: r›
    have : 0 < sep.length := List.length_pos_iff.mpr hne
    simp only [List.length_drop, List.length_cons]; omega
  · simp

/-- What `strings.Split(s, sep)` returns, for a non-empty `sep`: the substrings of `s` between
the occurrences of `sep`, found left to right without overlap. `split "" sep = [""]`, and a
trailing `sep` gives a trailing empty field. -/
def split (s sep : GoString) : List GoString := splitAux sep s []

/-! Tests of `split`. -/

example : split go!"a/b" go!"/" = [go!"a", go!"b"] := by simp [split, splitAux]
example : split go!"" go!"/" = [go!""] := by simp [split, splitAux]
example : split go!"a/" go!"/" = [go!"a", go!""] := by simp [split, splitAux]
example : split go!"x//ab///" go!"//" = [go!"x", go!"ab", go!"/"] := by simp [split, splitAux]

theorem splitAux_ne_nil (sep r field : GoString) : splitAux sep r field ≠ [] := by
  fun_induction splitAux sep r field <;> simp_all

/-- `strings.Split` returns at least one field. -/
theorem split_ne_nil (s sep : GoString) : split s sep ≠ [] := splitAux_ne_nil _ _ _

theorem intercalate_splitAux (sep r field : GoString) :
    sep.intercalate (splitAux sep r field) = field ++ r := by
  fun_induction splitAux sep r field with
  | case1 field => simp
  | case2 c r field h ih =>
    obtain ⟨t, ht⟩ := h.2
    rw [List.intercalate_cons_of_ne_nil (splitAux_ne_nil _ _ _), ih, ← ht]
    simp
  | case3 c r field h ih => rw [ih]; simp

/-- The fields of `split s sep` joined by `sep` (as `strings.Join` joins them) give `s` back. -/
theorem intercalate_split (s sep : GoString) : sep.intercalate (split s sep) = s :=
  intercalate_splitAux sep s []

theorem splitAux_no_infix (sep r field : GoString) (hsep : sep ≠ [])
    (H : ∀ k < field.length, ¬ sep <+: field.drop k ++ r) :
    ∀ f ∈ splitAux sep r field, ¬ sep <:+: f := by
  fun_induction splitAux sep r field with
  | case1 field =>
    intro f hf ⟨u, v, huv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    have hlt : u.length < f.length := by
      rw [← huv]; have := List.length_pos_iff.mpr hsep; simp; omega
    apply H u.length hlt
    rw [← huv]; simp
  | case2 c r field h ih =>
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · rintro ⟨u, v, huv⟩
      have hlt : u.length < f.length := by
        rw [← huv]; have := List.length_pos_iff.mpr hsep; simp; omega
      apply H u.length hlt
      rw [← huv]; simp
    · exact ih (by simp) f hf
  | case3 c r field h ih =>
    apply ih
    intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hk' : k < field.length
    · rw [List.drop_append_of_le_length (by omega)]
      simpa using H k hk'
    · rw [show k = field.length by omega, List.drop_append_of_le_length (Nat.le_refl _)]
      simp only [List.drop_length, List.nil_append, List.singleton_append]
      exact fun hp => h ⟨hsep, hp⟩

/-- No field of `split s sep` contains `sep`, for a non-empty `sep`. -/
theorem split_no_infix (s sep : GoString) (hsep : sep ≠ []) :
    ∀ f ∈ split s sep, ¬ sep <:+: f :=
  splitAux_no_infix sep s [] hsep (by simp)

/-- `strings.Split(s, sep)`, for a non-empty `sep`: a new slice of the fields `split s sep`.
Proved from the model of `Split` (`Perennial/TrustedCode/strings.lean`), which does not model
Go's split of `s` into UTF-8 sequences for an empty `sep`. -/
theorem wp_Split (s sep : GoString) (Hsep : sep ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Split)) (Val #s)) (Val #sep))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* split s sep ∗ ownSliceCap GoString sl (DFrac.own 1) }} := by
  wp_start as #Hinit
  obtain ⟨c0, Hc0⟩ : ∃ c0, sep[0]? = some c0 := by
    cases sep with
    | nil => exact absurd rfl Hsep
    | cons c _ => exact ⟨c, rfl⟩
  wp_auto
  rw [Hc0]
  wp_auto
  ihave IH : iprop(∃ (a_sl : GoSlice) (fs : List GoString) (field rest : GoString),
      "a" ∷ a_ptr ↦ a_sl ∗
      "Ha" ∷ a_sl ↦* fs ∗
      "Hcap" ∷ ownSliceCap GoString a_sl (DFrac.own 1) ∗
      "field" ∷ field_ptr ↦ field ∗
      "rest" ∷ rest_ptr ↦ rest ∗
      "%Hinv" ∷ ⌜split s sep = fs ++ splitAux sep rest field⌝) $$ [a field rest]
  · iexists _, [], _, _
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    rfl
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hrlen
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    obtain ⟨c, r, rfl⟩ : ∃ c r, rest = c :: r := by
      cases rest with
      | nil => exfalso; simp at Hif'
      | cons c r => exact ⟨c, r, rfl⟩
    -- the model calls `HasPrefix` by its name (the trusted code is below `Code.strings`)
    rw [show (go!"strings.HasPrefix" : GoString) = HasPrefix from rfl]
    wp_apply wp_HasPrefix
    by_cases hp : sep <+: c :: r
    · -- an occurrence of `sep`: the field ends
      simp only [hp, decide_true]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoString) (t := go.string) [field]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.string #field)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Htmp, -⟩
      wp_auto
      wp_apply wp_slice_append (V := GoString) (t := go.string) a_sl fs _ [field] (DFrac.own 1)
        $$ [Ha Hcap Htmp] as %a' ⟨Ha', Hcap', -⟩
      · iframe
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      ihave %Hlen := ownSlice_len $$ Hsl
      ihave %Hwf := ownSlice_wf $$ Hsl
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      have Hp : sep.length ≤ (c :: r).length := hp.length_le
      have Hk : 0 ≤ sint.Z (W64 sep.length) ∧ sint.Z (W64 sep.length) ≤ sint.Z sl.len := by word
      rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
      icases (ownSlice_split_all (W64 sep.length) sl _ _ Hk).1 $$ Hsl with ⟨-, Hsl⟩
      rw [show sint.nat (W64 sep.length) = sep.length by word]
      wp_apply wp_bytes_to_string $$ Hsl as -
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      rw [Hinv, splitAux, ite_eq_left ⟨Hsep, hp⟩]
      simp
    · -- another byte: it goes to the field
      simp only [hp, decide_false]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [c]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.byte #c)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %c_sl ⟨Hc_sl, -⟩
      wp_apply wp_bytes_to_string $$ Hc_sl as -
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      ihave %Hlen := ownSlice_len $$ Hsl
      ihave %Hwf := ownSlice_wf $$ Hsl
      have Hk : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len := by
        simp only [List.length_cons] at Hlen Hrlen; word
      rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
      icases (ownSlice_split_all (W64 1) sl _ _ Hk).1 $$ Hsl with ⟨-, Hsl⟩
      rw [show sint.nat (W64 1) = 1 by word]
      wp_apply wp_bytes_to_string $$ Hsl as -
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      rw [Hinv, splitAux, ite_eq_right (fun h => hp h.2)]
      simp
  · -- the end of `s`: the last field
    have Hnot : ¬ sint.Z (W64 0) < sint.Z (W64 rest.length) :=
      fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    have Hrest : rest = [] := List.eq_nil_of_length_eq_zero (by word)
    subst Hrest
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoString) (t := go.string) [field]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.string #field)] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Htmp, -⟩
    wp_apply wp_slice_append (V := GoString) (t := go.string) a_sl fs _ [field] (DFrac.own 1)
      $$ [Ha Hcap Htmp] as %a' ⟨Ha', Hcap', -⟩
    · iframe
    rw [Hinv, splitAux]
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
