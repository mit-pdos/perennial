/-
Shared definitions of the proofs of the Go `strings` package: its `isPkgInit`,
the models of what `Fields`, `Compare`, `TrimPrefix` and `Split` return, when `Join`
returns (`JoinFits`), and lemmas about them.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.strings
public import Perennial.GeneratedProof.strings
public import Perennial.Proof.internal.abi.Base
public import Perennial.Proof.internal.bytealg.Base
public import Perennial.Proof.«unsafe».Base

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

/-- What `strings.Compare(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically less
than, equal to or greater than `b` (Go's `<` on strings, `GoStringLt`), as `bytes.compareResult`. -/
def compareResult (a b : GoString) : w64 :=
  if go.GoStringLt a b then W64 (-1) else if a = b then W64 0 else W64 1

/-- What `strings.TrimPrefix(s, pfx)` returns: `s` without the prefix `pfx` if it has it,
else `s`. -/
def trimPrefix (s pfx : GoString) : GoString :=
  if pfx <+: s then s.drop pfx.length else s

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

end wps

end strings

end Perennial
end
