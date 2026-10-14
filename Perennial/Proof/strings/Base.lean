/-
Shared definitions of the proofs of the Go `strings` package: its `isPkgInit`,
the models of what `Fields`, `Compare`, `TrimPrefix`, `Count` and `Split` return, when `Join`
returns (`JoinFits`), and lemmas about them.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.strings
public import Perennial.GeneratedProof.strings
public import Perennial.Proof.internal.abi.Base
public import Perennial.Proof.internal.bytealg.Base
public import Perennial.Proof.internal.stringslite.Base
public import Perennial.Proof.unicode.utf8.Base
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

/-- What `strings.Compare(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically less
than, equal to or greater than `b` (Go's `<` on strings, `GoStringLt`), as
`internal/bytealg.CompareString` computes it. -/
abbrev compareResult (a b : GoString) : w64 := internal.bytealg.compareResult a b

/-- What `strings.TrimPrefix(s, pfx)` returns: `s` without the prefix `pfx` if it has it,
else `s` (`internal/stringslite.TrimPrefix`). -/
abbrev trimPrefix (s pfx : GoString) : GoString := internal.stringslite.trimPrefix s pfx

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
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

end wps

end strings

end Perennial
end
