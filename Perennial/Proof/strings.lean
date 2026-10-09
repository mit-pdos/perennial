/-
Specs for the Go `strings` package.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.strings
public import Perennial.GeneratedProof.strings

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
  iframe Hown
  is_pkg_init_finish

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

/-- `strings.Join(elems, sep)`: the elements of `elems` separated by `sep`. Proved from
the model of `Join` (`Perennial/TrustedCode/strings.lean`), which does not model Go's panic
when the result's length overflows `int`. -/
theorem wp_Join (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs }}
      (App (App (Val (@! Join)) (Val #elems)) (Val #sep))
    {{ RET #(sep.intercalate xs); elems ↦*{dq} xs }} := by
  wp_start as Hs
  wp_auto
  -- `forRange`'s counter is `i`; the model's own `i` (the key) is shadowed
  rename_i k_ptr
  irename : (k_ptr ↦ zero_val w64 : IProp GF) => k
  ihave %Hlen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (n kv : w64) (acc ev : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "k" ∷ k_ptr ↦ kv ∗
      "s" ∷ s_ptr ↦ acc ∗
      "e" ∷ e_ptr ↦ ev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (xs.length : Int)⌝ ∗
      "%Hacc" ∷ ⌜acc = sep.intercalate (xs.take (sint.Z n).toNat)⌝) $$ [i k s e]
  · iexists _, _, _, _
    iframe
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp; rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < xs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, xs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z elems.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index elems (sint.Z n) xs dq x Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    wp_if_destruct
    all_goals
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have Hx' : xs[(sint.Z n).toNat] = x := by
        rw [List.getElem?_eq_getElem Hlt] at Hx; exact Option.some.inj Hx
      have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
      rw [Hsucc, intercalate_take_succ sep xs _ x Hlt Hx']
    · simp [Hacc, show (sint.Z n).toNat ≠ 0 by word]
    · simp [Hacc, show (sint.Z n).toNat = 0 by word]
  · rw [Hacc, List.take_of_length_le (by word)]
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
