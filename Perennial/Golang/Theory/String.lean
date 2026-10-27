/-
Specs for the conversions between strings
and byte slices, which are implemented by the Go model
`github.com/mit-pdos/perennial/goose/model/strings` (proved in
`Perennial/Proof/github_com/mit_pdos/perennial/goose/model/strings.lean`),
and facts about the string order `go.GoStringLt`.
-/
module

public import Perennial.Golang.Defn.String
public import Perennial.Golang.Theory.Pre
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go

/-! `GoStringLt` is a strict total order (Lean core's facts about `List.Lex`). -/

theorem goStringLt_irrefl (a : GoString) : ¬ GoStringLt a a :=
  List.lex_irrefl (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun _ => Int.lt_irrefl _) a

theorem goStringLt_trans {a b c : GoString} (h1 : GoStringLt a b) (h2 : GoStringLt b c) :
    GoStringLt a c :=
  List.lex_trans (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun h h' => Int.lt_trans h h') h1 h2

theorem goStringLt_asymm {a b : GoString} (h : GoStringLt a b) : ¬ GoStringLt b a :=
  List.lex_asymm (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun h h' => Int.lt_asymm h h') h

/-- Go's `<` on strings is total. -/
theorem goStringLt_eq_of_not_lt {a b : GoString} (h1 : ¬ GoStringLt a b)
    (h2 : ¬ GoStringLt b a) : a = b :=
  List.lex_trichotomous (r := fun (x y : w8) => uint.Z x < uint.Z y) (fun x y a1 a2 => by
    apply BitVec.eq_of_toNat_eq
    simp only [uint.Z] at a1 a2
    omega) h2 h1

theorem goStringLt_cons_iff (x y : w8) (xs ys : GoString) :
    GoStringLt (x :: xs) (y :: ys) ↔ uint.Z x < uint.Z y ∨ (x = y ∧ GoStringLt xs ys) := by
  constructor
  · intro h; cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

theorem goStringLt_nil_cons (x : w8) (xs : GoString) : GoStringLt [] (x :: xs) := List.Lex.nil

theorem goStringLt_not_nil (k : GoString) : ¬ GoStringLt k [] := by intro h; cases h

end go

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics] [go.StringSemantics]
variable {s : Stuckness} {E : CoPset}

open github_com.mit_pdos.perennial.goose.model.strings in
attribute [local instance] go.tagged_internal_inst in
theorem wp_string_to_bytes (str : GoString) {from_ to elem_type : go.GoType}
    [to ↓u go.SliceType elem_type] [elem_type ↓u go.byte] [from_ ↓u go.string] :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (Convert from_ to))) (Val #str)) @ s; E
    {{ (sl : GoSlice), RET #sl; sl ↦* str ∗ ownSliceCap w8 sl (DFrac.own 1) }} := by
  iintro %Φ _ HΦ
  wp_pure
  wp_apply wp_StringToByteSlice str with %sl Hsl
  iapply HΦ $$ Hsl

open github_com.mit_pdos.perennial.goose.model.strings in
attribute [local instance] go.tagged_internal_inst in
theorem wp_bytes_to_string (sl : GoSlice) (str : GoString) (dq : DFrac)
    {from_ elem_type to : go.GoType}
    [from_ ↓u go.SliceType elem_type] [elem_type ↓u go.byte] [to ↓u go.string] :
    {{ (sl ↦*{dq} str : IProp GF) }}
      (App (Val (GoInstruction (Convert from_ to))) (Val #sl)) @ s; E
    {{ RET #str; sl ↦*{dq} str }} := by
  iintro %Φ Hsl HΦ
  wp_pure
  wp_apply wp_ByteSliceToString sl str dq $$ Hsl with Hsl
  iapply HΦ $$ Hsl

/-- The postcondition of the body of a range loop: after the body ends normally or with
`continue`, the loop goes on with `P`; after `break`, `return` or a panic, the loop
ends with that outcome (`Φ executeVal` for `break`). -/
def forRangePostcondition (P : IProp GF) (Φ : val → IProp GF) (bv : val) : IProp GF :=
  iprop((⌜bv = continueVal⌝ ∗ P) ∨
    (⌜bv = executeVal⌝ ∗ P) ∨
    (⌜bv = breakVal⌝ ∗ Φ executeVal) ∨
    (∃ v, ⌜bv = returnVal v⌝ ∗ Φ bv) ∨
    (∃ p, ⌜bv = PanicV p⌝ ∗ Φ bv))

set_option maxRecDepth 20000 in
open github_com.mit_pdos.perennial.goose.model.strings in
/-- A range loop over the string `str`: `P i` is the invariant before the `i`-th
iteration, which runs the body with the rune at byte index `k` and its value `r`,
`(go.runes str)[i] = (k, r)`. -/
theorem wp_string_for_range (str : GoString) (body : GoFunc) (P : Nat → IProp GF)
    (Φ : val → IProp GF) :
    P 0 -∗
    □ (∀ (i k : Nat) (r : w32), ⌜(go.runes str)[i]? = some (k, r)⌝ -∗ P i -∗
        WP (App (App (Val #body) (Val #(W64 k))) (Val #r)) @ s; E
          {{ forRangePostcondition (P (i + 1)) Φ }}) -∗
    (P (go.runes str).length -∗ Φ executeVal) -∗
    WP (App (App (Val string.forRange) (Val #str)) (Val #body)) @ s; E {{ Φ }} := by
  iintro HP #Hiter HΦ
  unfold string.forRange
  wp_call
  wp_auto
  ihave Hinv : (∃ (j n : Nat),
      "i" ∷ i_ptr ↦ W64 n ∗
      "HP" ∷ P j ∗
      "HΦ" ∷ (P (go.runes str).length -∗ Φ executeVal) ∗
      "%Hn" ∷ ⌜(go.runes str).drop j = go.runesFrom str (str.length - n) n ∧ n ≤ str.length ∧
        j ≤ (go.runes str).length⌝ :
      IProp GF) $$ [i HP HΦ]
  · iexists 0, 0
    iframe
    ipureintro
    exact ⟨rfl, Nat.zero_le _, Nat.zero_le _⟩
  wp_for Hinv
  wp_apply wp_string_len with %Hlen
  by_cases hn : n < str.length
  · have hc : sint.Z (W64 (n : Int)) < sint.Z (W64 (str.length : Int)) := by word
    simp only [decide_eq_true hc, decide_true, ↓reduceIte]
    wp_call
    wp_auto
    have hsn : sint.nat (W64 (n : Int)) = n := by word
    have h0 : 0 ≤ sint.Z (W64 (n : Int)) := by word
    have h1 : sint.nat (W64 (n : Int)) < str.length := by rw [hsn]; exact hn
    wp_apply wp_DecodeRune str (W64 n) h0 h1
    rw [hsn]
    have hcons := go.runesFrom_cons str n hn
    have hj : (go.runes str)[j]? = some (n, (go.decodeRune str n).1) := by
      have h := congrArg (·[0]?) Hn.1
      simp only [hcons, List.getElem?_drop] at h
      simpa using h
    iapply wp_wand $$ (Hiter $$ %j %n %_ %hj HP)
    iintro %bv Hpost
    have hnext := go.decodeRune_snd str n hn
    have hlt : j < (go.runes str).length := (List.getElem?_eq_some_iff.1 hj).1
    have hdrop : (go.runes str).drop (j + 1) =
        go.runesFrom str (str.length - (go.decodeRune str n).2) (go.decodeRune str n).2 := by
      have h := congrArg List.tail Hn.1
      simpa [hcons, List.tail_drop] using h
    unfold forRangePostcondition
    icases Hpost with (⟨%hbv, HP⟩ | ⟨%hbv, HP⟩ | ⟨%hbv, HΦ'⟩ | ⟨%v, %hbv, HΦ'⟩ | ⟨%p, %hbv, HΦ'⟩)
    · subst hbv
      iapply wp_for_post_continue
      wp_call
      iexists (j + 1), (go.decodeRune str n).2
      iframe
      ipureintro
      exact ⟨hdrop, hnext.2, by omega⟩
    · subst hbv
      iapply wp_for_post_do
      wp_call
      iexists (j + 1), (go.decodeRune str n).2
      iframe
      ipureintro
      exact ⟨hdrop, hnext.2, by omega⟩
    · subst hbv
      iapply wp_for_post_break
      iexact HΦ'
    · subst hbv
      iapply wp_for_post_return
      iexact HΦ'
    · subst hbv
      iapply wp_for_post_panic
      iexact HΦ'
  · have hc : ¬ sint.Z (W64 (n : Int)) < sint.Z (W64 (str.length : Int)) := by word
    simp only [decide_eq_false hc, decide_eq_false false_neq_true, Bool.false_eq_true,
      ↓reduceIte, _root_.decide_true]
    have hend : (go.runes str).drop j = [] := by
      rw [Hn.1]; exact go.runesFrom_end str n (by omega)
    have hjl : j = (go.runes str).length := by
      have := List.drop_eq_nil_iff.1 hend; omega
    subst hjl
    iapply HΦ $$ HP

end proof

end Perennial
