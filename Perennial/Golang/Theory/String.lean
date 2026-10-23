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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

end proof

end Perennial
