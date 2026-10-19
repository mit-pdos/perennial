/-
String conversions are implemented by the
Go model `github.com/mit-pdos/perennial/goose/model/strings`, whose generated
translation lives in namespace `github_com.mit_pdos.perennial.goose.model.strings`.
-/
module

public import Perennial.Golang.Defn.Loop
public import Perennial.Golang.Defn.Assume
public import Perennial.Golang.Defn.Predeclared
public import Perennial.Code.github_com.mit_pdos.perennial.goose.model.strings

@[expose] public section

namespace Perennial

namespace go

/-- Lexicographic order on byte strings, comparing bytes by `uint.Z`. -/
def GoStringLt : GoString → GoString → Prop :=
  List.Lex (fun (x y : w8) => uint.Z x < uint.Z y)

instance goStringLt_dec : DecidableRel GoStringLt :=
  fun x y => inferInstanceAs (Decidable (List.Lex _ x y))

example :
    ¬ GoStringLt go!"" go!"" ∧
    GoStringLt go!"" go!"a" ∧
    ¬ GoStringLt go!"a" go!"" ∧
    ¬ GoStringLt go!"ab" go!"a" ∧
    GoStringLt go!"ab" go!"b" := by
  decide

def GoStringLe (x y : GoString) : Prop :=
  x = y ∨ GoStringLt x y

instance goStringLe_dec : DecidableRel GoStringLe :=
  fun x y => inferInstanceAs (Decidable (x = y ∨ GoStringLt x y))

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

section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]
open github_com.mit_pdos.perennial.goose.model

class StringSemantics [GoSemanticsFunctions] : Prop where
  [package_sem : strings.Assumptions]

  internal_string_len_step (s : GoString) :
    ⟦InternalStringLen, #s⟧ ⤳ (if s.length < 2^63 then
                                  (Val #(W64 s.length))
                                else AngelicExit #())

  string_len_unfold {t : go.GoType} [t ↓u go.string] : FuncUnfold go.len [t]
    (λ: "s", InternalStringLen "s" : val)

  string_index (s : GoString) (i : w64) :
    ⟦Index go.string, (#s, #i)⟧ ⤳[under]
    (match (if 0 ≤ sint.Z i then s[sint.nat i]? else none) with
     | some b => #b
     | _ => Panic "index out of bounds")

  string_slice (s : GoString) (low high : w64) :
    ⟦Slice go.string, (#s, #low, #high)⟧ ⤳[under]
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ s.length then
       #((s.drop (sint.nat low)).take (sint.nat high - sint.nat low))
     else Panic "slice bounds out of range")

  convert_byte_to_string (c : w8) :
    ⟦Convert go.byte go.string, #c⟧ ⤳[under] #([c] : GoString)

  convert_bytes_to_string {from_ elem_type to : go.GoType}
    [from_ ↓u go.SliceType elem_type] [elem_type ↓u go.byte] [to ↓u go.string] (v : val) :
    ⟦Convert from_ to, v⟧ ⤳[internal] (@! strings.ByteSliceToString v)

  convert_string_to_bytes {from_ to elem_type : go.GoType}
    [from_ ↓u go.string] [to ↓u go.SliceType elem_type] [elem_type ↓u go.byte] (v : val) :
    ⟦Convert from_ to, v⟧ ⤳[internal] (@! strings.StringToByteSlice v)

  lt_string (x y : GoString) :
    ⟦GoOp GoLt go.string, (#x, #y)⟧ ⤳[under] #(decide (GoStringLt x y))

  le_string (x y : GoString) :
    ⟦GoOp GoLe go.string, (#x, #y)⟧ ⤳[under] #(decide (GoStringLe x y))

  gt_string (x y : GoString) :
    ⟦GoOp GoGt go.string, (#x, #y)⟧ ⤳[under] #(decide (GoStringLt y x))

  ge_string (x y : GoString) :
    ⟦GoOp GoGe go.string, (#x, #y)⟧ ⤳[under] #(decide (GoStringLe y x))

attribute [instance] StringSemantics.package_sem StringSemantics.internal_string_len_step
  StringSemantics.string_len_unfold StringSemantics.string_index StringSemantics.string_slice
  StringSemantics.convert_byte_to_string StringSemantics.convert_bytes_to_string
  StringSemantics.convert_string_to_bytes StringSemantics.lt_string StringSemantics.le_string
  StringSemantics.gt_string StringSemantics.ge_string
export StringSemantics (internal_string_len_step string_len_unfold string_index string_slice
  convert_byte_to_string convert_bytes_to_string convert_string_to_bytes lt_string le_string
  gt_string ge_string)

end defs
end go

end Perennial
