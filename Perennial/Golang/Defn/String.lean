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

  /-- `s[i]`: the byte at index `i`; a run-time panic unless `0 ≤ i < len(s)` ("the index x is
  in range if 0 <= x < len(a), otherwise it is out of range", the Go spec, "Index expressions").
  The test `0 ≤ i` is needed because `sint.nat` sends a negative `i` to 0. -/
  string_index (s : GoString) (i : w64) :
    ⟦Index go.string, (#s, #i)⟧ ⤳[under]
    (match (if 0 ≤ sint.Z i then s[sint.nat i]? else none) with
     | some b => #b
     | _ => Panic "index out of bounds")

  /-- `s[low:high]`: the bytes of `s` from index `low` up to (not including) `high`; a run-time
  panic unless `0 ≤ low ≤ high ≤ len(s)` ("for strings, the indices are in range if
  0 <= low <= high <= len(a), otherwise they are out of range", the Go spec, "Slice
  expressions"; the upper bound of a string is its length, it has no capacity). Goose
  translates `s[low:]` and `s[:high]` with `low = 0` and `high = len(s)` filled in. -/
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
