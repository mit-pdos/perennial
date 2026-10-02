/-
Port of `new/golang/defn/string.v`. String conversions are implemented by the
Go model `github.com/mit-pdos/perennial/goose/model/strings`, whose generated
translation lives in namespace `github_com.mit_pdos.perennial.goose.model.strings`
(Rocq: `strings`).
-/
import Perennial.Golang.Defn.Loop
import Perennial.Golang.Defn.Assume
import Perennial.Golang.Defn.Predeclared
import Perennial.Code.github_com.mit_pdos.perennial.goose.model.strings

namespace Perennial

namespace go

/-- Lexicographic order on byte strings (Rocq: stdpp `lexico` with
`w8_lexico x y := uint.Z x < uint.Z y`). -/
def go_string_lt : go_string → go_string → Prop :=
  List.Lex (fun (x y : w8) => uint.Z x < uint.Z y)

instance go_string_lt_dec : DecidableRel go_string_lt :=
  fun x y => inferInstanceAs (Decidable (List.Lex _ x y))

example :
    ¬ go_string_lt go!"" go!"" ∧
    go_string_lt go!"" go!"a" ∧
    ¬ go_string_lt go!"a" go!"" ∧
    ¬ go_string_lt go!"ab" go!"a" ∧
    go_string_lt go!"ab" go!"b" := by
  decide

def go_string_le (x y : go_string) : Prop :=
  x = y ∨ go_string_lt x y

instance go_string_le_dec : DecidableRel go_string_le :=
  fun x y => inferInstanceAs (Decidable (x = y ∨ go_string_lt x y))

section defs
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext]
open github_com.mit_pdos.perennial.goose.model

class StringSemantics [GoSemanticsFunctions] : Prop where
  [package_sem : strings.Assumptions]

  internal_string_len_step (s : go_string) :
    ⟦InternalStringLen, #s⟧ ⤳ (if s.length < 2^63 then
                                  (Val #(W64 s.length))
                                else AngelicExit #())

  string_len_unfold {t : go.type} [t ↓u go.string] : FuncUnfold go.len [t]
    (λ: "s", InternalStringLen "s" : val)

  string_index (s : go_string) (i : w64) :
    ⟦Index go.string, (#s, #i)⟧ ⤳[under]
    (match s[sint.nat i]? with | some b => #b | _ => Panic "index out of bounds")

  convert_byte_to_string (c : w8) :
    ⟦Convert go.byte go.string, #c⟧ ⤳[under] #([c] : go_string)

  convert_bytes_to_string {from_ elem_type to : go.type}
    [from_ ↓u go.SliceType elem_type] [elem_type ↓u go.byte] [to ↓u go.string] (v : val) :
    ⟦Convert from_ to, v⟧ ⤳[internal] (@! strings.ByteSliceToString v)

  convert_string_to_bytes {from_ to elem_type : go.type}
    [from_ ↓u go.string] [to ↓u go.SliceType elem_type] [elem_type ↓u go.byte] (v : val) :
    ⟦Convert from_ to, v⟧ ⤳[internal] (@! strings.StringToByteSlice v)

  lt_string (x y : go_string) :
    ⟦GoOp GoLt go.string, (#x, #y)⟧ ⤳[under] #(decide (go_string_lt x y))

  le_string (x y : go_string) :
    ⟦GoOp GoLe go.string, (#x, #y)⟧ ⤳[under] #(decide (go_string_le x y))

  gt_string (x y : go_string) :
    ⟦GoOp GoGt go.string, (#x, #y)⟧ ⤳[under] #(decide (go_string_lt y x))

  ge_string (x y : go_string) :
    ⟦GoOp GoGe go.string, (#x, #y)⟧ ⤳[under] #(decide (go_string_le y x))

attribute [instance] StringSemantics.package_sem StringSemantics.internal_string_len_step
  StringSemantics.string_len_unfold StringSemantics.string_index
  StringSemantics.convert_byte_to_string StringSemantics.convert_bytes_to_string
  StringSemantics.convert_string_to_bytes StringSemantics.lt_string StringSemantics.le_string
  StringSemantics.gt_string StringSemantics.ge_string
export StringSemantics (internal_string_len_step string_len_unfold string_index
  convert_byte_to_string convert_bytes_to_string convert_string_to_bytes lt_string le_string
  gt_string ge_string)

end defs
end go

end Perennial
