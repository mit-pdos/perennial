/-
Port of `new/golang/theory/string.v`: specs for the conversions between strings
and byte slices, which are implemented by the Go model
`github.com/mit-pdos/perennial/goose/model/strings` (proved in
`Perennial/Proof/github_com/mit_pdos/perennial/goose/model/strings.lean`).
-/
import Perennial.Golang.Defn.String
import Perennial.Golang.Theory.Pre
import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics] [go.StringSemantics]
variable {s : Stuckness} {E : CoPset}

open github_com.mit_pdos.perennial.goose.model.strings in
attribute [local instance] go.tagged_internal_inst in
theorem wp_string_to_bytes (str : go_string) {from_ to elem_type : go.type}
    [to ↓u go.SliceType elem_type] [elem_type ↓u go.byte] [from_ ↓u go.string] :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (Convert from_ to))) (Val #str)) @ s; E
    {{ (sl : slice.t), RET #sl; sl ↦* str ∗ own_slice_cap w8 sl (DFrac.own 1) }} := by
  iintro %Φ _ HΦ
  wp_pure
  wp_apply wp_StringToByteSlice str with %sl Hsl
  iapply HΦ $$ Hsl

open github_com.mit_pdos.perennial.goose.model.strings in
attribute [local instance] go.tagged_internal_inst in
theorem wp_bytes_to_string (sl : slice.t) (str : go_string) (dq : DFrac)
    {from_ elem_type to : go.type}
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
