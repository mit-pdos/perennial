From New.golang.defn Require Export postlang.

Section helpers.
Context {ext : ffi_syntax}.
(* Implementations for max and min for integer types. *)

Definition minⁱᵐᵖˡ t (n : nat) : val :=
  match n with
  | 2%nat => (λ: "x" "y", if: ("x" <⟨t⟩ "y")%E then "x" else "y")%V
  | _ => LitV $ LitPoison
  end.

Definition maxⁱᵐᵖˡ t (n : nat) : val :=
  match n with
  | 2%nat => (λ: "x" "y", if: "x" >⟨t⟩ "y" then "x" else "y")%V
  | _ => LitV $ LitPoison
  end.

End helpers.

Module unsafe.
Definition Pointer : go.type := go.Named "unsafe.Pointer"%go [].
Class Semantics {ext : ffi_syntax} {go_lctx : GoLocalContext}
  {go_gctx : GoGlobalContext} `{!GoSemanticsFunctions} :=
  {
    #[global] type_repr_Pointer :: go.TypeRepr Pointer loc;
    #[global] go_eq_Pointer :: go.IsStrictlyComparable Pointer loc;
    #[global] underlying_pointer :: unsafe.Pointer ↓u unsafe.Pointer;
    #[global] convert_unsafe_to_pointer elem (l : loc) ::
      ⟦Convert unsafe.Pointer (go.PointerType elem), #l⟧ ⤳[under] #l;
    #[global] convert_pointer_to_unsafe elem (l : loc) ::
      ⟦Convert (go.PointerType elem) unsafe.Pointer, #l⟧ ⤳[under] #l;
  }.
End unsafe.

Module any.
Definition t {ext : ffi_syntax} := interface.t.
End any.


Module go.

(* Functions from https://go.dev/ref/spec#Predeclared_identifiers *)
Definition append : go_string := "append".
Definition cap : go_string := "cap".
Definition clear : go_string := "clear".
Definition close : go_string := "close".
Definition complex : go_string := "close".
Definition copy : go_string := "copy".
Definition delete : go_string := "delete".
Definition imag : go_string := "imag".
Definition len : go_string := "len".
Definition make3 : go_string := "make3".
Definition make2 : go_string := "make2".
Definition make1 : go_string := "make1".
Definition max : go_string := "max".
Definition min : go_string := "min".
(* Instead of [Definition new], the model uses [GoAlloc] *)
Definition panic : go_string := "panic".
Definition print : go_string := "print".
Definition println : go_string := "println".
Definition real : go_string := "real".
Definition recover : go_string := "recover".

(* Types from https://go.dev/ref/spec#Predeclared_identifiers *)
Definition any : go.type := go.InterfaceType [].
Definition bool : go.type := go.Named "bool"%go [].
(*         byte is aliased below *)
(*         comparable is omitted: it's only used in type
           constraints and does not affect executions *)
Definition complex64 : go.type := go.Named "complex64"%go [].
Definition complex128 : go.type := go.Named "complex128"%go [].
(*         error is aliased below, after defining string. *)
Definition float32: go.type := go.Named "float32"%go [].
Definition float64 : go.type := go.Named "float64"%go [].
Definition int : go.type := go.Named "int"%go [].
Definition int8 : go.type := go.Named "int8"%go [].
Definition int16 : go.type := go.Named "int16"%go [].
Definition int32 : go.type := go.Named "int32"%go [].
Definition int64 : go.type := go.Named "int64"%go [].
Definition rune : go.type := int32.
Definition string : go.type := go.Named "string"%go [].
Definition error : go.type :=
  go.InterfaceType [go.MethodElem "Error"%go (go.Signature [] false [go.string])].

Definition uint : go.type := go.Named "uint"%go [].
Definition uint8 : go.type := go.Named "uint8"%go [].
Definition byte : go.type := uint8.
Definition uint16 : go.type := go.Named "uint16"%go [].
Definition uint32 : go.type := go.Named "uint32"%go [].
Definition uint64 : go.type := go.Named "uint64"%go [].
Definition uintptr : go.type := go.Named "uintptr"%go [].

(* Untyped types *)
Definition untyped_int := go.Named "untyped int"%go [].
Definition untyped_string := go.Named "untyped string"%go [].
Definition untyped_bool := go.Named "untyped bool"%go [].
Definition untyped_nil := go.Named "untyped nil"%go [].
Definition untyped_float := go.Named "untyped float"%go [].
Definition untyped_rune := untyped_int.

Definition proph_id := go.Named "proph id"%go [].

Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

(** These are the predeclareds that are modeled as taking up a single heap
    location. *)
Inductive is_predeclared : go.type → Prop :=
| is_predeclared_uint : is_predeclared go.uint
| is_predeclared_uint8 : is_predeclared go.uint8
| is_predeclared_uint16 : is_predeclared go.uint16
| is_predeclared_uint32 : is_predeclared go.uint32
| is_predeclared_uint64 : is_predeclared go.uint64
| is_predeclared_int : is_predeclared go.int
| is_predeclared_int8 : is_predeclared go.int8
| is_predeclared_int16 : is_predeclared go.int16
| is_predeclared_int32 : is_predeclared go.int32
| is_predeclared_int64 : is_predeclared go.int64
| is_predeclared_string : is_predeclared go.string
| is_predeclared_bool : is_predeclared go.bool
| is_predeclared_Pointer : is_predeclared unsafe.Pointer
| is_predeclared_float32 : is_predeclared go.float32
| is_predeclared_float64 : is_predeclared go.float64

(* Treating this like a predeclared too. *)
| is_predeclared_proph_id : is_predeclared go.proph_id.

Class ProphIdSemantics `{!GoSemanticsFunctions} :=
{
  #[global] underlying_proph_id :: go.proph_id ↓u go.proph_id;
  #[global] type_repr_proph_id :: go.TypeRepr go.proph_id goose_lang.proph_id;
}.
Class UntypedIntSemantics `{!GoSemanticsFunctions} :=
{
  #[global] underlying_untyped_int :: go.untyped_int ↓u go.untyped_int;
  #[global] neg_untyped_int (v : Z) ::
    ⟦GoUnOp GoNeg go.untyped_int, #v⟧ ⤳ #(-v);

  #[global] convert_untyped_int_to_int (v : Z) :: ⟦Convert go.untyped_int go.int, #v⟧ ⤳[under] #(W64 v);
  #[global] convert_untyped_int_to_int64 (v : Z) :: ⟦Convert go.untyped_int go.int64, #v⟧ ⤳[under] #(W64 v);
  #[global] convert_untyped_int_to_int32 (v : Z) :: ⟦Convert go.untyped_int go.int32, #v⟧ ⤳[under] #(W32 v);
  #[global] convert_untyped_int_to_int16 (v : Z) :: ⟦Convert go.untyped_int go.int16, #v⟧ ⤳[under] #(W16 v);
  #[global] convert_untyped_int_to_int8 (v : Z) :: ⟦Convert go.untyped_int go.int8, #v⟧ ⤳[under] #(W8 v);
  #[global] convert_untyped_int_to_uint (v : Z) :: ⟦Convert go.untyped_int go.uint, #v⟧ ⤳[under] #(W64 v);
  #[global] convert_untyped_int_to_uint64 (v : Z) :: ⟦Convert go.untyped_int go.uint64, #v⟧ ⤳[under] #(W64 v);
  #[global] convert_untyped_int_to_uint32 (v : Z) :: ⟦Convert go.untyped_int go.uint32, #v⟧ ⤳[under] #(W32 v);
  #[global] convert_untyped_int_to_uint16 (v : Z) :: ⟦Convert go.untyped_int go.uint16, #v⟧ ⤳[under] #(W16 v);
  #[global] convert_untyped_int_to_uint8 (v : Z) :: ⟦Convert go.untyped_int go.uint8, #v⟧ ⤳[under] #(W8 v);
}.
Class IntSemantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int :: go.TypeRepr go.int w64;
  #[global] comparable_int :: ⟦CheckComparable go.int, #()⟧ ⤳[under] #();
  #[global] underlying_int :: go.int ↓u go.int;
  #[global] go_eq_int :: go.IsStrictlyComparable go.int w64;
  #[global] le_int (v1 v2 : w64) :: ⟦GoOp GoLe go.int, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int (v1 v2 : w64) :: ⟦GoOp GoLt go.int, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int (v1 v2 : w64) :: ⟦GoOp GoGe go.int, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int (v1 v2 : w64) :: ⟦GoOp GoGt go.int, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int (v1 v2 : w64) :: ⟦GoOp GoPlus go.int, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_int (v1 v2 : w64) :: ⟦GoOp GoSub go.int, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_int (v1 v2 : w64) :: ⟦GoOp GoMul go.int, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_int (v1 v2 : w64) :: ⟦GoOp GoDiv go.int, (#v1, #v2)⟧ ⤳[under] #(word.divs v1 v2);
  #[global] remainder_int (v1 v2 : w64) :: ⟦GoOp GoRemainder go.int, (#v1, #v2)⟧ ⤳[under] #(word.mods v1 v2);
  #[global] and_int (v1 v2 : w64) :: ⟦GoOp GoAnd go.int, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_int (v1 v2 : w64) :: ⟦GoOp GoOr go.int, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_int (v1 v2 : w64) :: ⟦GoOp GoXor go.int, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_int (v1 v2 : w64) :: ⟦GoOp GoShiftl go.int, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_int (v1 v2 : w64) :: ⟦GoOp GoShiftr go.int, (#v1, #v2)⟧ ⤳[under] #(word.srs v1 v2);

  #[global] convert_int_to_int (v : w64) :: ⟦Convert go.int go.int, #v⟧ ⤳[under] #v;
  #[global] convert_int64_to_int (v : w64) :: ⟦Convert go.int64 go.int, #v⟧ ⤳[under] #v;
  #[global] convert_int32_to_int (v : w32) :: ⟦Convert go.int32 go.int, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int16_to_int (v : w16) :: ⟦Convert go.int16 go.int, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int8_to_int (v : w8) :: ⟦Convert go.int8 go.int, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_uint_to_int (v : w64) :: ⟦Convert go.uint go.int, #v⟧ ⤳[under] #v;
  #[global] convert_uint64_to_int (v : w64) :: ⟦Convert go.uint64 go.int, #v⟧ ⤳[under] #v;
  #[global] convert_uint32_to_int (v : w32) :: ⟦Convert go.uint32 go.int, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint16_to_int (v : w16) :: ⟦Convert go.uint16 go.int, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint8_to_int (v : w8) :: ⟦Convert go.uint8 go.int, #v⟧ ⤳[under] #((W64 $ uint.Z v));
}.
Class Int64Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int64 :: go.TypeRepr go.int64 w64;
  #[global] comparable_int64 :: ⟦CheckComparable go.int64, #()⟧ ⤳[under] #();
  #[global] underlying_int64 :: go.int64 ↓u go.int64;
  #[global] go_eq_int64 :: go.IsStrictlyComparable go.int64 w64;
  #[global] le_int64 (v1 v2 : w64) :: ⟦GoOp GoLe go.int64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int64 (v1 v2 : w64) :: ⟦GoOp GoLt go.int64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int64 (v1 v2 : w64) :: ⟦GoOp GoGe go.int64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int64 (v1 v2 : w64) :: ⟦GoOp GoGt go.int64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int64 (v1 v2 : w64) :: ⟦GoOp GoPlus go.int64, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_int64 (v1 v2 : w64) :: ⟦GoOp GoSub go.int64, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_int64 (v1 v2 : w64) :: ⟦GoOp GoMul go.int64, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_int64 (v1 v2 : w64) :: ⟦GoOp GoDiv go.int64, (#v1, #v2)⟧ ⤳[under] #(word.divs v1 v2);
  #[global] remainder_int64 (v1 v2 : w64) :: ⟦GoOp GoRemainder go.int64, (#v1, #v2)⟧ ⤳[under] #(word.mods v1 v2);
  #[global] and_int64 (v1 v2 : w64) :: ⟦GoOp GoAnd go.int64, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_int64 (v1 v2 : w64) :: ⟦GoOp GoOr go.int64, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_int64 (v1 v2 : w64) :: ⟦GoOp GoXor go.int64, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_int64 (v1 v2 : w64) :: ⟦GoOp GoShiftl go.int64, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_int64 (v1 v2 : w64) :: ⟦GoOp GoShiftr go.int64, (#v1, #v2)⟧ ⤳[under] #(word.srs v1 v2);

  #[global] convert_int_to_int64 (v : w64) :: ⟦Convert go.int go.int64, #v⟧ ⤳[under] #v;
  #[global] convert_int64_to_int64 (v : w64) :: ⟦Convert go.int64 go.int64, #v⟧ ⤳[under] #v;
  #[global] convert_int32_to_int64 (v : w32) :: ⟦Convert go.int32 go.int64, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int16_to_int64 (v : w16) :: ⟦Convert go.int16 go.int64, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int8_to_int64 (v : w8) :: ⟦Convert go.int8 go.int64, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_uint_to_int64 (v : w64) :: ⟦Convert go.uint go.int64, #v⟧ ⤳[under] #v;
  #[global] convert_uint64_to_int64 (v : w64) :: ⟦Convert go.uint64 go.int64, #v⟧ ⤳[under] #v;
  #[global] convert_uint32_to_int64 (v : w32) :: ⟦Convert go.uint32 go.int64, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint16_to_int64 (v : w16) :: ⟦Convert go.uint16 go.int64, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint8_to_int64 (v : w8) :: ⟦Convert go.uint8 go.int64, #v⟧ ⤳[under] #((W64 $ uint.Z v));
}.
Class Int32Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int32 :: go.TypeRepr go.int32 w32;
  #[global] comparable_int32 :: ⟦CheckComparable go.int32, #()⟧ ⤳[under] #();
  #[global] underlying_int32 :: go.int32 ↓u go.int32;
  #[global] go_eq_int32 :: go.IsStrictlyComparable go.int32 w32;
  #[global] le_int32 (v1 v2 : w32) :: ⟦GoOp GoLe go.int32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int32 (v1 v2 : w32) :: ⟦GoOp GoLt go.int32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int32 (v1 v2 : w32) :: ⟦GoOp GoGe go.int32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int32 (v1 v2 : w32) :: ⟦GoOp GoGt go.int32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int32 (v1 v2 : w32) :: ⟦GoOp GoPlus go.int32, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_int32 (v1 v2 : w32) :: ⟦GoOp GoSub go.int32, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_int32 (v1 v2 : w32) :: ⟦GoOp GoMul go.int32, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_int32 (v1 v2 : w32) :: ⟦GoOp GoDiv go.int32, (#v1, #v2)⟧ ⤳[under] #(word.divs v1 v2);
  #[global] remainder_int32 (v1 v2 : w32) :: ⟦GoOp GoRemainder go.int32, (#v1, #v2)⟧ ⤳[under] #(word.mods v1 v2);
  #[global] and_int32 (v1 v2 : w32) :: ⟦GoOp GoAnd go.int32, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_int32 (v1 v2 : w32) :: ⟦GoOp GoOr go.int32, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_int32 (v1 v2 : w32) :: ⟦GoOp GoXor go.int32, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_int32 (v1 v2 : w32) :: ⟦GoOp GoShiftl go.int32, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_int32 (v1 v2 : w32) :: ⟦GoOp GoShiftr go.int32, (#v1, #v2)⟧ ⤳[under] #(word.srs v1 v2);

  #[global] convert_int_to_int32 (v : w64) :: ⟦Convert go.int go.int32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_int64_to_int32 (v : w64) :: ⟦Convert go.int64 go.int32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_int32_to_int32 (v : w32) :: ⟦Convert go.int32 go.int32, #v⟧ ⤳[under] #v;
  #[global] convert_int16_to_int32 (v : w16) :: ⟦Convert go.int16 go.int32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_int8_to_int32 (v : w8) :: ⟦Convert go.int8 go.int32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_uint_to_int32 (v : w64) :: ⟦Convert go.uint go.int32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
  #[global] convert_uint64_to_int32 (v : w64) :: ⟦Convert go.uint64 go.int32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
  #[global] convert_uint32_to_int32 (v : w32) :: ⟦Convert go.uint32 go.int32, #v⟧ ⤳[under] #v;
  #[global] convert_uint16_to_int32 (v : w16) :: ⟦Convert go.uint16 go.int32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
  #[global] convert_uint8_to_int32 (v : w8) :: ⟦Convert go.uint8 go.int32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
}.
Class Int16Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int16 :: go.TypeRepr go.int16 w16;
  #[global] comparable_int16 :: ⟦CheckComparable go.int16, #()⟧ ⤳[under] #();
  #[global] underlying_int16 :: go.int16 ↓u go.int16;
  #[global] go_eq_int16 :: go.IsStrictlyComparable go.int16 w16;
  #[global] le_int16 (v1 v2 : w16) :: ⟦GoOp GoLe go.int16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int16 (v1 v2 : w16) :: ⟦GoOp GoLt go.int16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int16 (v1 v2 : w16) :: ⟦GoOp GoGe go.int16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int16 (v1 v2 : w16) :: ⟦GoOp GoGt go.int16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int16 (v1 v2 : w16) :: ⟦GoOp GoPlus go.int16, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_int16 (v1 v2 : w16) :: ⟦GoOp GoSub go.int16, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_int16 (v1 v2 : w16) :: ⟦GoOp GoMul go.int16, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_int16 (v1 v2 : w16) :: ⟦GoOp GoDiv go.int16, (#v1, #v2)⟧ ⤳[under] #(word.divs v1 v2);
  #[global] remainder_int16 (v1 v2 : w16) :: ⟦GoOp GoRemainder go.int16, (#v1, #v2)⟧ ⤳[under] #(word.mods v1 v2);
  #[global] and_int16 (v1 v2 : w16) :: ⟦GoOp GoAnd go.int16, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_int16 (v1 v2 : w16) :: ⟦GoOp GoOr go.int16, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_int16 (v1 v2 : w16) :: ⟦GoOp GoXor go.int16, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_int16 (v1 v2 : w16) :: ⟦GoOp GoShiftl go.int16, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_int16 (v1 v2 : w16) :: ⟦GoOp GoShiftr go.int16, (#v1, #v2)⟧ ⤳[under] #(word.srs v1 v2);

  #[global] convert_int_to_int16 (v : w64) :: ⟦Convert go.int go.int16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_int64_to_int16 (v : w64) :: ⟦Convert go.int64 go.int16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_int32_to_int16 (v : w32) :: ⟦Convert go.int32 go.int16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_int16_to_int16 (v : w16) :: ⟦Convert go.int16 go.int16, #v⟧ ⤳[under] #v;
  #[global] convert_int8_to_int16 (v : w8) :: ⟦Convert go.int8 go.int16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_uint_to_int16 (v : w64) :: ⟦Convert go.uint go.int16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
  #[global] convert_uint64_to_int16 (v : w64) :: ⟦Convert go.uint64 go.int16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
  #[global] convert_uint32_to_int16 (v : w32) :: ⟦Convert go.uint32 go.int16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
  #[global] convert_uint16_to_int16 (v : w16) :: ⟦Convert go.uint16 go.int16, #v⟧ ⤳[under] #v;
  #[global] convert_uint8_to_int16 (v : w8) :: ⟦Convert go.uint8 go.int16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
}.
Class Int8Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int8 :: go.TypeRepr go.int8 w8;
  #[global] comparable_int8 :: ⟦CheckComparable go.int8, #()⟧ ⤳[under] #();
  #[global] underlying_int8 :: go.int8 ↓u go.int8;
  #[global] go_eq_int8 :: go.IsStrictlyComparable go.int8 w8;
  #[global] le_int8 (v1 v2 : w8) :: ⟦GoOp GoLe go.int8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int8 (v1 v2 : w8) :: ⟦GoOp GoLt go.int8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int8 (v1 v2 : w8) :: ⟦GoOp GoGe go.int8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int8 (v1 v2 : w8) :: ⟦GoOp GoGt go.int8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int8 (v1 v2 : w8) :: ⟦GoOp GoPlus go.int8, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_int8 (v1 v2 : w8) :: ⟦GoOp GoSub go.int8, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_int8 (v1 v2 : w8) :: ⟦GoOp GoMul go.int8, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_int8 (v1 v2 : w8) :: ⟦GoOp GoDiv go.int8, (#v1, #v2)⟧ ⤳[under] #(word.divs v1 v2);
  #[global] remainder_int8 (v1 v2 : w8) :: ⟦GoOp GoRemainder go.int8, (#v1, #v2)⟧ ⤳[under] #(word.mods v1 v2);
  #[global] and_int8 (v1 v2 : w8) :: ⟦GoOp GoAnd go.int8, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_int8 (v1 v2 : w8) :: ⟦GoOp GoOr go.int8, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_int8 (v1 v2 : w8) :: ⟦GoOp GoXor go.int8, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_int8 (v1 v2 : w8) :: ⟦GoOp GoShiftl go.int8, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_int8 (v1 v2 : w8) :: ⟦GoOp GoShiftr go.int8, (#v1, #v2)⟧ ⤳[under] #(word.srs v1 v2);

  #[global] convert_int_to_int8 (v : w64) :: ⟦Convert go.int go.int8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int64_to_int8 (v : w64) :: ⟦Convert go.int64 go.int8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int32_to_int8 (v : w32) :: ⟦Convert go.int32 go.int8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int16_to_int8 (v : w16) :: ⟦Convert go.int16 go.int8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int8_to_int8 (v : w8) :: ⟦Convert go.int8 go.int8, #v⟧ ⤳[under] #v;
  #[global] convert_uint_to_int8 (v : w64) :: ⟦Convert go.uint go.int8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint64_to_int8 (v : w64) :: ⟦Convert go.uint64 go.int8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint32_to_int8 (v : w32) :: ⟦Convert go.uint32 go.int8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint16_to_int8 (v : w16) :: ⟦Convert go.uint16 go.int8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint8_to_int8 (v : w8) :: ⟦Convert go.uint8 go.int8, #v⟧ ⤳[under] #v;
}.
Class UintSemantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint :: go.TypeRepr go.uint w64;
  #[global] comparable_uint :: ⟦CheckComparable go.uint, #()⟧ ⤳[under] #();
  #[global] underlying_uint :: go.uint ↓u go.uint;
  #[global] go_eq_uint :: go.IsStrictlyComparable go.uint w64;
  #[global] le_uint (v1 v2 : w64) :: ⟦GoOp GoLe go.uint, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint (v1 v2 : w64) :: ⟦GoOp GoLt go.uint, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint (v1 v2 : w64) :: ⟦GoOp GoGe go.uint, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint (v1 v2 : w64) :: ⟦GoOp GoGt go.uint, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint (v1 v2 : w64) :: ⟦GoOp GoPlus go.uint, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_uint (v1 v2 : w64) :: ⟦GoOp GoSub go.uint, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_uint (v1 v2 : w64) :: ⟦GoOp GoMul go.uint, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_uint (v1 v2 : w64) :: ⟦GoOp GoDiv go.uint, (#v1, #v2)⟧ ⤳[under] #(word.divu v1 v2);
  #[global] remainder_uint (v1 v2 : w64) :: ⟦GoOp GoRemainder go.uint, (#v1, #v2)⟧ ⤳[under] #(word.modu v1 v2);
  #[global] and_uint (v1 v2 : w64) :: ⟦GoOp GoAnd go.uint, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_uint (v1 v2 : w64) :: ⟦GoOp GoOr go.uint, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_uint (v1 v2 : w64) :: ⟦GoOp GoXor go.uint, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_uint (v1 v2 : w64) :: ⟦GoOp GoShiftl go.uint, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_uint (v1 v2 : w64) :: ⟦GoOp GoShiftr go.uint, (#v1, #v2)⟧ ⤳[under] #(word.sru v1 v2);

  #[global] convert_int_to_uint (v : w64) :: ⟦Convert go.int go.uint, #v⟧ ⤳[under] #v;
  #[global] convert_int64_to_uint (v : w64) :: ⟦Convert go.int64 go.uint, #v⟧ ⤳[under] #v;
  #[global] convert_int32_to_uint (v : w32) :: ⟦Convert go.int32 go.uint, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int16_to_uint (v : w16) :: ⟦Convert go.int16 go.uint, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int8_to_uint (v : w8) :: ⟦Convert go.int8 go.uint, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_uint_to_uint (v : w64) :: ⟦Convert go.uint go.uint, #v⟧ ⤳[under] #v;
  #[global] convert_uint64_to_uint (v : w64) :: ⟦Convert go.uint64 go.uint, #v⟧ ⤳[under] #v;
  #[global] convert_uint32_to_uint (v : w32) :: ⟦Convert go.uint32 go.uint, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint16_to_uint (v : w16) :: ⟦Convert go.uint16 go.uint, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint8_to_uint (v : w8) :: ⟦Convert go.uint8 go.uint, #v⟧ ⤳[under] #((W64 $ uint.Z v));
}.
Class Uint64Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint64 :: go.TypeRepr go.uint64 w64;
  #[global] comparable_uint64 :: ⟦CheckComparable go.uint64, #()⟧ ⤳[under] #();
  #[global] underlying_uint64 :: go.uint64 ↓u go.uint64;
  #[global] go_eq_uint64 :: go.IsStrictlyComparable go.uint64 w64;
  #[global] le_uint64 (v1 v2 : w64) :: ⟦GoOp GoLe go.uint64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint64 (v1 v2 : w64) :: ⟦GoOp GoLt go.uint64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint64 (v1 v2 : w64) :: ⟦GoOp GoGe go.uint64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint64 (v1 v2 : w64) :: ⟦GoOp GoGt go.uint64, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint64 (v1 v2 : w64) :: ⟦GoOp GoPlus go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_uint64 (v1 v2 : w64) :: ⟦GoOp GoSub go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_uint64 (v1 v2 : w64) :: ⟦GoOp GoMul go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_uint64 (v1 v2 : w64) :: ⟦GoOp GoDiv go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.divu v1 v2);
  #[global] remainder_uint64 (v1 v2 : w64) :: ⟦GoOp GoRemainder go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.modu v1 v2);
  #[global] and_uint64 (v1 v2 : w64) :: ⟦GoOp GoAnd go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_uint64 (v1 v2 : w64) :: ⟦GoOp GoOr go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_uint64 (v1 v2 : w64) :: ⟦GoOp GoXor go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_uint64 (v1 v2 : w64) :: ⟦GoOp GoShiftl go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_uint64 (v1 v2 : w64) :: ⟦GoOp GoShiftr go.uint64, (#v1, #v2)⟧ ⤳[under] #(word.sru v1 v2);

  #[global] convert_int_to_uint64 (v : w64) :: ⟦Convert go.int go.uint64, #v⟧ ⤳[under] #v;
  #[global] convert_int64_to_uint64 (v : w64) :: ⟦Convert go.int64 go.uint64, #v⟧ ⤳[under] #v;
  #[global] convert_int32_to_uint64 (v : w32) :: ⟦Convert go.int32 go.uint64, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int16_to_uint64 (v : w16) :: ⟦Convert go.int16 go.uint64, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_int8_to_uint64 (v : w8) :: ⟦Convert go.int8 go.uint64, #v⟧ ⤳[under] #((W64 $ sint.Z v));
  #[global] convert_uint_to_uint64 (v : w64) :: ⟦Convert go.uint go.uint64, #v⟧ ⤳[under] #v;
  #[global] convert_uint64_to_uint64 (v : w64) :: ⟦Convert go.uint64 go.uint64, #v⟧ ⤳[under] #v;
  #[global] convert_uint32_to_uint64 (v : w32) :: ⟦Convert go.uint32 go.uint64, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint16_to_uint64 (v : w16) :: ⟦Convert go.uint16 go.uint64, #v⟧ ⤳[under] #((W64 $ uint.Z v));
  #[global] convert_uint8_to_uint64 (v : w8) :: ⟦Convert go.uint8 go.uint64, #v⟧ ⤳[under] #((W64 $ uint.Z v));
}.
Class Uint32Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint32 :: go.TypeRepr go.uint32 w32;
  #[global] comparable_uint32 :: ⟦CheckComparable go.uint32, #()⟧ ⤳[under] #();
  #[global] underlying_uint32 :: go.uint32 ↓u go.uint32;
  #[global] go_eq_uint32 :: go.IsStrictlyComparable go.uint32 w32;
  #[global] le_uint32 (v1 v2 : w32) :: ⟦GoOp GoLe go.uint32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint32 (v1 v2 : w32) :: ⟦GoOp GoLt go.uint32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint32 (v1 v2 : w32) :: ⟦GoOp GoGe go.uint32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint32 (v1 v2 : w32) :: ⟦GoOp GoGt go.uint32, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint32 (v1 v2 : w32) :: ⟦GoOp GoPlus go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_uint32 (v1 v2 : w32) :: ⟦GoOp GoSub go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_uint32 (v1 v2 : w32) :: ⟦GoOp GoMul go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_uint32 (v1 v2 : w32) :: ⟦GoOp GoDiv go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.divs v1 v2);
  #[global] remainder_uint32 (v1 v2 : w32) :: ⟦GoOp GoRemainder go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.mods v1 v2);
  #[global] and_uint32 (v1 v2 : w32) :: ⟦GoOp GoAnd go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_uint32 (v1 v2 : w32) :: ⟦GoOp GoOr go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_uint32 (v1 v2 : w32) :: ⟦GoOp GoXor go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_uint32 (v1 v2 : w32) :: ⟦GoOp GoShiftl go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_uint32 (v1 v2 : w32) :: ⟦GoOp GoShiftr go.uint32, (#v1, #v2)⟧ ⤳[under] #(word.sru v1 v2);

  #[global] convert_int_to_uint32 (v : w64) :: ⟦Convert go.int go.uint32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_int64_to_uint32 (v : w64) :: ⟦Convert go.int64 go.uint32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_int32_to_uint32 (v : w32) :: ⟦Convert go.int32 go.uint32, #v⟧ ⤳[under] #v;
  #[global] convert_int16_to_uint32 (v : w16) :: ⟦Convert go.int16 go.uint32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_int8_to_uint32 (v : w8) :: ⟦Convert go.int8 go.uint32, #v⟧ ⤳[under] #((W32 $ sint.Z v));
  #[global] convert_uint_to_uint32 (v : w64) :: ⟦Convert go.uint go.uint32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
  #[global] convert_uint64_to_uint32 (v : w64) :: ⟦Convert go.uint64 go.uint32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
  #[global] convert_uint32_to_uint32 (v : w32) :: ⟦Convert go.uint32 go.uint32, #v⟧ ⤳[under] #v;
  #[global] convert_uint16_to_uint32 (v : w16) :: ⟦Convert go.uint16 go.uint32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
  #[global] convert_uint8_to_uint32 (v : w8) :: ⟦Convert go.uint8 go.uint32, #v⟧ ⤳[under] #((W32 $ uint.Z v));
}.
Class Uint16Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint16 :: go.TypeRepr go.uint16 w16;
  #[global] comparable_uint16 :: ⟦CheckComparable go.uint16, #()⟧ ⤳[under] #();
  #[global] underlying_uint16 :: go.uint16 ↓u go.uint16;
  #[global] go_eq_uint16 :: go.IsStrictlyComparable go.uint16 w16;
  #[global] le_uint16 (v1 v2 : w16) :: ⟦GoOp GoLe go.uint16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint16 (v1 v2 : w16) :: ⟦GoOp GoLt go.uint16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint16 (v1 v2 : w16) :: ⟦GoOp GoGe go.uint16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint16 (v1 v2 : w16) :: ⟦GoOp GoGt go.uint16, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint16 (v1 v2 : w16) :: ⟦GoOp GoPlus go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_uint16 (v1 v2 : w16) :: ⟦GoOp GoSub go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_uint16 (v1 v2 : w16) :: ⟦GoOp GoMul go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_uint16 (v1 v2 : w16) :: ⟦GoOp GoDiv go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.divu v1 v2);
  #[global] remainder_uint16 (v1 v2 : w16) :: ⟦GoOp GoRemainder go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.modu v1 v2);
  #[global] and_uint16 (v1 v2 : w16) :: ⟦GoOp GoAnd go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_uint16 (v1 v2 : w16) :: ⟦GoOp GoOr go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_uint16 (v1 v2 : w16) :: ⟦GoOp GoXor go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_uint16 (v1 v2 : w16) :: ⟦GoOp GoShiftl go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_uint16 (v1 v2 : w16) :: ⟦GoOp GoShiftr go.uint16, (#v1, #v2)⟧ ⤳[under] #(word.sru v1 v2);

  #[global] convert_int_to_uint16 (v : w64) :: ⟦Convert go.int go.uint16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_int64_to_uint16 (v : w64) :: ⟦Convert go.int64 go.uint16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_int32_to_uint16 (v : w32) :: ⟦Convert go.int32 go.uint16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_int16_to_uint16 (v : w16) :: ⟦Convert go.int16 go.uint16, #v⟧ ⤳[under] #v;
  #[global] convert_int8_to_uint16 (v : w8) :: ⟦Convert go.int8 go.uint16, #v⟧ ⤳[under] #((W16 $ sint.Z v));
  #[global] convert_uint_to_uint16 (v : w64) :: ⟦Convert go.uint go.uint16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
  #[global] convert_uint64_to_uint16 (v : w64) :: ⟦Convert go.uint64 go.uint16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
  #[global] convert_uint32_to_uint16 (v : w32) :: ⟦Convert go.uint32 go.uint16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
  #[global] convert_uint16_to_uint16 (v : w16) :: ⟦Convert go.uint16 go.uint16, #v⟧ ⤳[under] #v;
  #[global] convert_uint8_to_uint16 (v : w8) :: ⟦Convert go.uint8 go.uint16, #v⟧ ⤳[under] #((W16 $ uint.Z v));
}.
Class Uint8Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint8 :: go.TypeRepr go.uint8 w8;
  #[global] comparable_uint8 :: ⟦CheckComparable go.uint8, #()⟧ ⤳[under] #();
  #[global] underlying_uint8 :: go.uint8 ↓u go.uint8;
  #[global] go_eq_uint8 :: go.IsStrictlyComparable go.uint8 w8;
  #[global] le_uint8 (v1 v2 : w8) :: ⟦GoOp GoLe go.uint8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint8 (v1 v2 : w8) :: ⟦GoOp GoLt go.uint8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint8 (v1 v2 : w8) :: ⟦GoOp GoGe go.uint8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint8 (v1 v2 : w8) :: ⟦GoOp GoGt go.uint8, (#v1, #v2)⟧ ⤳[under] #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint8 (v1 v2 : w8) :: ⟦GoOp GoPlus go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.add v1 v2);
  #[global] sub_uint8 (v1 v2 : w8) :: ⟦GoOp GoSub go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.sub v1 v2);
  #[global] mul_uint8 (v1 v2 : w8) :: ⟦GoOp GoMul go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.mul v1 v2);
  #[global] div_uint8 (v1 v2 : w8) :: ⟦GoOp GoDiv go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.divu v1 v2);
  #[global] remainder_uint8 (v1 v2 : w8) :: ⟦GoOp GoRemainder go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.modu v1 v2);
  #[global] and_uint8 (v1 v2 : w8) :: ⟦GoOp GoAnd go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.and v1 v2);
  #[global] or_uint8 (v1 v2 : w8) :: ⟦GoOp GoOr go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.or v1 v2);
  #[global] xor_uint8 (v1 v2 : w8) :: ⟦GoOp GoXor go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.xor v1 v2);
  #[global] shiftl_uint8 (v1 v2 : w8) :: ⟦GoOp GoShiftl go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.slu v1 v2);
  #[global] shiftr_uint8 (v1 v2 : w8) :: ⟦GoOp GoShiftr go.uint8, (#v1, #v2)⟧ ⤳[under] #(word.sru v1 v2);

  #[global] convert_int_to_uint8 (v : w64) :: ⟦Convert go.int go.uint8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int64_to_uint8 (v : w64) :: ⟦Convert go.int64 go.uint8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int32_to_uint8 (v : w32) :: ⟦Convert go.int32 go.uint8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int16_to_uint8 (v : w16) :: ⟦Convert go.int16 go.uint8, #v⟧ ⤳[under] #((W8 $ sint.Z v));
  #[global] convert_int8_to_uint8 (v : w8) :: ⟦Convert go.int8 go.uint8, #v⟧ ⤳[under] #v;
  #[global] convert_uint_to_uint8 (v : w64) :: ⟦Convert go.uint go.uint8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint64_to_uint8 (v : w64) :: ⟦Convert go.uint64 go.uint8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint32_to_uint8 (v : w32) :: ⟦Convert go.uint32 go.uint8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint16_to_uint8 (v : w16) :: ⟦Convert go.uint16 go.uint8, #v⟧ ⤳[under] #((W8 $ uint.Z v));
  #[global] convert_uint8_to_uint8 (v : w8) :: ⟦Convert go.uint8 go.uint8, #v⟧ ⤳[under] #v;
}.
Class UntypedFloatSemantics `{!GoSemanticsFunctions} :=
{
  #[global] underlying_untyped_float :: go.untyped_float ↓u go.untyped_float;
  #[global] convert_untyped_float64 (v : w64) ::
    ⟦Convert go.untyped_float go.float64, #v⟧ ⤳[under] #v;
  #[global] convert_untyped_float32 (v : w64) ::
    ⟦Convert go.untyped_float go.float32, #v⟧ ⤳[under] #(float64_to_float32 v);
}.
Class Float64Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_float64 :: go.TypeRepr go.float64 w64;
  #[global] comparable_float64:: ⟦CheckComparable go.float64, #()⟧ ⤳[under] #();
  #[global] underlying_float64 :: go.float64 ↓u go.float64;
  #[global] go_eq_float64 :: go.IsStrictlyComparable go.float64 w64;
  #[global] le_float64 (v1 v2 : w64) :: ⟦GoOp GoLe go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_leb v1 v2);
  #[global] lt_float64 (v1 v2 : w64) :: ⟦GoOp GoLt go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_leb v1 v2 && bool_decide (v1 ≠ v2));
  #[global] ge_float64 (v1 v2 : w64) :: ⟦GoOp GoGe go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_leb v2 v1);
  #[global] gt_float64 (v1 v2 : w64) :: ⟦GoOp GoGt go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_leb v2 v1 && bool_decide (v1 ≠ v2));
  #[global] plus_float64 (v1 v2 : w64) :: ⟦GoOp GoPlus go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_add v1 v2);
  #[global] sub_float64 (v1 v2 : w64) :: ⟦GoOp GoSub go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_sub v1 v2);
  #[global] mul_float64 (v1 v2 : w64) :: ⟦GoOp GoMul go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_mul v1 v2);
  #[global] div_float64 (v1 v2 : w64) :: ⟦GoOp GoDiv go.float64, (#v1, #v2)⟧ ⤳[under] #(float64_div v1 v2);
}.
Class Float32Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_float32 :: go.TypeRepr go.float32 w32;
  #[global] comparable_float32:: ⟦CheckComparable go.float32, #()⟧ ⤳[under] #();
  #[global] underlying_float32 :: go.float32 ↓u go.float32;
  #[global] go_eq_float32 :: go.IsStrictlyComparable go.float32 w32;
  #[global] le_float32 (v1 v2 : w32) :: ⟦GoOp GoLe go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_leb v1 v2);
  #[global] lt_float32 (v1 v2 : w32) :: ⟦GoOp GoLt go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_leb v1 v2 && bool_decide (v1 ≠ v2));
  #[global] ge_float32 (v1 v2 : w32) :: ⟦GoOp GoGe go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_leb v2 v1);
  #[global] gt_float32 (v1 v2 : w32) :: ⟦GoOp GoGt go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_leb v2 v1 && bool_decide (v1 ≠ v2));
  #[global] plus_float32 (v1 v2 : w32) :: ⟦GoOp GoPlus go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_add v1 v2);
  #[global] sub_float32 (v1 v2 : w32) :: ⟦GoOp GoSub go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_sub v1 v2);
  #[global] mul_float32 (v1 v2 : w32) :: ⟦GoOp GoMul go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_mul v1 v2);
  #[global] div_float32 (v1 v2 : w32) :: ⟦GoOp GoDiv go.float32, (#v1, #v2)⟧ ⤳[under] #(float32_div v1 v2);
}.

Class PredeclaredSemantics `{!GoSemanticsFunctions} :=
{
  #[global] alloc_predeclared t (H : is_predeclared t) v ::
    ⟦GoAlloc t, v⟧ ⤳[internal_under] (go.ref_one v)%E;
  #[global] load_predeclared t (H : is_predeclared t) l ::
    ⟦GoLoad t, l⟧ ⤳[internal_under] (Read l)%E;
  #[global] store_predeclared t (H : is_predeclared t) l v ::
    ⟦GoStore t, (l, v)⟧ ⤳[internal_under] (l <- v)%E;

  predeclared_underlying t (H : is_predeclared t) : underlying t = t;

  len_underlying t : functions len [t] = functions len [underlying t];
  cap_underlying t : functions cap [t] = functions cap [underlying t];
  clear_underlying t : functions clear [t] = functions clear [underlying t];
  copy_underlying t : functions copy [t] = functions copy [underlying t];
  delete_underlying t : functions delete [t] = functions delete [underlying t];
  make3_underlying t : functions make3 [t] = functions make3 [underlying t];
  make2_underlying t : functions make2 [t] = functions make2 [underlying t];
  make1_underlying t : functions make1 [t] = functions make1 [underlying t];

  min_ordered n t : #(functions min (replicate n t)) = minⁱᵐᵖˡ t n;
  max_ordered n t : #(functions max (replicate n t)) = maxⁱᵐᵖˡ t n;

  #[global] unsafe_sem :: unsafe.Semantics;

  #[global] comparable_bool :: ⟦CheckComparable go.bool, #()⟧ ⤳[under] #();
  #[global] go_eq_bool :: go.IsStrictlyComparable go.bool Datatypes.bool;
  #[global] underlying_bool :: go.bool ↓u go.bool;
  #[global] type_repr_bool :: go.TypeRepr go.bool Datatypes.bool;
  #[global] underlying_untyped_bool :: go.untyped_bool ↓u go.untyped_bool;
  #[global] convert_untyped_bool (b : Datatypes.bool) ::
    ⟦Convert go.untyped_bool go.bool, #b⟧ ⤳[under] #b;

  #[global] untyped_int_semantics :: UntypedIntSemantics;
  #[global] int_semantics :: IntSemantics;
  #[global] int64_semantics :: Int64Semantics;
  #[global] int32_semantics :: Int32Semantics;
  #[global] int16_semantics :: Int16Semantics;
  #[global] int8_semantics :: Int8Semantics;
  #[global] uint_semantics :: UintSemantics;
  #[global] uint64_semantics :: Uint64Semantics;
  #[global] uint32_semantics :: Uint32Semantics;
  #[global] uint16_semantics :: Uint16Semantics;
  #[global] uint8_semantics :: Uint8Semantics;

  #[global] untyped_float_semantics :: UntypedFloatSemantics;
  #[global] float64_semantics :: Float64Semantics;
  #[global] float32_semantics :: Float32Semantics;

  #[global] comparable_string :: ⟦CheckComparable go.string, #()⟧ ⤳[under] #();
  #[global] go_eq_string :: go.IsStrictlyComparable go.string go_string;
  #[global] underlying_string :: go.string ↓u go.string;
  #[global] plus_string (v1 v2 : go_string) :: ⟦GoOp GoPlus go.string, (#v1, #v2)⟧ ⤳[under] #(v1 ++ v2);
  #[global] type_repr_string :: go.TypeRepr go.string go_string;
  #[global] underlying_untyped_string :: go.untyped_string ↓u go.untyped_string;
  #[global] convert_untyped_string (s : go_string) ::
    ⟦Convert go.untyped_string go.string, #s⟧ ⤳[under] #s;

  #[global] underlying_untyped_nil :: go.untyped_nil ↓u go.untyped_nil;
  #[global] convert_nil_pointer elem ::
    ⟦Convert go.untyped_nil (go.PointerType elem), UntypedNil⟧ ⤳[under] #null;
  #[global] convert_nil_function sig ::
    ⟦Convert go.untyped_nil (go.FunctionType sig), UntypedNil⟧ ⤳[under] #func.nil;
  #[global] convert_nil_slice elem ::
    ⟦Convert go.untyped_nil (go.SliceType elem), UntypedNil⟧ ⤳[under] #slice.nil;
  #[global] convert_nil_chan dir elem ::
    ⟦Convert go.untyped_nil (go.ChannelType dir elem), UntypedNil⟧ ⤳[under] #chan.nil;
  #[global] convert_nil_map key elem ::
    ⟦Convert go.untyped_nil (go.MapType key elem), UntypedNil⟧ ⤳[under] #map.nil;
  #[global] convert_nil_interface elems ::
    ⟦Convert go.untyped_nil (go.InterfaceType elems), UntypedNil⟧ ⤳[under] #interface.nil;
}.

End defs.
End go.
