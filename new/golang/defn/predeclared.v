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
    #[global] go_eq_Pointer :: go.AlwaysSafelyComparable Pointer loc;
  }.
End unsafe.

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
.

Inductive is_predeclared_zero_val : go.type → val → Prop :=
| is_predeclared_zero_val_uint : is_predeclared_zero_val go.uint #(W64 0)
| is_predeclared_zero_val_uint8 : is_predeclared_zero_val go.uint8 #(W8 0)
| is_predeclared_zero_val_uint16 : is_predeclared_zero_val go.uint16 #(W16 0)
| is_predeclared_zero_val_uint32 : is_predeclared_zero_val go.uint32 #(W32 0)
| is_predeclared_zero_val_uint64 : is_predeclared_zero_val go.uint64 #(W64 0)
| is_predeclared_zero_val_int : is_predeclared_zero_val go.int #(W64 0)
| is_predeclared_zero_val_int8 : is_predeclared_zero_val go.int8 #(W8 0)
| is_predeclared_zero_val_int16 : is_predeclared_zero_val go.int16 #(W16 0)
| is_predeclared_zero_val_int32 : is_predeclared_zero_val go.int32 #(W32 0)
| is_predeclared_zero_val_int64 : is_predeclared_zero_val go.int64 #(W64 0)
| is_predeclared_zero_val_string : is_predeclared_zero_val go.string #""%go
| is_predeclared_zero_val_bool : is_predeclared_zero_val go.bool #false.

Class IntSemantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int :: go.TypeRepr go.int w64;
  #[global] comparable_int :: go.IsComparable go.int;
  #[global] go_eq_int :: go.AlwaysSafelyComparable go.int w64;
  #[global] le_int (v1 v2 : w64) :: go.IsGoOp GoLe go.int (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int (v1 v2 : w64) :: go.IsGoOp GoLt go.int (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int (v1 v2 : w64) :: go.IsGoOp GoGe go.int (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int (v1 v2 : w64) :: go.IsGoOp GoGt go.int (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int (v1 v2 : w64) :: go.IsGoOp GoPlus go.int (#v1, #v2) #(word.add v1 v2);
  #[global] sub_int (v1 v2 : w64) :: go.IsGoOp GoSub go.int (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_int (v1 v2 : w64) :: go.IsGoOp GoMul go.int (#v1, #v2) #(word.mul v1 v2);
  #[global] div_int (v1 v2 : w64) :: go.IsGoOp GoDiv go.int (#v1, #v2) #(word.divs v1 v2);
  #[global] remainder_int (v1 v2 : w64) :: go.IsGoOp GoRemainder go.int (#v1, #v2) #(word.mods v1 v2);
  #[global] and_int (v1 v2 : w64) :: go.IsGoOp GoAnd go.int (#v1, #v2) #(word.and v1 v2);
  #[global] or_int (v1 v2 : w64) :: go.IsGoOp GoOr go.int (#v1, #v2) #(word.or v1 v2);
  #[global] xor_int (v1 v2 : w64) :: go.IsGoOp GoXor go.int (#v1, #v2) #(word.xor v1 v2);
}.
Class Int64Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int64 :: go.TypeRepr go.int64 w64;
  #[global] comparable_int64 :: go.IsComparable go.int64;
  #[global] go_eq_int64 :: go.AlwaysSafelyComparable go.int64 w64;
  #[global] le_int64 (v1 v2 : w64) :: go.IsGoOp GoLe go.int64 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int64 (v1 v2 : w64) :: go.IsGoOp GoLt go.int64 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int64 (v1 v2 : w64) :: go.IsGoOp GoGe go.int64 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int64 (v1 v2 : w64) :: go.IsGoOp GoGt go.int64 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int64 (v1 v2 : w64) :: go.IsGoOp GoPlus go.int64 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_int64 (v1 v2 : w64) :: go.IsGoOp GoSub go.int64 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_int64 (v1 v2 : w64) :: go.IsGoOp GoMul go.int64 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_int64 (v1 v2 : w64) :: go.IsGoOp GoDiv go.int64 (#v1, #v2) #(word.divs v1 v2);
  #[global] remainder_int64 (v1 v2 : w64) :: go.IsGoOp GoRemainder go.int64 (#v1, #v2) #(word.mods v1 v2);
  #[global] and_int64 (v1 v2 : w64) :: go.IsGoOp GoAnd go.int64 (#v1, #v2) #(word.and v1 v2);
  #[global] or_int64 (v1 v2 : w64) :: go.IsGoOp GoOr go.int64 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_int64 (v1 v2 : w64) :: go.IsGoOp GoXor go.int64 (#v1, #v2) #(word.xor v1 v2);
}.
Class Int32Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int32 :: go.TypeRepr go.int32 w32;
  #[global] comparable_int32 :: go.IsComparable go.int32;
  #[global] go_eq_int32 :: go.AlwaysSafelyComparable go.int32 w32;
  #[global] le_int32 (v1 v2 : w32) :: go.IsGoOp GoLe go.int32 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int32 (v1 v2 : w32) :: go.IsGoOp GoLt go.int32 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int32 (v1 v2 : w32) :: go.IsGoOp GoGe go.int32 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int32 (v1 v2 : w32) :: go.IsGoOp GoGt go.int32 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int32 (v1 v2 : w32) :: go.IsGoOp GoPlus go.int32 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_int32 (v1 v2 : w32) :: go.IsGoOp GoSub go.int32 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_int32 (v1 v2 : w32) :: go.IsGoOp GoMul go.int32 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_int32 (v1 v2 : w32) :: go.IsGoOp GoDiv go.int32 (#v1, #v2) #(word.divs v1 v2);
  #[global] remainder_int32 (v1 v2 : w32) :: go.IsGoOp GoRemainder go.int32 (#v1, #v2) #(word.mods v1 v2);
  #[global] and_int32 (v1 v2 : w32) :: go.IsGoOp GoAnd go.int32 (#v1, #v2) #(word.and v1 v2);
  #[global] or_int32 (v1 v2 : w32) :: go.IsGoOp GoOr go.int32 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_int32 (v1 v2 : w32) :: go.IsGoOp GoXor go.int32 (#v1, #v2) #(word.xor v1 v2);
}.
Class Int16Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int16 :: go.TypeRepr go.int16 w16;
  #[global] comparable_int16 :: go.IsComparable go.int16;
  #[global] go_eq_int16 :: go.AlwaysSafelyComparable go.int16 w16;
  #[global] le_int16 (v1 v2 : w16) :: go.IsGoOp GoLe go.int16 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int16 (v1 v2 : w16) :: go.IsGoOp GoLt go.int16 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int16 (v1 v2 : w16) :: go.IsGoOp GoGe go.int16 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int16 (v1 v2 : w16) :: go.IsGoOp GoGt go.int16 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int16 (v1 v2 : w16) :: go.IsGoOp GoPlus go.int16 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_int16 (v1 v2 : w16) :: go.IsGoOp GoSub go.int16 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_int16 (v1 v2 : w16) :: go.IsGoOp GoMul go.int16 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_int16 (v1 v2 : w16) :: go.IsGoOp GoDiv go.int16 (#v1, #v2) #(word.divs v1 v2);
  #[global] remainder_int16 (v1 v2 : w16) :: go.IsGoOp GoRemainder go.int16 (#v1, #v2) #(word.mods v1 v2);
  #[global] and_int16 (v1 v2 : w16) :: go.IsGoOp GoAnd go.int16 (#v1, #v2) #(word.and v1 v2);
  #[global] or_int16 (v1 v2 : w16) :: go.IsGoOp GoOr go.int16 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_int16 (v1 v2 : w16) :: go.IsGoOp GoXor go.int16 (#v1, #v2) #(word.xor v1 v2);
}.
Class Int8Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_int8 :: go.TypeRepr go.int8 w8;
  #[global] comparable_int8 :: go.IsComparable go.int8;
  #[global] go_eq_int8 :: go.AlwaysSafelyComparable go.int8 w8;
  #[global] le_int8 (v1 v2 : w8) :: go.IsGoOp GoLe go.int8 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] lt_int8 (v1 v2 : w8) :: go.IsGoOp GoLt go.int8 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] ge_int8 (v1 v2 : w8) :: go.IsGoOp GoGe go.int8 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] gt_int8 (v1 v2 : w8) :: go.IsGoOp GoGt go.int8 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] plus_int8 (v1 v2 : w8) :: go.IsGoOp GoPlus go.int8 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_int8 (v1 v2 : w8) :: go.IsGoOp GoSub go.int8 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_int8 (v1 v2 : w8) :: go.IsGoOp GoMul go.int8 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_int8 (v1 v2 : w8) :: go.IsGoOp GoDiv go.int8 (#v1, #v2) #(word.divs v1 v2);
  #[global] remainder_int8 (v1 v2 : w8) :: go.IsGoOp GoRemainder go.int8 (#v1, #v2) #(word.mods v1 v2);
  #[global] and_int8 (v1 v2 : w8) :: go.IsGoOp GoAnd go.int8 (#v1, #v2) #(word.and v1 v2);
  #[global] or_int8 (v1 v2 : w8) :: go.IsGoOp GoOr go.int8 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_int8 (v1 v2 : w8) :: go.IsGoOp GoXor go.int8 (#v1, #v2) #(word.xor v1 v2);
}.
Class UintSemantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint :: go.TypeRepr go.uint w64;
  #[global] comparable_uint :: go.IsComparable go.uint;
  #[global] go_eq_uint :: go.AlwaysSafelyComparable go.uint w64;
  #[global] le_uint (v1 v2 : w64) :: go.IsGoOp GoLe go.uint (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint (v1 v2 : w64) :: go.IsGoOp GoLt go.uint (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint (v1 v2 : w64) :: go.IsGoOp GoGe go.uint (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint (v1 v2 : w64) :: go.IsGoOp GoGt go.uint (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint (v1 v2 : w64) :: go.IsGoOp GoPlus go.uint (#v1, #v2) #(word.add v1 v2);
  #[global] sub_uint (v1 v2 : w64) :: go.IsGoOp GoSub go.uint (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_uint (v1 v2 : w64) :: go.IsGoOp GoMul go.uint (#v1, #v2) #(word.mul v1 v2);
  #[global] div_uint (v1 v2 : w64) :: go.IsGoOp GoDiv go.uint (#v1, #v2) #(word.divu v1 v2);
  #[global] remainder_uint (v1 v2 : w64) :: go.IsGoOp GoRemainder go.uint (#v1, #v2) #(word.modu v1 v2);
  #[global] and_uint (v1 v2 : w64) :: go.IsGoOp GoAnd go.uint (#v1, #v2) #(word.and v1 v2);
  #[global] or_uint (v1 v2 : w64) :: go.IsGoOp GoOr go.uint (#v1, #v2) #(word.or v1 v2);
  #[global] xor_uint (v1 v2 : w64) :: go.IsGoOp GoXor go.uint (#v1, #v2) #(word.xor v1 v2);
}.
Class Uint64Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint64 :: go.TypeRepr go.uint64 w64;
  #[global] comparable_uint64 :: go.IsComparable go.uint64;
  #[global] go_eq_uint64 :: go.AlwaysSafelyComparable go.uint64 w64;
  #[global] le_uint64 (v1 v2 : w64) :: go.IsGoOp GoLe go.uint64 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint64 (v1 v2 : w64) :: go.IsGoOp GoLt go.uint64 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint64 (v1 v2 : w64) :: go.IsGoOp GoGe go.uint64 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint64 (v1 v2 : w64) :: go.IsGoOp GoGt go.uint64 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint64 (v1 v2 : w64) :: go.IsGoOp GoPlus go.uint64 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_uint64 (v1 v2 : w64) :: go.IsGoOp GoSub go.uint64 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_uint64 (v1 v2 : w64) :: go.IsGoOp GoMul go.uint64 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_uint64 (v1 v2 : w64) :: go.IsGoOp GoDiv go.uint64 (#v1, #v2) #(word.divu v1 v2);
  #[global] remainder_uint64 (v1 v2 : w64) :: go.IsGoOp GoRemainder go.uint64 (#v1, #v2) #(word.modu v1 v2);
  #[global] and_uint64 (v1 v2 : w64) :: go.IsGoOp GoAnd go.uint64 (#v1, #v2) #(word.and v1 v2);
  #[global] or_uint64 (v1 v2 : w64) :: go.IsGoOp GoOr go.uint64 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_uint64 (v1 v2 : w64) :: go.IsGoOp GoXor go.uint64 (#v1, #v2) #(word.xor v1 v2);
}.
Class Uint32Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint32 :: go.TypeRepr go.uint32 w32;
  #[global] comparable_uint32 :: go.IsComparable go.uint32;
  #[global] go_eq_uint32 :: go.AlwaysSafelyComparable go.uint32 w32;
  #[global] le_uint32 (v1 v2 : w32) :: go.IsGoOp GoLe go.uint32 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint32 (v1 v2 : w32) :: go.IsGoOp GoLt go.uint32 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint32 (v1 v2 : w32) :: go.IsGoOp GoGe go.uint32 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint32 (v1 v2 : w32) :: go.IsGoOp GoGt go.uint32 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint32 (v1 v2 : w32) :: go.IsGoOp GoPlus go.uint32 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_uint32 (v1 v2 : w32) :: go.IsGoOp GoSub go.uint32 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_uint32 (v1 v2 : w32) :: go.IsGoOp GoMul go.uint32 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_uint32 (v1 v2 : w32) :: go.IsGoOp GoDiv go.uint32 (#v1, #v2) #(word.divs v1 v2);
  #[global] remainder_uint32 (v1 v2 : w32) :: go.IsGoOp GoRemainder go.uint32 (#v1, #v2) #(word.mods v1 v2);
  #[global] and_uint32 (v1 v2 : w32) :: go.IsGoOp GoAnd go.uint32 (#v1, #v2) #(word.and v1 v2);
  #[global] or_uint32 (v1 v2 : w32) :: go.IsGoOp GoOr go.uint32 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_uint32 (v1 v2 : w32) :: go.IsGoOp GoXor go.uint32 (#v1, #v2) #(word.xor v1 v2);
}.
Class Uint16Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint16 :: go.TypeRepr go.uint16 w16;
  #[global] comparable_uint16 :: go.IsComparable go.uint16;
  #[global] go_eq_uint16 :: go.AlwaysSafelyComparable go.uint16 w16;
  #[global] le_uint16 (v1 v2 : w16) :: go.IsGoOp GoLe go.uint16 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint16 (v1 v2 : w16) :: go.IsGoOp GoLt go.uint16 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint16 (v1 v2 : w16) :: go.IsGoOp GoGe go.uint16 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint16 (v1 v2 : w16) :: go.IsGoOp GoGt go.uint16 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint16 (v1 v2 : w16) :: go.IsGoOp GoPlus go.uint16 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_uint16 (v1 v2 : w16) :: go.IsGoOp GoSub go.uint16 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_uint16 (v1 v2 : w16) :: go.IsGoOp GoMul go.uint16 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_uint16 (v1 v2 : w16) :: go.IsGoOp GoDiv go.uint16 (#v1, #v2) #(word.divu v1 v2);
  #[global] remainder_uint16 (v1 v2 : w16) :: go.IsGoOp GoRemainder go.uint16 (#v1, #v2) #(word.modu v1 v2);
  #[global] and_uint16 (v1 v2 : w16) :: go.IsGoOp GoAnd go.uint16 (#v1, #v2) #(word.and v1 v2);
  #[global] or_uint16 (v1 v2 : w16) :: go.IsGoOp GoOr go.uint16 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_uint16 (v1 v2 : w16) :: go.IsGoOp GoXor go.uint16 (#v1, #v2) #(word.xor v1 v2);
}.
Class Uint8Semantics `{!GoSemanticsFunctions} :=
{
  #[global] type_repr_uint8 :: go.TypeRepr go.uint8 w8;
  #[global] comparable_uint8 :: go.IsComparable go.uint8;
  #[global] go_eq_uint8 :: go.AlwaysSafelyComparable go.uint8 w8;
  #[global] le_uint8 (v1 v2 : w8) :: go.IsGoOp GoLe go.uint8 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] lt_uint8 (v1 v2 : w8) :: go.IsGoOp GoLt go.uint8 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] ge_uint8 (v1 v2 : w8) :: go.IsGoOp GoGe go.uint8 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] gt_uint8 (v1 v2 : w8) :: go.IsGoOp GoGt go.uint8 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] plus_uint8 (v1 v2 : w8) :: go.IsGoOp GoPlus go.uint8 (#v1, #v2) #(word.add v1 v2);
  #[global] sub_uint8 (v1 v2 : w8) :: go.IsGoOp GoSub go.uint8 (#v1, #v2) #(word.sub v1 v2);
  #[global] mul_uint8 (v1 v2 : w8) :: go.IsGoOp GoMul go.uint8 (#v1, #v2) #(word.mul v1 v2);
  #[global] div_uint8 (v1 v2 : w8) :: go.IsGoOp GoDiv go.uint8 (#v1, #v2) #(word.divu v1 v2);
  #[global] remainder_uint8 (v1 v2 : w8) :: go.IsGoOp GoRemainder go.uint8 (#v1, #v2) #(word.modu v1 v2);
  #[global] and_uint8 (v1 v2 : w8) :: go.IsGoOp GoAnd go.uint8 (#v1, #v2) #(word.and v1 v2);
  #[global] or_uint8 (v1 v2 : w8) :: go.IsGoOp GoOr go.uint8 (#v1, #v2) #(word.or v1 v2);
  #[global] xor_uint8 (v1 v2 : w8) :: go.IsGoOp GoXor go.uint8 (#v1, #v2) #(word.xor v1 v2);
}.

Class PredeclaredSemantics `{!GoSemanticsFunctions} :=
{
  alloc_predeclared t (H : is_predeclared t) : alloc t = (λ: "v", go.ref_one "v")%V;
  load_predeclared t (H : is_predeclared t) : load t = (λ: "l", Read "l")%V;
  store_predeclared t (H : is_predeclared t) : store t = (λ: "l" "v", "l" <- "v")%V;

  predeclared_underlying t (H : is_predeclared t) : to_underlying t = t;

  len_underlying t : functions len [t] = functions len [to_underlying t];
  cap_underlying t : functions cap [t] = functions cap [to_underlying t];
  clear_underlying t : functions clear [t] = functions clear [to_underlying t];
  copy_underlying t : functions copy [t] = functions copy [to_underlying t];
  delete_underlying t : functions delete [t] = functions delete [to_underlying t];
  make3_underlying t : functions make3 [t] = functions make3 [to_underlying t];
  make2_underlying t : functions make2 [t] = functions make2 [to_underlying t];
  make1_underlying t : functions make1 [t] = functions make1 [to_underlying t];

  min_ordered n t : #(functions min (replicate n t)) = minⁱᵐᵖˡ t n;
  max_ordered n t : #(functions max (replicate n t)) = maxⁱᵐᵖˡ t n;

  #[global] unsafe_sem :: unsafe.Semantics;
  #[global] comparable_bool :: go.IsComparable go.bool;
  #[global] go_eq_bool :: go.AlwaysSafelyComparable go.bool Datatypes.bool;
  #[global] type_repr_bool :: go.TypeRepr go.bool Datatypes.bool;

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

  #[global] comparable_string :: go.IsComparable go.string;
  #[global] go_eq_string :: go.AlwaysSafelyComparable go.string go_string;
  #[global] plus_string (v1 v2 : go_string) :: go.IsGoOp GoPlus go.string (#v1, #v2) #(v1 ++ v2);
  #[global] type_repr_string :: go.TypeRepr go.string go_string;
  index_string i (s : go_string) b (Hinrange : s !! (Z.to_nat i) = Some b) :
    index (go.string) i #s = #b;

  #[global] string_len_unfold :: FuncUnfold len [go.string]
    (λ: "s",
       if: IsNoStringOverflow "s" then
         StringLength "s"
       else AngelicExit #())%V;

  #[global] string_index (s : go_string) i ::
    go.GoExprEq (index go.string i #s)
    (match (s !! (Z.to_nat i)) with
     | Some b => #b
     | _ => Panic "index out of bounds"
     end);
}.

End defs.
End go.
