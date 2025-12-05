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

Inductive is_integer_type : go.type → Prop :=
| is_integer_type_uint : _ go.uint
| is_integer_type_uint64 : _ go.uint64
| is_integer_type_uint32 : _ go.uint32
| is_integer_type_uint16 : _ go.uint16
| is_integer_type_uint8 : _ go.uint8
| is_integer_type_int : _ go.int
| is_integer_type_int64 : _ go.int64
| is_integer_type_int32 : _ go.int32
| is_integer_type_int16 : _ go.int16
| is_integer_type_int8 : _ go.int8.

Existing Class is_integer_type.
Global Existing Instances
  is_integer_type_uint is_integer_type_uint64 is_integer_type_uint32
  is_integer_type_uint16 is_integer_type_uint8 is_integer_type_int
  is_integer_type_int64 is_integer_type_int32 is_integer_type_int16
  is_integer_type_int8.

Inductive is_ordered_type : go.type → Prop :=
| is_ordered_type_string : _ go.string
| is_ordered_type_numeric t (H : is_integer_type t) : _ t
.

Existing Class is_ordered_type.
Global Existing Instances is_ordered_type_string is_ordered_type_numeric.

Class PredeclaredSemantics `{!GoSemanticsFunctions} :=
{
  alloc_predeclared t v (H : is_predeclared_zero_val t v) : alloc t = (λ: <>, go.ref_one v)%V;
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

  min_ordered n t (H : is_ordered_type t) : #(functions min (replicate n t)) = minⁱᵐᵖˡ t n;
  max_ordered n t (H : is_ordered_type t) : #(functions max (replicate n t)) = maxⁱᵐᵖˡ t n;

  #[global]
  comparable_bool :: go.IsComparable go.bool;
  #[global] go_eq_bool :: go.AlwaysSafelyComparable go.bool Datatypes.bool;

  #[global] comparable_ordered t (H : is_ordered_type t) :: go.IsComparable t | 10;

  go_eq_int :: go.AlwaysSafelyComparable go.int w64;
  go_eq_int64 :: go.AlwaysSafelyComparable go.int64 w64;
  go_eq_int32 :: go.AlwaysSafelyComparable go.int32 w32;
  go_eq_int16 :: go.AlwaysSafelyComparable go.int16 w16;
  go_eq_int8 :: go.AlwaysSafelyComparable go.int8 w8;
  go_eq_uint :: go.AlwaysSafelyComparable go.uint w64;
  go_eq_uint64 :: go.AlwaysSafelyComparable go.uint64 w64;
  go_eq_uint32 :: go.AlwaysSafelyComparable go.uint32 w32;
  go_eq_uint16 :: go.AlwaysSafelyComparable go.uint16 w16;
  go_eq_uint8 :: go.AlwaysSafelyComparable go.uint8 w8;

  #[global] le_int (v1 v2 : w64) :: go.IsGoOp GoLe go.int (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] le_int64 (v1 v2 : w64) :: go.IsGoOp GoLe go.int64 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] le_int32 (v1 v2 : w32) :: go.IsGoOp GoLe go.int32 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] le_int16 (v1 v2 : w16) :: go.IsGoOp GoLe go.int16 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] le_int8 (v1 v2 : w8) :: go.IsGoOp GoLe go.int8 (#v1, #v2) #(bool_decide (sint.Z v1 ≤ sint.Z v2));
  #[global] le_uint (v1 v2 : w64) :: go.IsGoOp GoLe go.uint (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] le_uint64 (v1 v2 : w64) :: go.IsGoOp GoLe go.uint64 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] le_uint32 (v1 v2 : w32) :: go.IsGoOp GoLe go.uint32 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] le_uint16 (v1 v2 : w16) :: go.IsGoOp GoLe go.uint16 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));
  #[global] le_uint8 (v1 v2 : w8) :: go.IsGoOp GoLe go.uint8 (#v1, #v2) #(bool_decide (uint.Z v1 ≤ uint.Z v2));

  #[global] lt_int (v1 v2 : w64) :: go.IsGoOp GoLt go.int (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] lt_int64 (v1 v2 : w64) :: go.IsGoOp GoLt go.int64 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] lt_int32 (v1 v2 : w32) :: go.IsGoOp GoLt go.int32 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] lt_int16 (v1 v2 : w16) :: go.IsGoOp GoLt go.int16 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] lt_int8 (v1 v2 : w8) :: go.IsGoOp GoLt go.int8 (#v1, #v2) #(bool_decide (sint.Z v1 < sint.Z v2));
  #[global] lt_uint (v1 v2 : w64) :: go.IsGoOp GoLt go.uint (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] lt_uint64 (v1 v2 : w64) :: go.IsGoOp GoLt go.uint64 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] lt_uint32 (v1 v2 : w32) :: go.IsGoOp GoLt go.uint32 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] lt_uint16 (v1 v2 : w16) :: go.IsGoOp GoLt go.uint16 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));
  #[global] lt_uint8 (v1 v2 : w8) :: go.IsGoOp GoLt go.uint8 (#v1, #v2) #(bool_decide (uint.Z v1 < uint.Z v2));

  #[global] ge_int (v1 v2 : w64) :: go.IsGoOp GoGe go.int (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] ge_int64 (v1 v2 : w64) :: go.IsGoOp GoGe go.int64 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] ge_int32 (v1 v2 : w32) :: go.IsGoOp GoGe go.int32 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] ge_int16 (v1 v2 : w16) :: go.IsGoOp GoGe go.int16 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] ge_int8 (v1 v2 : w8) :: go.IsGoOp GoGe go.int8 (#v1, #v2) #(bool_decide (sint.Z v2 ≤ sint.Z v1));
  #[global] ge_uint (v1 v2 : w64) :: go.IsGoOp GoGe go.uint (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] ge_uint64 (v1 v2 : w64) :: go.IsGoOp GoGe go.uint64 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] ge_uint32 (v1 v2 : w32) :: go.IsGoOp GoGe go.uint32 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] ge_uint16 (v1 v2 : w16) :: go.IsGoOp GoGe go.uint16 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));
  #[global] ge_uint8 (v1 v2 : w8) :: go.IsGoOp GoGe go.uint8 (#v1, #v2) #(bool_decide (uint.Z v2 ≤ uint.Z v1));

  #[global] gt_int (v1 v2 : w64) :: go.IsGoOp GoGt go.int (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] gt_int64 (v1 v2 : w64) :: go.IsGoOp GoGt go.int64 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] gt_int32 (v1 v2 : w32) :: go.IsGoOp GoGt go.int32 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] gt_int16 (v1 v2 : w16) :: go.IsGoOp GoGt go.int16 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] gt_int8 (v1 v2 : w8) :: go.IsGoOp GoGt go.int8 (#v1, #v2) #(bool_decide (sint.Z v2 < sint.Z v1));
  #[global] gt_uint (v1 v2 : w64) :: go.IsGoOp GoGt go.uint (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] gt_uint64 (v1 v2 : w64) :: go.IsGoOp GoGt go.uint64 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] gt_uint32 (v1 v2 : w32) :: go.IsGoOp GoGt go.uint32 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] gt_uint16 (v1 v2 : w16) :: go.IsGoOp GoGt go.uint16 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));
  #[global] gt_uint8 (v1 v2 : w8) :: go.IsGoOp GoGt go.uint8 (#v1, #v2) #(bool_decide (uint.Z v2 < uint.Z v1));

  go_eq_string :: go.AlwaysSafelyComparable go.string go_string;
  index_string i (s : go_string) b (Hinrange : s !! (Z.to_nat i) = Some b) :
    index (go.string) i #s = #b
}.

End defs.
End go.
