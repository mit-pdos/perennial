From New.golang.defn Require Export postlang.

Section helpers.
Context {ext : ffi_syntax}.
(* Implementations for max and min for integer types. *)
Definition minⁱᵐᵖˡ t (n : nat) : val :=
  match n with
  | 2%nat => (λ: "x" "y", if: "x" <[t] "y" then "x" else "y")%V
  | _ => LitV $ LitPoison
  end.

Definition maxⁱᵐᵖˡ t (n : nat) : val :=
  match n with
  | 2%nat => (λ: "x" "y", if: "x" >[t] "y" then "x" else "y")%V
  | _ => LitV $ LitPoison
  end.

Axiom recover : val.

Definition float_placeholder : val := #().

(* Definition make_nondet (t : go.type) : val :=
  λ: <>,
     if decide (t = go.uint64) then
       ArbitraryInt
     else
       Panic "unsupported nondet". *)
(*
     match t with
     | go.uint64 => ArbitraryInt
     | uint32T => u_to_w32 ArbitraryInt
     | uint16T => u_to_w16 ArbitraryInt
     | _
     end. *)
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
Context `{ffi_syntax}.

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

Inductive is_predeclared_zero_val : go.type → ∀ {V} `{!IntoVal V}, V → Prop :=
| is_predeclared_zero_val_uint : is_predeclared_zero_val go.uint (W64 0)
| is_predeclared_zero_val_uint8 : is_predeclared_zero_val go.uint8 (W8 0)
| is_predeclared_zero_val_uint16 : is_predeclared_zero_val go.uint16 (W16 0)
| is_predeclared_zero_val_uint32 : is_predeclared_zero_val go.uint32 (W32 0)
| is_predeclared_zero_val_uint64 : is_predeclared_zero_val go.uint64 (W64 0)
| is_predeclared_zero_val_int : is_predeclared_zero_val go.int (W64 0)
| is_predeclared_zero_val_int8 : is_predeclared_zero_val go.int8 (W8 0)
| is_predeclared_zero_val_int16 : is_predeclared_zero_val go.int16 (W16 0)
| is_predeclared_zero_val_int32 : is_predeclared_zero_val go.int32 (W32 0)
| is_predeclared_zero_val_int64 : is_predeclared_zero_val go.int64 (W64 0)
| is_predeclared_zero_val_string : is_predeclared_zero_val go.string ""%go
| is_predeclared_zero_val_bool : is_predeclared_zero_val go.bool false.

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

Inductive is_ordered_type : go.type → Prop :=
| is_ordered_type_numeric t (H : is_integer_type t) : _ t
| is_ordered_type_string : _ go.string
.

Class PredeclaredSemantics {go_ctx : GoContext} :=
{
  alloc_predeclared t {V} (v : V) `{!IntoVal V} (H : is_predeclared_zero_val t v) :
    alloc t = (λ: <>, ref #v)%V;
  load_predeclared t (H : is_predeclared t) : load t = (λ: "l", ! "l")%V;
  store_predeclared t (H : is_predeclared t) : store t = (λ: "l" "v", "l" <- "v")%V;

  predeclared_underlying t (H : is_predeclared t) : to_underlying t = t;

  len_underlying t : functions len [t] = functions len [to_underlying t];

  cap_underlying t : functions cap [t] = functions cap [to_underlying t];

  make3_underlying t : functions make3 [t] = functions make3 [to_underlying t];
  make2_underlying t : functions make2 [t] = functions make2 [to_underlying t];
  make1_underlying t : functions make1 [t] = functions make1 [to_underlying t];

  min_ordered n t (H : is_ordered_type t) : #(functions min (replicate n t)) = minⁱᵐᵖˡ t n;
  max_ordered n t (H : is_ordered_type t) : #(functions min (replicate n t)) = maxⁱᵐᵖˡ t n;
}.

End defs.
End go.
