(* Trusted stuff that's conceptually part of the GooseLang semantics. E.g.
   assumptions about valid GoContext and definition of zero values via
   IntoVal. *)

From Perennial.goose_lang Require Export lang notation.
From Perennial Require Export base.

Class IntoVal {ext : ffi_syntax} (V : Type) :=
  {
    to_val_def : V → val;
    zero_val : V;
  }.

Program Definition to_val := sealed @to_val_def.
Definition to_val_unseal : to_val = _ := seal_eq _.
Arguments to_val {_ _ _} v%go.
Arguments zero_val {_} (V) {_}.
(* Disable Notation "# l". *)
Global Notation "# x" := (to_val x%go).
Global Notation "#" := to_val (at level 0).

(* One of [V] or [ty] should not be an evar before doing typeclass search *)
Global Hint Mode IntoVal - ! : typeclass_instances.

Module func.
Section defn.
Context `{ffi_syntax}.
Record t := mk {
      f : binder;
      x : binder;
      e : expr;
    }.
Definition nil := mk <> <> (LitV LitPoison).
End defn.
End func.

Module chan.
  Definition t := loc.
  Definition nil : chan.t := null.
End chan.

Module interface.
Section goose_lang.
  Context `{ffi_syntax}.

  Inductive t :=
  | mk (type_id : go_string) (v : val) : t
  | nil : t.

End goose_lang.
End interface.

Section into_val_instances.
Context `{ffi_syntax}.

Global Instance into_val_loc : IntoVal loc :=
  {| to_val_def v := (LitV $ LitLoc v); zero_val := null |}.

Global Instance into_val_w64 : IntoVal w64 :=
  {| to_val_def v := (LitV $ LitInt v); zero_val := W64 0 |}.

Global Instance into_val_w32 : IntoVal w32 :=
  {| to_val_def v := (LitV $ LitInt32 v); zero_val := W32 0 |}.

Global Instance into_val_w16 : IntoVal w16 :=
  {| to_val_def v := (LitV $ LitInt16 v); zero_val := W16 0 |}.

Global Instance into_val_w8 : IntoVal w8 :=
  {| to_val_def v := (LitV $ LitByte v); zero_val := W8 0 |}.

Global Instance into_val_unit : IntoVal () :=
  {| to_val_def _ := (LitV $ LitUnit); zero_val := () |}.

Global Instance into_val_bool : IntoVal bool :=
  {| to_val_def b := (LitV $ LitBool b); zero_val := false |}.

Global Instance into_val_go_string : IntoVal go_string :=
  {| to_val_def s := (LitV $ LitString s); zero_val := ""%go |}.

Global Instance into_val_func : IntoVal func.t :=
  {| to_val_def f := RecV f.(func.f) f.(func.x) f.(func.e); zero_val := func.nil |}.

Global Instance into_val_array `{!IntoVal V} n : IntoVal (vec V n) :=
  {|
    to_val_def v := ArrayV (to_val <$> (vec_to_list v));
    zero_val := vreplicate n (zero_val V);
  |}.

Global Instance into_val_slice : IntoVal slice.t :=
  {|
    to_val_def (s: slice.t) := LitV (LitSlice s);
    zero_val := slice.nil;
  |}.

Global Instance into_val_interface : IntoVal interface.t :=
  {|
    to_val_def (i: interface.t) :=
      match i with
      | interface.nil => NONEV
      | interface.mk type_id v => SOMEV (#type_id, v)%V
      end;
    zero_val := interface.nil;
  |}.

End into_val_instances.
Global Notation "()" := tt : val_scope.
Global Opaque to_val.

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E #false) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E #true e2%E) (only parsing) : expr_scope.

Module go.

(* built-in types *)
Definition uint64 : go.type := go.Named "uint64"%go [].
Definition uint32 : go.type := go.Named "uint32"%go [].
Definition uint16 : go.type := go.Named "uint16"%go [].
Definition uint8 : go.type := go.Named "uint8"%go [].
Definition int64 : go.type := go.Named "int64"%go [].
Definition int32 : go.type := go.Named "int32"%go [].
Definition int16 : go.type := go.Named "int16"%go [].
Definition int8 : go.type := go.Named "int8"%go [].
Definition string : go.type := go.Named "string"%go [].
Definition bool : go.type := go.Named "bool"%go [].
Definition byte : go.type := uint8.
Definition rune : go.type := uint32.

Section defs.
Context `{ffi_syntax}.

Inductive is_primitive : go.type → Prop :=
| is_primitive_uint64 : is_primitive uint64
| is_primitive_uint32 : is_primitive uint32
| is_primitive_uint16 : is_primitive uint16
| is_primitive_uint8 : is_primitive uint8
| is_primitive_int64 : is_primitive int64
| is_primitive_int32 : is_primitive int32
| is_primitive_int16 : is_primitive int16
| is_primitive_int8 : is_primitive int8
| is_primitive_string : is_primitive string
| is_primitive_bool : is_primitive bool

| is_primitive_pointer t : is_primitive (go.PointerType t)
| is_primitive_function sig : is_primitive (go.FunctionType sig)
| is_primitive_interface elems : is_primitive (go.InterfaceType elems)
| is_primitive_slice elem : is_primitive (go.SliceType elem)
| is_primitive_map kt vt : is_primitive (go.MapType kt vt)
| is_primitive_channel dir t : is_primitive (go.ChannelType dir t).

Inductive is_primitive_zero_val : go.type → ∀ {V} `{!IntoVal V}, V → Prop :=
| is_primitive_zero_val_uint64 : is_primitive_zero_val uint64 (W64 0)
| is_primitive_zero_val_uint32 : is_primitive_zero_val uint32 (W32 0)
| is_primitive_zero_val_uint16 : is_primitive_zero_val uint16 (W16 0)
| is_primitive_zero_val_uint8 : is_primitive_zero_val uint8 (W8 0)
| is_primitive_zero_val_int64 : is_primitive_zero_val int64 (W64 0)
| is_primitive_zero_val_int32 : is_primitive_zero_val int32 (W32 0)
| is_primitive_zero_val_int16 : is_primitive_zero_val int16 (W16 0)
| is_primitive_zero_val_int8 : is_primitive_zero_val int8 (W8 0).

(** [go.ContextValid] defines when a GoContext is valid. *)
Class ContextValid `{!GoContext} :=
{
  alloc_underlying t : alloc t = alloc (to_underlying t);
  alloc_primitive t `{!IntoVal V} (v : V) (H : is_primitive_zero_val t v) :
    alloc t = (λ: <>, ref #v)%V;
  alloc_struct fds : alloc (go.StructType fds) = alloc (go.StructType fds); (* TODO *)
  alloc_array n elem : alloc (go.ArrayType n elem) = alloc (go.ArrayType n elem); (* TODO *)

  load_underlying t : load t = load (to_underlying t);
  load_primitive t (H : is_primitive t) : load t = (λ: "l", ! "l")%V;
  load_struct fds : load (go.StructType fds) = (λ: "l", Panic "impl")%V; (* TODO *)
  load_array n elem : load (go.ArrayType n elem) = load (go.ArrayType n elem); (* TODO *)

  store_underlying t : store t = store (to_underlying t);
  store_primitive t (H : is_primitive t) : store t = (λ: "l" "v", "l" <- "v")%V;
  store_struct fds : store (go.StructType fds) = (λ: "l", Panic "impl")%V; (* TODO *)
  store_array n elem : store (go.ArrayType n elem) = store (go.ArrayType n elem); (* TODO *)

  struct_field_ref_underlying t : struct_field_ref t = struct_field_ref (to_underlying t);
}.

End defs.
End go.
