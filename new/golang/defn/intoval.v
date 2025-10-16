From New.golang.defn Require Export notation.
From Perennial Require Import base.

Class IntoVal `{ffi_syntax} (V : Type) :=
  {
    to_val_def : V → val;
    zero_val : V;
  }.

Program Definition to_val := sealed @to_val_def.
Definition to_val_unseal : to_val = _ := seal_eq _.
Arguments to_val {_ _ _} v.
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

Section primitive_instances.
Context `{ffi_syntax}.

Global Instance into_val_loc : IntoVal loc :=
  {| to_val_def := λ v, (LitV $ LitLoc v); zero_val := null |}.

Global Instance into_val_w64 : IntoVal w64 :=
  {| to_val_def := λ v, (LitV $ LitInt v); zero_val := W64 0 |}.

Global Instance into_val_w32 : IntoVal w32 :=
  {| to_val_def := λ v, (LitV $ LitInt32 v); zero_val := W32 0 |}.

Global Instance into_val_w16 : IntoVal w16 :=
  {| to_val_def := λ v, (LitV $ LitInt16 v); zero_val := W16 0 |}.

Global Instance into_val_w8 : IntoVal w8 :=
  {| to_val_def := λ v, (LitV $ LitByte v); zero_val := W8 0 |}.

Global Instance into_val_unit : IntoVal () :=
  {| to_val_def := λ _, (LitV $ LitUnit); zero_val := () |}.

Global Instance into_val_bool : IntoVal bool :=
  {| to_val_def := λ b, (LitV $ LitBool b); zero_val := false |}.

Global Instance into_val_go_string : IntoVal go_string :=
  {| to_val_def := λ s, (LitV $ LitString s); zero_val := ""%go |}.

Global Instance into_val_func : IntoVal func.t :=
  {| to_val_def := λ (f : func.t), RecV f.(func.f) f.(func.x) f.(func.e); zero_val := func.nil |}.
End primitive_instances.

Module slice.
Record t := mk { ptr_f: loc; len_f: u64; cap_f: u64; }.
Definition nil : slice.t := mk null 0 0.
End slice.

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

Section instances.
Context `{ffi_syntax}.
Global Instance into_val_array `{!IntoVal V} n : IntoVal (vec V n) :=
  {|
    to_val_def := λ v, (Vector.fold_right PairV (vmap to_val v) #());
    zero_val := vreplicate n (zero_val V);
  |}.

Global Instance into_val_slice : IntoVal slice.t :=
  {|
    to_val_def (s: slice.t) := InjLV (#s.(slice.ptr_f), #s.(slice.len_f), #s.(slice.cap_f));
    zero_val := slice.nil;
  |}.

Global Instance slice_eq_dec : EqDecision slice.t.
Proof. solve_decision. Qed.

Global Instance into_val_interface `{ffi_syntax} : IntoVal interface.t :=
  {|
    to_val_def (i: interface.t) :=
      match i with
      | interface.nil => NONEV
      | interface.mk type_id v => SOMEV (#type_id, v)%V
      end;
    zero_val := interface.nil;
  |}.

End instances.
Global Notation "()" := tt : val_scope.

Global Opaque to_val.
