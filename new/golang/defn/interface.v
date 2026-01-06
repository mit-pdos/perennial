From New.golang.defn Require Export postlang.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext} `{!GoSemanticsFunctions}.

Definition is_interface_type (t : go.type) : bool :=
  match (to_underlying t) with
  | go.InterfaceType _ => true
  | _ => false
  end.

(* Based on: https://go.dev/ref/spec#General_interfaces *)
Definition type_set_term_contains {go_ctx : GoLocalContext} t (e : go.type_term) : bool :=
  match e with
  | go.TypeTerm t' => bool_decide (t = t')
  | go.TypeTermUnderlying t' => bool_decide (to_underlying t = t')
  end.

Definition type_set_elem_contains {go_ctx : GoLocalContext} t (e : go.interface_elem) : bool :=
  match e with
  | go.MethodElem m signature => bool_decide (method_set t !! m = Some signature)
  | go.TypeElem terms => existsb (type_set_term_contains t) terms
  end.

Definition type_set_elems_contains {go_ctx : GoLocalContext} t (elems : list go.interface_elem) : bool :=
  forallb (type_set_elem_contains t) elems.

(** Equals [true] iff t is in the type set of t'. *)
Definition type_set_contains {go_ctx : GoLocalContext} t t' : bool :=
  match (to_underlying t') with
  | go.InterfaceType elems => type_set_elems_contains t elems
  | _ => bool_decide (t = t')
  end.

Class InterfaceSemantics :=
{
  #[global] interface_make_step dt v ::
    go.IsGoStepPureDet (InterfaceMake dt) v #(interface.mk dt v);
  #[global] interface_get_step m i ::
    go.IsGoStepPureDet (InterfaceGet m) #i
    (match i with
     | interface.nil => Panic "nil dereference in interface call"
     | interface.mk t v => (λ: "arg1", #(methods t m) v "arg1")%E
     end);
  #[global] type_assert_step t i ::
    go.IsGoStepPureDet (TypeAssert t) #i
    (match i with
     | interface.nil => Panic "type assert failed"
     | interface.mk dt v =>
         if is_interface_type t then
           (if (type_set_contains dt t) then #i else Panic "type assert failed")
         else
           (if decide (t = dt) then v else Panic "type assert failed")
     end);
  #[global] type_assert2_step t i ::
    go.IsGoStepPureDet (TypeAssert2 t) #i
    (match i with
     | interface.nil => (#interface.nil, #false)%V
     | interface.mk dt v =>
         if is_interface_type t then
           (if (type_set_contains dt t) then (#i, #true)%V else (#interface.nil, #false)%V)
         else
           (if decide (t = dt) then (v, #true)%V else (GoZeroVal t #(), #false)%E)
     end);

  method_interface t m (H : is_interface_type t = true) :
    #(methods t m) = (InterfaceGet m);
}.
End defs.
End go.
