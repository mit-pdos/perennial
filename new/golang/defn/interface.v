From New.golang.defn Require Export postlang.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext} `{!GoSemanticsFunctions}.

Definition is_interface_type (t : go.type) : bool :=
  match t with go.InterfaceType _ => true | _ => false end.

(* Based on: https://go.dev/ref/spec#General_interfaces *)
Definition type_set_term_contains {go_ctx : GoLocalContext} t (e : go.type_term) : bool :=
  match e with
  | go.TypeTerm t' => bool_decide (t = t')
  | go.TypeTermUnderlying t' => bool_decide (underlying t = t')
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
  match (underlying t') with
  | go.InterfaceType elems => type_set_elems_contains t elems
  | _ => bool_decide (t = t')
  end.

Class InterfaceSemantics :=
{
  #[global] is_comparable_interface elems :: go.IsComparable (go.InterfaceType elems);
  #[global] go_eq_interface elems i1 i2 ::
    go.GoExprEq (go_eq (go.InterfaceType elems) #i1 #i2)
      (match i1, i2 with
       | interface.nil, interface.nil => #true
       | (interface.ok i1), (interface.ok i2) =>
           if decide (i1.(interface.ty) = i2.(interface.ty)) then
             go_eq i1.(interface.ty) i1.(interface.v) i2.(interface.v)
           else #false
       | _, _ => #false
       end);
  #[global] convert_to_interface (v : val)
    `{!from ↓u funder} `{!to ≤u go.InterfaceType elems} ::
    go.GoExprEq (Convert from to v)
      (Val (if is_interface_type funder then v else #(interface.mk_ok from v)));

  #[global] interface_get_step_nil m i ::
    go.IsGoStepPureDet (InterfaceGet m) #i
    (match i with
     | interface.nil => (Panic "nil dereference in interface call")
     | interface.ok i => (λ: "arg1", #(methods i.(interface.ty) m) i.(interface.v) "arg1")%E
     end);

  #[global] type_assert_step `{!t ↓u tunder} i ::
    go.IsGoStepPureDet (TypeAssert t) #i
    (match i with
     | interface.nil => Panic "type assert failed"
     | interface.ok i =>
         if is_interface_type tunder then
           if (type_set_contains i.(interface.ty) t) then #i else Panic "type assert failed"
         else
           if decide (t = i.(interface.ty)) then i.(interface.v) else Panic "type assert failed"
     end);

  #[global] type_assert2_interface_step `{!t ↓u tunder} i ::
    go.IsGoStepPureDet (TypeAssert2 t) #i
    (match i with
     | interface.nil => (#interface.nil, #false)%V
     | interface.ok i =>
         if is_interface_type tunder then
           if (type_set_contains i.(interface.ty) t) then (#i, #true)%V else (#interface.nil, #false)%V
         else
           if decide (t = i.(interface.ty)) then (i.(interface.v), #true)%V else (GoZeroVal t #(), #false)%E
     end);

  method_interface m `{!t ≤u go.InterfaceType elems} :
    #(methods t m) = (λ: "v", InterfaceGet m "v")%V;
}.
End defs.
End go.
