From New.golang.defn Require Export postlang.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext} `{!GoSemanticsFunctions}.

Definition is_interface_type (t : go.type) : bool :=
  match t with go.InterfaceType _ => true | _ => false end.

Definition is_untyped_nil (t : go.type) : bool :=
  match t with go.Named n [] => ByteString.eqb n "untyped nil" | _ => false end.

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
  #[global] is_comparable_interface elems ::
    ⟦CheckComparable (go.InterfaceType elems), #()⟧ ⤳[under] #();
  #[global] go_eq_interface elems i1 i2 ::
    ⟦GoOp GoEquals (go.InterfaceType elems), (#i1, #i2)⟧ ⤳[under]
      (match i1, i2 with
       | interface.nil, interface.nil => #true
       | (interface.ok i1), (interface.ok i2) =>
           if decide (i1.(interface.ty) = i2.(interface.ty)) then
             (CheckComparable i1.(interface.ty);;
              GoOp GoEquals i1.(interface.ty) (i1.(interface.v), i2.(interface.v))%V)%E
           else #false
       | _, _ => #false
       end);

  #[global] convert_to_interface (v : val)
    `{!from ↓u funder} `{!to ≤u go.InterfaceType elems} ::
    ⟦Convert from to, v⟧ ⤳
    (Val (if is_interface_type funder then v else
            if is_untyped_nil funder then #interface.nil
            else #(interface.mk_ok from v)));

  #[global] type_assert_step `{!t ↓u t_under} i ::
    ⟦TypeAssert t, #i⟧ ⤳
    (match i with
     | interface.nil => Panic "type assert failed"
     | interface.ok ii =>
         if is_interface_type t_under then
           if (type_set_contains ii.(interface.ty) t) then #i else Panic "type assert failed"
         else
           if decide (ii.(interface.ty) = t) then ii.(interface.v) else Panic "type assert failed"
     end);

  #[global] type_assert2_interface_step `{!t ↓u t_under} i `{!⟦GoZeroVal t, #()⟧ ⤳ Val v} ::
    ⟦TypeAssert2 t, #i⟧ ⤳
    ((match i with
      | interface.nil => v
      | interface.ok ii =>
          (if is_interface_type t_under then
             if (type_set_contains ii.(interface.ty) t) then #i else v
           else
             if decide (ii.(interface.ty) = t) then ii.(interface.v) else v)
      end),
       #(match i with
         | interface.nil => false
         | interface.ok ii =>
             if is_interface_type t_under then type_set_contains ii.(interface.ty) t
             else bool_decide (ii.(interface.ty) = t)
         end)
     )%V;

  #[global] method_interface_ok m `{!t ≤u go.InterfaceType elems} (i : interface.t) ::
    ⟦MethodResolve t m, #i⟧ ⤳
    (match i with
     | interface.nil => (Panic "nil interface")%E
     | interface.ok i => #(methods i.(interface.ty) m i.(interface.v))
     end);
}.
End defs.
End go.
