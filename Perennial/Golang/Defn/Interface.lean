/-
Port of `new/golang/defn/interface.v`.
-/
import Perennial.Golang.Defn.PostLang

namespace Perennial

namespace go
section defs
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

def is_interface_type (t : go.type) : Bool :=
  match t with | go.InterfaceType _ => true | _ => false

def is_untyped_nil (t : go.type) : Bool :=
  match t with | go.Named n [] => decide (n = go!"untyped nil") | _ => false

/-- Based on: https://go.dev/ref/spec#General_interfaces -/
noncomputable def type_set_term_contains (t : go.type) (e : go.type_term) : Bool :=
  match e with
  | go.TypeTerm t' => decide (t = t')
  | go.TypeTermUnderlying t' => decide (underlying t = t')

noncomputable def type_set_elem_contains (t : go.type) (e : go.interface_elem) : Bool :=
  match e with
  | go.MethodElem m signature => decide (method_set t !! m = some signature)
  | go.TypeElem terms => terms.any (type_set_term_contains t)

noncomputable def type_set_elems_contains (t : go.type) (elems : List go.interface_elem) : Bool :=
  elems.all (type_set_elem_contains t)

/-- Equals `true` iff t is in the type set of t'. -/
noncomputable def type_set_contains (t t' : go.type) : Bool :=
  match (underlying t') with
  | go.InterfaceType elems => type_set_elems_contains t elems
  | _ => decide (t = t')

class InterfaceSemantics : Prop where
  is_comparable_interface (elems : List go.interface_elem) :
    ⟦CheckComparable (go.InterfaceType elems), #()⟧ ⤳[under] #()
  go_eq_interface (elems : List go.interface_elem) (i1 i2 : interface.t) :
    ⟦GoOp GoEquals (go.InterfaceType elems), (#i1, #i2)⟧ ⤳[under]
      (match i1, i2 with
       | interface.nil, interface.nil => #true
       | (interface.ok i1), (interface.ok i2) =>
           if i1.ty = i2.ty then
             gl(CheckComparable i1.ty ;;
              GoOp GoEquals i1.ty glv((i1.v, i2.v)))
           else #false
       | _, _ => #false)

  convert_to_interface (v : val) {from_ funder to : go.type} {elems : List go.interface_elem}
    [from_ ↓u funder] [to ≤u go.InterfaceType elems] :
    ⟦Convert from_ to, v⟧ ⤳
    (Val (if is_interface_type funder then v else
            if is_untyped_nil funder then #interface.nil
            else #(interface.mk_ok from_ v)))

  type_assert_step {t t_under : go.type} [t ↓u t_under] (i : interface.t) :
    ⟦TypeAssert t, #i⟧ ⤳
    (match i with
     | interface.nil => Panic "type assert failed"
     | interface.ok ii =>
         if is_interface_type t_under then
           if (type_set_contains ii.ty t) then #i else Panic "type assert failed"
         else
           if ii.ty = t then ii.v else Panic "type assert failed")

  type_assert2_interface_step {t t_under : go.type} [t ↓u t_under] (i : interface.t) {v : val}
    [⟦GoZeroVal t, #()⟧ ⤳ Val v] :
    ⟦TypeAssert2 t, #i⟧ ⤳
    glv(((match i with
      | interface.nil => v
      | interface.ok ii =>
          (if is_interface_type t_under then
             if (type_set_contains ii.ty t) then #i else v
           else
             if ii.ty = t then ii.v else v)),
       #(match i with
         | interface.nil => false
         | interface.ok ii =>
             if is_interface_type t_under then type_set_contains ii.ty t
             else decide (ii.ty = t))
     ))

  method_interface_ok (m : go_string) {t : go.type} {elems : List go.interface_elem}
    [t ≤u go.InterfaceType elems] (i : interface.t) :
    ⟦MethodResolve t m, #i⟧ ⤳
    (match i with
     | interface.nil => Panic "nil interface"
     | interface.ok i => #(methods i.ty m i.v))

attribute [instance] InterfaceSemantics.is_comparable_interface InterfaceSemantics.go_eq_interface
  InterfaceSemantics.convert_to_interface InterfaceSemantics.type_assert_step
  InterfaceSemantics.type_assert2_interface_step InterfaceSemantics.method_interface_ok
export InterfaceSemantics (is_comparable_interface go_eq_interface convert_to_interface
  type_assert_step type_assert2_interface_step method_interface_ok)

end defs
end go

end Perennial
