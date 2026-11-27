/-
Interface semantics: type sets, comparison, conversion, type assertions and
method calls on interface values.
-/
module

public import Perennial.Golang.Defn.PostLang
public import Perennial.Golang.Defn.MethodSet

@[expose] public section

namespace Perennial

namespace go
section defs
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

def isInterfaceType (t : go.GoType) : Bool :=
  match t with | go.InterfaceType _ => true | _ => false

/-- A defined type without type arguments, or a pointer to one: a type whose identity in Go is its
(package-qualified) name, so that the equality of its translation is Go's type identity. (Not so for
a type literal: Lean's struct field names are unqualified where Go's unexported ones are not, so
two struct types of different packages can be equal here and different in Go.) -/
def identByName (t : go.GoType) : Bool :=
  match t with
  | go.Named _ [] => true
  | go.PointerType (go.Named _ []) => true
  | _ => false

def isUntypedNil (t : go.GoType) : Bool :=
  match t with | go.Named n [] => decide (n = go!"untyped nil") | _ => false

omit [GoSemanticsFunctions] in
/-- Based on: https://go.dev/ref/spec#General_interfaces -/
noncomputable def typeSetTermContains (t : go.GoType) (e : go.type_term) : Bool :=
  match e with
  | go.TypeTerm t' => decide (t = t')
  | go.TypeTermUnderlying t' => decide (underlying t = t')

omit [GoSemanticsFunctions] in
noncomputable def typeSetElemContains (t : go.GoType) (e : go.InterfaceElem) : Bool :=
  match e with
  | go.MethodElem m signature => decide (methodSet t !! m = some signature)
  | go.TypeElem terms => terms.any (typeSetTermContains t)

omit [GoSemanticsFunctions] in
noncomputable def typeSetElemsContains (t : go.GoType) (elems : List go.InterfaceElem) : Bool :=
  elems.all (typeSetElemContains t)

omit [GoSemanticsFunctions] in
/-- Equals `true` iff t is in the type set of t'. goose writes an interface type as the list of
all its methods (`go.MethodElem`, named by their ids, those of embedded interfaces included),
followed by its other embedded elements (unions, constraints such as `comparable`), which only
occur in type constraints; a method element is decided by `methodSet` (`MethodSet.lean`). -/
noncomputable def typeSetContains (t t' : go.GoType) : Bool :=
  match (underlying t') with
  | go.InterfaceType elems => typeSetElemsContains t elems
  | _ => decide (t = t')

/-- The underlying types at which `TypeAssertUnderlying2` reads a value (`reflect.Value`'s
`Int`/`Uint` for an integer kind, `String` for kind `String`): the integer types and `string`. -/
class inductive IsIntegerOrString : go.GoType → Prop
  | integer (t : go.GoType) [IsInteger t] : IsIntegerOrString t
  | string : IsIntegerOrString go.string

attribute [instance] IsIntegerOrString.integer IsIntegerOrString.string

class InterfaceSemantics : Prop where
  is_comparable_interface (elems : List go.InterfaceElem) :
    ⟦CheckComparable (go.InterfaceType elems), #()⟧ ⤳[under] #()
  go_eq_interface (elems : List go.InterfaceElem) (i1 i2 : GoInterface) :
    ⟦GoOp GoEquals (go.InterfaceType elems), (#i1, #i2)⟧ ⤳[under]
      (match i1, i2 with
       | interface.nil, interface.nil => #true
       | (interface.ok i1), (interface.ok i2) =>
           if i1.ty = i2.ty then
             gl(CheckComparable i1.ty ;;
              GoOp GoEquals i1.ty glv((i1.v, i2.v)))
           else #false
       | _, _ => #false)

  /-- `T(x)` for an interface type `T`. The rule does not check that `x`'s type implements
  `T`: it relies on goose emitting only conversions that type-check. A trusted primitive that
  constructs a conversion at run time must check it itself (`ConvertAt`'s premise `hi`,
  `Reflect.lean`). -/
  convert_to_interface (v : val) {from_ funder to : go.GoType} {elems : List go.InterfaceElem}
    [from_ ↓u funder] [to ≤u go.InterfaceType elems] :
    ⟦Convert from_ to, v⟧ ⤳
    (Val (if isInterfaceType funder then v else
            if isUntypedNil funder then #interface.nil
            else #(interface.mkOk from_ v)))

  type_assert_step {t t_under : go.GoType} [t ↓u t_under] (i : GoInterface) :
    ⟦TypeAssert t, #i⟧ ⤳
    (match i with
     | interface.nil => Panic "type assert failed"
     | interface.ok ii =>
         if isInterfaceType t_under then
           if (typeSetContains ii.ty t) then #i else Panic "type assert failed"
         else
           if ii.ty = t then ii.v else Panic "type assert failed")

  type_assert2_interface_step {t t_under : go.GoType} [t ↓u t_under] (i : GoInterface) {v : val}
    [⟦GoZeroVal t, #()⟧ ⤳ Val v] :
    ⟦TypeAssert2 t, #i⟧ ⤳
    glv(((match i with
      | interface.nil => v
      | interface.ok ii =>
          (if isInterfaceType t_under then
             if (typeSetContains ii.ty t) then #i else v
           else
             if ii.ty = t then ii.v else v)),
       #(match i with
         | interface.nil => false
         | interface.ok ii =>
             if isInterfaceType t_under then typeSetContains ii.ty t
             else decide (ii.ty = t))
     ))

  /-- `reflect.ValueOf(i)` read at the kind of `t`, for a `t` whose underlying type is an integer
  type (`v.Int()`, `v.Uint()`) or `string` (`v.String()`): an interface whose dynamic type has
  `t`'s underlying type gives its value, any other interface (`nil` included) `t`'s zero value,
  with whether it did. Go values of types with the same underlying type have the same
  representation (`CoreSemantics.convert_underlying`). Restricted to integer types and `string`
  (`IsIntegerOrString`): for a struct type, Lean's field names are unqualified where Go's
  unexported ones are not, so equal underlying types here need not be equal in Go. -/
  type_assert_underlying2_step {t t_under : go.GoType} [t ↓u t_under] [IsIntegerOrString t_under]
    (i : GoInterface) {v : val}
    [⟦GoZeroVal t, #()⟧ ⤳ Val v] :
    ⟦TypeAssertUnderlying2 t, #i⟧ ⤳
    glv(((match i with
      | interface.nil => v
      | interface.ok ii => if underlying ii.ty = t_under then ii.v else v),
       #(match i with
         | interface.nil => false
         | interface.ok ii => decide (underlying ii.ty = t_under))))

  type_of_eq_step (i1 i2 : GoInterface) :
    ⟦TypeOfEq, (#i1, #i2)⟧ ⤳
    #(match i1, i2 with
      | interface.nil, interface.nil => true
      | interface.ok ii1, interface.ok ii2 => decide (ii1.ty = ii2.ty)
      | _, _ => false)

  method_interface_ok (m : GoString) {t : go.GoType} {elems : List go.InterfaceElem}
    [t ≤u go.InterfaceType elems] (i : GoInterface) :
    ⟦MethodResolve t m, #i⟧ ⤳
    (match i with
     | interface.nil => Panic "nil interface"
     | interface.ok i => #(methods i.ty m i.v))

  /-- The types with no methods (`go.NoMethods`) have an empty method set. The method sets
  of the named types of a package are facts of the package's `Assumptions`
  (`MethodSet.lean`). -/
  method_set_no_methods (t : go.GoType) [NoMethods t] : MethodSetIs t []

attribute [instance] InterfaceSemantics.is_comparable_interface InterfaceSemantics.go_eq_interface
  InterfaceSemantics.convert_to_interface InterfaceSemantics.type_assert_step
  InterfaceSemantics.type_assert2_interface_step InterfaceSemantics.type_assert_underlying2_step
  InterfaceSemantics.type_of_eq_step InterfaceSemantics.method_interface_ok
  InterfaceSemantics.method_set_no_methods
export InterfaceSemantics (is_comparable_interface go_eq_interface convert_to_interface
  type_assert_step type_assert2_interface_step type_assert_underlying2_step type_of_eq_step
  method_interface_ok
  method_set_no_methods)

end defs
end go

end Perennial
