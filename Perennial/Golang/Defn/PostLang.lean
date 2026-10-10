/-
The core of Goose's Go semantics, stated as typeclasses over an abstract
`GoSemanticsFunctions`.

## Conventions used in `Perennial/Golang/Defn` and `Perennial/TrustedCode`

* **Sealing.** A sealed definition is written
  ```
  def foo_def := ...
  @[irreducible] def foo := foo_def
  theorem foo_unseal : foo = foo_def := by with_unfolding_all rfl
  ```
  (`irreducible_def` is Mathlib-only). Opaque definitions get
  `attribute [irreducible] foo`.
* **Typeclasses.** A semantics class is a `class C : Prop` whose fields are
  either instances `[f : D]` (followed by `attribute [instance] C.f`) or
  properties `g : P`. Fields with an instance premise `A` take `A` as an
  instance-implicit binder. Output positions of a class are `outParam`s. The
  fields are re-`export`ed so that names such as `go.convert_underlying` and
  `go.alloc_struct` resolve.
* **Notation.** GooseLang code uses the notation of
  `Perennial/GooseLang/Notation.lean`; this file adds `⟦instr, args⟧ ⤳ e`,
  `⟦instr, args⟧ ⤳[tag] e` (whose `args` is in goose value mode and `e` in goose
  expression mode), `![t] e`, `e1 <-[t] e2`, `@! f`, `rcvr @!! t @!! m`,
  `s ≤u t`, `s <u t`, `t ↓u u` and `a =→ a'`.
* Decidable propositions are turned into booleans with `decide P`; machine-word
  operations are `BitVec` operations; list lookups are `l[i]?` and list updates
  are `l.set i v`.
-/
module

public import Perennial.GooseLang.Notation

@[expose] public section

namespace Perennial

/-- `EqualsUnfold a a'`, written `a =→ a'`: a sealed definition `a`
unfolds to `a'`. -/
class EqualsUnfold {A : Type} (a : A) (a' : outParam A) : Prop where
  equals_unfold : a = a'

export EqualsUnfold (equals_unfold)

scoped infix:50 " =→ " => EqualsUnfold

set_option checkBinderAnnotations false in
/-- Every element of the list satisfies the class `P` (found by typeclass search). -/
class inductive TCForall {A : Type} (P : A → Prop) : List A → Prop
  | nil : TCForall P []
  | cons {x : A} {xs : List A} [P x] [TCForall P xs] : TCForall P (x :: xs)

attribute [instance] TCForall.nil TCForall.cons

namespace map
abbrev _root_.Perennial.GoMap := Loc
def nil : GoMap := null
end map

class FloatOps where
  float64Neg : w64 → w64
  float64Add : w64 → w64 → w64
  float64Sub : w64 → w64 → w64
  float64Mul : w64 → w64 → w64
  float64Div : w64 → w64 → w64
  float64Leb : w64 → w64 → Bool

  float32Neg : w32 → w32
  float32Add : w32 → w32 → w32
  float32Sub : w32 → w32 → w32
  float32Mul : w32 → w32 → w32
  float32Div : w32 → w32 → w32
  float32Leb : w32 → w32 → Bool

  float64ToFloat32 : w64 → w32

export FloatOps (float64Neg float64Add float64Sub float64Mul float64Div float64Leb
  float32Neg float32Add float32Sub float32Mul float32Div float32Leb float64ToFloat32)

class GoSemanticsFunctions [FfiSyntax] where
  underlying : go.GoType → go.GoType
  globalAddr : GoString → Loc
  functions : GoString → List go.GoType → GoFunc
  methods : go.GoType → GoString → val → GoFunc

  methodSet : go.GoType → GMap GoString go.signature

  /-- This uses a Lean `Type` because there are multiple `go.GoType`s that have
  the same `Type` representation (e.g. uint64/int64, *X/*Y), but offsets are
  only supposed to depend on the Lean representation. Use it through the class
  `TypeRepr`. -/
  TypeRepr : go.GoType → (V : Type) → [ZeroVal V] → Prop
  structFieldRef : Type → GoString → Loc → Loc

  /-- The size in bytes (heap cells) of a value of Lean representation type `V` in memory:
  the stride of an array of them (`arrayIndexRef`). Like `structFieldRef`, indexed by the
  Lean representation, which determines it. -/
  typeSize : Type → Int

  mapEmpty : val → val
  mapLookup : val → val → Bool × val
  mapInsert : val → val → val → val
  mapDelete : val → val → val
  is_map_domain : val → List val → Prop

  is_map_pure (v : val) (m : val → Bool × val) : Prop
  mapDefault : val → val
  [float_ops : FloatOps]

attribute [instance] GoSemanticsFunctions.float_ops

export GoSemanticsFunctions (underlying globalAddr functions methods methodSet structFieldRef
  typeSize mapEmpty mapLookup mapInsert mapDelete is_map_domain is_map_pure mapDefault)

/-- The address of element `i` of an array of `V`s at `l`: `i` strides of `typeSize V`
bytes on, within `l`'s block. A location outside any block (`locCar = 0`, which no
allocation returns: `IsFresh`) has no elements, and stays where it is, so an index never
reaches `null` from a non-null array. -/
def arrayIndexRef [FfiSyntax] [GoSemanticsFunctions] (V : Type) (i : Int) (l : Loc) : Loc :=
  if l.locCar = 0 then l else l +ₗ i * typeSize V

theorem arrayIndexRef_of_car [FfiSyntax] [GoSemanticsFunctions] (V : Type) (i : Int) (l : Loc)
    (h : l.locCar ≠ 0) : arrayIndexRef V i l = l +ₗ i * typeSize V := by
  simp [arrayIndexRef, h]

@[simp] theorem arrayIndexRef_car [FfiSyntax] [GoSemanticsFunctions] (V : Type) (i : Int) (l : Loc) :
    (arrayIndexRef V i l).locCar = l.locCar := by
  unfold arrayIndexRef; split <;> rfl

/-- The class form of `GoSemanticsFunctions.TypeRepr` (`V` is an output). -/
class TypeRepr [FfiSyntax] [GoSemanticsFunctions] (t : go.GoType) (V : outParam Type) [ZeroVal V] :
    Prop where
  type_repr : GoSemanticsFunctions.TypeRepr t V

/-- `ptr .[ t , field ]`: the address of field `field` of the struct of type `t` at `ptr`. -/
scoped notation:max ptr ".[" t ", " field "]" => structFieldRef t field ptr

section unfolding_defs
variable [FfiSyntax] [GoSemanticsFunctions] [GoGlobalContext]

class FuncUnfold (f : GoString) (type_args : List go.GoType) (f_impl : outParam val) : Prop where
  func_unfold : #(functions f type_args) = f_impl

class MethodUnfold (t : go.GoType) (m : GoString) (m_impl : outParam val) : Prop where
  method_unfold : ∀ v, #(methods t m v) = (λ: "arg1", m_impl v "arg1" : val)

export FuncUnfold (func_unfold)
export MethodUnfold (method_unfold)
end unfolding_defs

inductive Tag where
  | under
  | underT (t : go.GoType)
  | internal
  | internalUnder

export Tag (under underT internal internalUnder)

namespace go
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

def GlobalAllocDef (v : GoString) (t : go.GoType) : val :=
  λ: <>,
    let: "l" := GoAlloc t (GoZeroVal t #()) in
    if: "l" =⟨go.PointerType t⟩ (GlobalVarAddr v #()) then
      #()
    else AngelicExit #()
@[irreducible] def GlobalAlloc (v : GoString) (t : go.GoType) : val := GlobalAllocDef v t
theorem GlobalAlloc_unseal : GlobalAlloc = GlobalAllocDef := by with_unfolding_all rfl

/-- This semantics considers several Go types to be `primitive` in the sense
that they are modeled as taking a single heap location. Predeclared types are
in their own file. A `class` so that the premise
`[IsPrimitive u]` of `alloc_primitive` etc. is found by typeclass search. -/
class inductive IsPrimitive : go.GoType → Prop
  | isPrimitive_pointer t : IsPrimitive (go.PointerType t)
  | isPrimitive_function sig : IsPrimitive (go.FunctionType sig)
  | isPrimitive_interface elems : IsPrimitive (go.InterfaceType elems)
  | isPrimitive_slice elem : IsPrimitive (go.SliceType elem)
  | isPrimitive_map kt vt : IsPrimitive (go.MapType kt vt)
  | isPrimitive_channel dir t : IsPrimitive (go.ChannelType dir t)

attribute [instance] IsPrimitive.isPrimitive_pointer IsPrimitive.isPrimitive_function
  IsPrimitive.isPrimitive_interface IsPrimitive.isPrimitive_slice IsPrimitive.isPrimitive_map
  IsPrimitive.isPrimitive_channel
export IsPrimitive (isPrimitive_pointer isPrimitive_function isPrimitive_interface
  isPrimitive_slice isPrimitive_map isPrimitive_channel)

inductive IsPrimitiveZeroVal : go.GoType → val → Prop
  | isPrimitiveZeroVal_pointer t : IsPrimitiveZeroVal (go.PointerType t) #null
  | isPrimitiveZeroVal_function t : IsPrimitiveZeroVal (go.FunctionType t) #func.nil
  | isPrimitive_zero_valinterface elems :
      IsPrimitiveZeroVal (go.InterfaceType elems) #interface.nil
  | isPrimitiveZeroVal_slice elem : IsPrimitiveZeroVal (go.SliceType elem) #slice.nil
  | isPrimitiveZeroVal_map kt vt : IsPrimitiveZeroVal (go.MapType kt vt) #null
  | isPrimitiveZeroVal_channel dir t : IsPrimitiveZeroVal (go.ChannelType dir t) #null

export IsPrimitiveZeroVal (isPrimitiveZeroVal_pointer isPrimitiveZeroVal_function
  isPrimitive_zero_valinterface isPrimitiveZeroVal_slice isPrimitiveZeroVal_map
  isPrimitiveZeroVal_channel)

-- `GoInterfaceOk`, `GoInterface` and `GoFunc` contain GooseLang syntax, whose
-- equality is decided classically (see `Lang.lean`).
noncomputable instance interface_ok_eq_dec : DecidableEq GoInterfaceOk :=
  fun a b => Classical.propDecidable (a = b)

noncomputable instance interface_eq_dec : DecidableEq GoInterface :=
  fun a b => Classical.propDecidable (a = b)

instance array_eq_dec (V : Type) (n : Int) [DecidableEq V] : DecidableEq (GoArray V n) :=
  fun a b =>
    if h : a.arr = b.arr then isTrue (by cases a; cases b; cases h; rfl)
    else isFalse (by intro e; cases e; exact h rfl)

noncomputable instance func_eq_dec : DecidableEq GoFunc :=
  fun a b => Classical.propDecidable (a = b)

/-
Here's an example exhibiting struct comparison subtleties:

```
package main

type comparableButNotSuperComparable struct {
	x int
	a any
}

func main() {
	a := comparableButNotSuperComparable{x: 37, a: make([]int, 0)}
	b := comparableButNotSuperComparable{x: 38, a: make([]int, 0)}
	var aa any = a
	var ba any = b
	if aa == ba {
	}
}
```
If the 38 is changed to 37, then the comparison `aa == ba` does not short
circuit, and it tries to check if the `any` fields are equal, at which point it
panics because the type is not comparable.
-/

/-- `⟦instr, args⟧ ⤳ e`: the Go instruction `instr` applied to `args` takes a
deterministic pure step to `e`. -/
class IsGoStepPureDet (instr : GoInstruction) (args : val) (e : outParam Expr) : Prop where
  isGoStep_det : ∀ s s' e',
    IsGoStep instr args e' s s' ↔ is_go_step_pure instr args e' ∧ s = s'
  isGoStep_pure_det : is_go_step_pure instr args = Eq e

export IsGoStepPureDet (isGoStep_det isGoStep_pure_det)

class IsGoStepPureDetTagged (t : Tag) (instr : GoInstruction) (args : val) (e : outParam Expr) :
    Prop where
  isGoStep_det_internal : IsGoStepPureDet instr args e

export IsGoStepPureDetTagged (isGoStep_det_internal)

end defs
end go

/-- `⟦instr, args⟧ ⤳ e` is `go.IsGoStepPureDet instr args e` (`args` in goose
value mode, `e` in goose expression mode). -/
scoped syntax:50 "⟦" term ", " term "⟧" " ⤳ " term:51 : term
/-- `⟦instr, args⟧ ⤳[tag] e` is `go.IsGoStepPureDetTagged tag instr args e`. -/
scoped syntax:50 "⟦" term ", " term "⟧" " ⤳[" term "] " term:51 : term

macro_rules
  | `(⟦$i, $a⟧ ⤳ $e) => `(go.IsGoStepPureDet $i glv($a) gl($e))
  | `(⟦$i, $a⟧ ⤳[$t] $e) => `(go.IsGoStepPureDetTagged $t $i glv($a) gl($e))

namespace go
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

theorem tagged_steps (t : Tag) :
    ∀ instr args e, ⟦instr, args⟧ ⤳[t] e → ⟦instr, args⟧ ⤳ e := by
  intro _ _ _ h; exact h.isGoStep_det_internal

class UnderlyingEq [GoSemanticsFunctions] (s : go.GoType) (t : outParam go.GoType) : Prop where
  underlying_eq : underlying s = underlying t

/-- This has a transitive instance, so only declare instances in a way that `t'`
is strictly "more underlying" than `t`. An instance with `t = t'` will cause an
infinite loop in typeclass search because of transitivity. -/
class UnderlyingDirectedEq [GoSemanticsFunctions] (t : go.GoType) (t' : outParam go.GoType) :
    Prop where
  underlying_unfold : underlying t = underlying t'

class NotNamed (t : go.GoType) : Prop where
  not_named : match t with | go.Named _ _ => False | _ => True

class NotInterface (t : go.GoType) : Prop where
  not_interface : match t with | go.InterfaceType _ => False | _ => True

class IsUnderlying [GoSemanticsFunctions] (t : go.GoType) (tunder : outParam go.GoType) : Prop where
  is_underlying : underlying t = tunder

export UnderlyingEq (underlying_eq)
export UnderlyingDirectedEq (underlying_unfold)
export NotNamed (not_named)
export NotInterface (not_interface)
export IsUnderlying (is_underlying)

end defs
end go

scoped infix:50 " ≤u " => go.UnderlyingEq
scoped infix:50 " <u " => go.UnderlyingDirectedEq
scoped infix:50 " ↓u " => go.IsUnderlying

namespace go
section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

class TypeReprUnderlying [GoSemanticsFunctions] (u : go.GoType) (V : outParam Type) [ZeroVal V] :
    Prop where
  type_repr_underlying_def : ∀ {t : go.GoType} [t ↓u u], TypeRepr t V

export TypeReprUnderlying (type_repr_underlying_def)

instance type_repr_underlying [GoSemanticsFunctions] {t u : go.GoType} {V : Type} [ZeroVal V]
    [t ↓u u] [TypeReprUnderlying u V] : TypeRepr t V :=
  TypeReprUnderlying.type_repr_underlying_def (u := u)

/-- Helper definition to cover types for which `a == b` always executes safely. -/
class IsStrictlyComparable [GoSemanticsFunctions] (t : go.GoType) (V : Type) [DecidableEq V] :
    Prop where
  is_strictly_comparable :
    ∀ (v1 v2 : V), ⟦GoOp GoEquals t, (#v1, #v2)⟧ ⤳[under] #(decide (v1 = v2))

attribute [instance] IsStrictlyComparable.is_strictly_comparable
export IsStrictlyComparable (is_strictly_comparable)

class CoreComparisonSemantics [GoSemanticsFunctions] : Prop where
  /-- special case equality for functions -/
  go_op_go_equals_func_nil_l (sig : go.signature) (f : GoFunc) :
    ⟦GoOp GoEquals (go.FunctionType sig), (#f, #func.nil)⟧ ⤳[under] #(decide (f = func.nil))
  go_op_go_equals_func_nil_r (sig : go.signature) (f : GoFunc) :
    ⟦GoOp GoEquals (go.FunctionType sig), (#func.nil, #f)⟧ ⤳[under] #(decide (f = func.nil))

  check_comparable_pointer (t : go.GoType) :
    ⟦CheckComparable (go.PointerType t), #()⟧ ⤳[under] #()
  go_eq_pointer (t : go.GoType) : IsStrictlyComparable (go.PointerType t) Loc

  check_comparable_channel (dir : go.ChanDir) (t : go.GoType) :
    ⟦CheckComparable (go.ChannelType dir t), #()⟧ ⤳[under] #()
  go_eq_channel (t : go.ChanDir) (dir : go.GoType) :
    IsStrictlyComparable (go.ChannelType t dir) Loc

  struct_is_comparable (fds : List go.field_decl)
    [TCForall (fun fd => ⟦CheckComparable (match fd with
      | go.FieldDecl _ t | go.EmbeddedField _ t => t), #()⟧ ⤳[under] #()) fds] :
    ⟦CheckComparable (go.StructType fds), #()⟧ ⤳[under] #()
  go_eq_struct {fds fds_unsealed : List go.field_decl} [fds =→ fds_unsealed] (v1 v2 : val) :
    ⟦GoOp GoEquals (go.StructType fds), (v1, v2)⟧ ⤳[under]
    (List.foldl (fun cmp_so_far fd =>
             let (field_name, field_type) :=
               match fd with
               | go.FieldDecl n t => (n, t)
               | go.EmbeddedField n t => (n, t)
             gl(if: cmp_so_far then
                (StructFieldGet (go.StructType fds) field_name v1) =⟨field_type⟩
                (StructFieldGet (go.StructType fds) field_name v2)
              else #false)
      ) (#true : Expr) fds_unsealed)

attribute [instance] CoreComparisonSemantics.go_op_go_equals_func_nil_l
  CoreComparisonSemantics.go_op_go_equals_func_nil_r CoreComparisonSemantics.check_comparable_pointer
  CoreComparisonSemantics.go_eq_pointer CoreComparisonSemantics.check_comparable_channel
  CoreComparisonSemantics.go_eq_channel CoreComparisonSemantics.struct_is_comparable
  CoreComparisonSemantics.go_eq_struct
export CoreComparisonSemantics (go_op_go_equals_func_nil_l go_op_go_equals_func_nil_r
  check_comparable_pointer go_eq_pointer check_comparable_channel go_eq_channel
  struct_is_comparable go_eq_struct)

def structFieldType (f : GoString) : List go.field_decl → go.GoType
  | [] => go.Named go!"field not found" []
  | go.FieldDecl f' t :: fds
  | go.EmbeddedField f' t :: fds =>
      if f = f' then t
      else structFieldType f fds

class IntoValUnfold (V : Type) (f : outParam (V → val)) : Prop where
  intoVal_unfold : @intoVal _ _ V = f

/-- Unfold `intoVal` at type `V` (explicit). -/
theorem intoVal_unfold (V : Type) {f : V → val} [IntoValUnfold V f] : @intoVal _ _ V = f :=
  IntoValUnfold.intoVal_unfold

class IntoValInj (V : Type) : Prop where
  intoVal_inj : Function.Injective (intoVal (V := V))

export IntoValInj (intoVal_inj)

class BasicIntoValInj : Prop where
  [intoVal_inj_loc : IntoValInj Loc]
  [intoVal_inj_slice : IntoValInj GoSlice]
  [intoVal_inj_w64 : IntoValInj w64]
  [intoVal_inj_w32 : IntoValInj w32]
  [intoVal_inj_w16 : IntoValInj w16]
  [intoVal_inj_w8 : IntoValInj w8]
  [intoVal_inj_bool : IntoValInj Bool]
  [intoVal_inj_string : IntoValInj GoString]
  [intoVal_inj_interface : IntoValInj GoInterface]
  [intoVal_inj_proph_id : IntoValInj proph_id]

attribute [instance] BasicIntoValInj.intoVal_inj_loc BasicIntoValInj.intoVal_inj_slice
  BasicIntoValInj.intoVal_inj_w64 BasicIntoValInj.intoVal_inj_w32
  BasicIntoValInj.intoVal_inj_w16 BasicIntoValInj.intoVal_inj_w8
  BasicIntoValInj.intoVal_inj_bool BasicIntoValInj.intoVal_inj_string
  BasicIntoValInj.intoVal_inj_interface BasicIntoValInj.intoVal_inj_proph_id

/-- `go.CoreSemantics` defines the basics of when a GoContext is valid,
excluding predeclared types (including primitives), arrays, slice, map, and
channels, each of which is in their own file. -/
class CoreSemantics [GoSemanticsFunctions] : Prop where
  [basic_into_val_inj : BasicIntoValInj]

  underlying_not_named {t : go.GoType} [NotNamed t] : t ↓u t

  -- Underlying-respecting instructions
  convert_underlying {from_ from_under to to_under : go.GoType} [from_ ↓u from_under]
    [to ↓u to_under] (v : val) (e : Expr) [⟦Convert from_under to_under, v⟧ ⤳[under] e] :
    ⟦Convert from_ to, v⟧ ⤳ e
  go_un_op_underlying (o : GoUnaryOperator) {t t_under : go.GoType} [t ↓u t_under] (v : val)
    (e : Expr) [⟦GoUnOp o t_under, v⟧ ⤳[under] e] : ⟦GoUnOp o t, v⟧ ⤳ e
  go_op_underlying (o : GoOperator) {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦GoOp o t_under, v⟧ ⤳[under] e] : ⟦GoOp o t, v⟧ ⤳ e
  composite_literal_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦CompositeLiteral t_under, v⟧ ⤳[under] e] : ⟦CompositeLiteral t, v⟧ ⤳ e
  slice_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦Slice t_under, v⟧ ⤳[under] e] : ⟦Slice t, v⟧ ⤳ e
  fullSlice_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦FullSlice t_under, v⟧ ⤳[under] e] : ⟦FullSlice t, v⟧ ⤳ e
  index_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦Index t_under, v⟧ ⤳[under] e] : ⟦Index t, v⟧ ⤳ e
  index_ref_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦IndexRef t_under, v⟧ ⤳[under] e] : ⟦IndexRef t, v⟧ ⤳ e
  check_comparable_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦CheckComparable t_under, v⟧ ⤳[under] e] : ⟦CheckComparable t, v⟧ ⤳ e
  struct_field_get_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    (f : GoString) [⟦StructFieldGet t_under f, v⟧ ⤳[under] e] : ⟦StructFieldGet t f, v⟧ ⤳ e
  struct_field_set_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    (f : GoString) [⟦StructFieldSet t_under f, v⟧ ⤳[under] e] : ⟦StructFieldSet t f, v⟧ ⤳ e
  structFieldRef_step_underlying {t t_under : go.GoType} [t ↓u t_under] (f : GoString)
    (v : val) (e : Expr) [⟦StructFieldRef t_under f, v⟧ ⤳[under] e] : ⟦StructFieldRef t f, v⟧ ⤳ e
  go_zero_val_step_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦GoZeroVal t_under, v⟧ ⤳[under] e] : ⟦GoZeroVal t, v⟧ ⤳ e

  go_func_resolve_step (n : GoString) (ts : List go.GoType) :
    ⟦FuncResolve n ts, #()⟧ ⤳ #(functions n ts)
  go_method_resolve_step (m : GoString) (t : go.GoType) (rcvr : val) {tunder : go.GoType}
    [t ↓u tunder] [NotInterface tunder] :
    ⟦MethodResolve t m, rcvr⟧ ⤳ #(methods t m rcvr)
  go_global_var_addr_step (v : GoString) : ⟦GlobalVarAddr v, #()⟧ ⤳ #(globalAddr v)

  /-- FIXME: unsound semantics: simply computing the struct field address will
  panic if the base address is nil. This is a bit of a headache because every
  program step executing `StructFieldRef` will need to have a precondition that
  `l ≠ null`. -/
  structFieldRef_step (t : go.GoType) (f : GoString) (l : Loc) {V : Type} [ZeroVal V]
    [TypeRepr t V] : ⟦StructFieldRef t f, #l⟧ ⤳[under] #(structFieldRef V f l)

  /-- The language spec doesn't say anything about the addresses of zero-sized
  allocation. But, in the runtime, these addresses are non-nil, so the
  semantics assumes it here.
  https://cs.opensource.google/go/go/+/refs/tags/go1.25.5:src/runtime/malloc.go;l=927
  https://cs.opensource.google/go/go/+/refs/tags/go1.25.5:src/runtime/malloc.go;l=1023 -/
  go_prealloc_step : is_go_step_pure GoPrealloc #() = (fun (e : Expr) => ∃ (l : Loc), l ≠ null ∧ e = #l)
  angelic_exit_step : is_go_step_pure AngelicExit #() = (fun (e : Expr) => e = AngelicExit #())

  intoVal_unfold_func : IntoValUnfold GoFunc (fun f => RecV f.f f.x f.e)
  intoVal_unfold_bool : IntoValUnfold Bool (fun x => LitV (LitBool x))

  -- Eventually want to get rid of these.
  intoVal_unfold_w64 : IntoValUnfold w64 (fun x => LitV (LitInt x))
  intoVal_unfold_w32 : IntoValUnfold w32 (fun x => LitV (LitInt32 x))
  intoVal_unfold_w16 : IntoValUnfold w16 (fun x => LitV (LitInt16 x))
  intoVal_unfold_w8 : IntoValUnfold w8 (fun x => LitV (LitByte x))
  intoVal_unfold_string : IntoValUnfold GoString (fun x => LitV (LitString x))
  intoVal_unfold_loc : IntoValUnfold Loc (fun x => LitV (LitLoc x))
  intoVal_unfold_unit : IntoValUnfold Unit (fun _ => LitV LitUnit)

  go_zero_val_step {V : Type} [ZeroVal V] {t : go.GoType} [TypeRepr t V] :
    ⟦GoZeroVal t, #()⟧ ⤳ #(zero_val V)

  go_zero_val_pointer (t : go.GoType) : TypeReprUnderlying (go.PointerType t) Loc
  go_zero_val_function (sig : go.signature) : TypeReprUnderlying (go.FunctionType sig) GoFunc
  go_zero_val_slice (elem_type : go.GoType) : TypeReprUnderlying (go.SliceType elem_type) GoSlice
  go_zero_val_interface (elems : List go.InterfaceElem) :
    TypeReprUnderlying (go.InterfaceType elems) GoInterface
  go_zero_val_channel (dir : go.ChanDir) (elem_type : go.GoType) :
    TypeReprUnderlying (go.ChannelType dir elem_type) GoChan
  go_zero_val_map (key_type elem_type : go.GoType) :
    TypeReprUnderlying (go.MapType key_type elem_type) GoMap

  [core_comparison_sem : CoreComparisonSemantics]

  composite_literal_pointer (elem_type : go.GoType) (l : val) :
    ⟦CompositeLiteral (go.PointerType elem_type), l⟧ ⤳[under]
    GoAlloc elem_type (CompositeLiteral elem_type l)

  composite_literal_struct (l : List keyed_element) {fds fds_unsealed : List go.field_decl}
    [fds =→ fds_unsealed] :
    ⟦CompositeLiteral (go.StructType fds), (LiteralValueV l)⟧ ⤳[under]
    (match l with
          | [] => GoZeroVal (go.StructType fds) #()
          | KeyedElement none _ :: _ =>
              -- unkeyed struct literal
              List.foldl (fun v (fd, ke) =>
                       let (field_name, field_type) :=
                         match fd with
                         | go.FieldDecl n t | go.EmbeddedField n t => (n, t)
                       match ke with
                       | KeyedElement none (ElementExpression from_ e) =>
                           gl(StructFieldSet (go.StructType fds) field_name
                             (v, Convert from_ field_type e))
                       | _ => Panic "invalid Go code"
                ) (GoZeroVal (go.StructType fds) #()) (fds_unsealed.zip l)
          | KeyedElement (some _) _ :: _ =>
              -- keyed struct literal
              List.foldl (fun v ke =>
                       match ke with
                       | KeyedElement (some (KeyField field_name)) (ElementExpression from_ e) =>
                           gl(StructFieldSet (go.StructType fds) field_name
                             (v, Convert from_ (structFieldType field_name fds_unsealed) e))
                       | _ => Panic "invalid Go code"
                ) (GoZeroVal (go.StructType fds) #()) l)

  alloc_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦GoAlloc t_under, v⟧ ⤳[internalUnder] e] : ⟦GoAlloc t, v⟧ ⤳[internal] e
  load_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦GoLoad t_under, v⟧ ⤳[internalUnder] e] : ⟦GoLoad t, v⟧ ⤳[internal] e
  store_underlying {t t_under : go.GoType} [t ↓u t_under] (v : val) (e : Expr)
    [⟦GoStore t_under, v⟧ ⤳[internalUnder] e] : ⟦GoStore t, v⟧ ⤳[internal] e

  alloc_primitive (v : val) (u : go.GoType) [H : IsPrimitive u] :
    ⟦GoAlloc u, v⟧ ⤳[internalUnder] Alloc v
  alloc_struct (v : val) {fds fds_unsealed : List go.field_decl} [fds =→ fds_unsealed] :
    ⟦GoAlloc (go.StructType fds), v⟧ ⤳[internalUnder]
      (let: "l" := GoPrealloc #() in
       List.foldr (fun fd alloc_rest =>
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => (n, t)
                                                | go.EmbeddedField n t => (n, t)
                let field_addr := gl(StructFieldRef (go.StructType fds) field_name "l")
                gl(let: "l_field" :=
                    GoAlloc field_type (StructFieldGet (go.StructType fds) field_name v) in
                  (if: ("l_field" =⟨go.PointerType field_type⟩ field_addr) then #()
                   else AngelicExit #()) ;;
                  alloc_rest)
         ) (#() : Expr) fds_unsealed ;;
       "l")

  load_primitive (u : go.GoType) [H : IsPrimitive u] (l : val) :
    ⟦GoLoad u, l⟧ ⤳[internalUnder] Read l

  load_struct (fds : List go.field_decl) (l : val) {fds_unsealed : List go.field_decl}
    [fds =→ fds_unsealed] :
    ⟦GoLoad (go.StructType fds), l⟧ ⤳[internalUnder]
      (List.foldl (fun struct_so_far fd =>
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => (n, t)
                                                | go.EmbeddedField n t => (n, t)
                let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                let field_val := gl(GoLoad field_type field_addr)
                gl(StructFieldSet (go.StructType fds) field_name (struct_so_far, field_val))
         ) (GoZeroVal (go.StructType fds) #()) fds_unsealed)

  store_primitive (u : go.GoType) [H : IsPrimitive u] (l v : val) :
    ⟦GoStore u, (l, v)⟧ ⤳[internalUnder] Store l v
  store_struct {fds fds_unsealed : List go.field_decl} [fds =→ fds_unsealed] (l v : val) :
    ⟦GoStore (go.StructType fds), (l, v)⟧ ⤳[internalUnder]
      (List.foldl (fun store_so_far fd =>
                gl(store_so_far ;;
                  (let (field_name, field_type) := match fd with
                                                  | go.FieldDecl n t => (n, t)
                                                  | go.EmbeddedField n t => (n, t)
                   let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                   let field_val := gl(StructFieldGet (go.StructType fds) field_name v)
                   gl(GoStore field_type (field_addr, field_val))))
         ) (#() : Expr) fds_unsealed)

  is_convert_underlying_same (t : go.GoType) (v : val) : ⟦Convert t t, v⟧ ⤳[under] v
  convert_same (t : go.GoType) (v : val) : ⟦Convert t t, v⟧ ⤳ v
  /-- A conversion between (unnamed) pointer types whose base types have the same
  underlying type keeps the pointer (the Go spec's conversion rule "x's type and T are
  pointer types that are not named types, and their pointer base types are not type
  parameters but have identical underlying types"), e.g. `(*BTreeG[Item])(t)` for
  `t : *BTree` with `type BTree BTreeG[Item]`. -/
  convert_pointer_same_underlying {t1 t2 u : go.GoType} [t1 ↓u u] [t2 ↓u u] (l : Loc) :
    ⟦Convert (go.PointerType t1) (go.PointerType t2), #l⟧ ⤳[under] #l

attribute [instance] CoreSemantics.basic_into_val_inj CoreSemantics.underlying_not_named
  CoreSemantics.convert_underlying CoreSemantics.go_un_op_underlying
  CoreSemantics.go_op_underlying CoreSemantics.composite_literal_underlying
  CoreSemantics.slice_underlying CoreSemantics.fullSlice_underlying
  CoreSemantics.index_underlying CoreSemantics.index_ref_underlying
  CoreSemantics.check_comparable_underlying CoreSemantics.struct_field_get_underlying
  CoreSemantics.struct_field_set_underlying CoreSemantics.structFieldRef_step_underlying
  CoreSemantics.go_zero_val_step_underlying CoreSemantics.go_func_resolve_step
  CoreSemantics.go_method_resolve_step CoreSemantics.go_global_var_addr_step
  CoreSemantics.structFieldRef_step CoreSemantics.intoVal_unfold_func
  CoreSemantics.intoVal_unfold_bool CoreSemantics.intoVal_unfold_w64
  CoreSemantics.intoVal_unfold_w32 CoreSemantics.intoVal_unfold_w16
  CoreSemantics.intoVal_unfold_w8 CoreSemantics.intoVal_unfold_string
  CoreSemantics.intoVal_unfold_loc CoreSemantics.intoVal_unfold_unit
  CoreSemantics.go_zero_val_step CoreSemantics.go_zero_val_pointer
  CoreSemantics.go_zero_val_function CoreSemantics.go_zero_val_slice
  CoreSemantics.go_zero_val_interface CoreSemantics.go_zero_val_channel
  CoreSemantics.go_zero_val_map CoreSemantics.core_comparison_sem
  CoreSemantics.composite_literal_pointer CoreSemantics.composite_literal_struct
  CoreSemantics.alloc_underlying CoreSemantics.load_underlying CoreSemantics.store_underlying
  CoreSemantics.alloc_primitive CoreSemantics.alloc_struct CoreSemantics.load_primitive
  CoreSemantics.load_struct CoreSemantics.store_primitive CoreSemantics.store_struct
  CoreSemantics.is_convert_underlying_same CoreSemantics.convert_same
  CoreSemantics.convert_pointer_same_underlying

export CoreSemantics (basic_into_val_inj underlying_not_named convert_underlying
  go_un_op_underlying go_op_underlying composite_literal_underlying slice_underlying
  fullSlice_underlying index_underlying index_ref_underlying check_comparable_underlying
  struct_field_get_underlying struct_field_set_underlying structFieldRef_step_underlying
  go_zero_val_step_underlying go_func_resolve_step go_method_resolve_step go_global_var_addr_step
  structFieldRef_step go_prealloc_step angelic_exit_step intoVal_unfold_func
  intoVal_unfold_bool intoVal_unfold_w64 intoVal_unfold_w32 intoVal_unfold_w16
  intoVal_unfold_w8 intoVal_unfold_string intoVal_unfold_loc intoVal_unfold_unit
  go_zero_val_step go_zero_val_pointer go_zero_val_function go_zero_val_slice
  go_zero_val_interface go_zero_val_channel go_zero_val_map core_comparison_sem
  composite_literal_pointer composite_literal_struct alloc_underlying load_underlying
  store_underlying alloc_primitive alloc_struct load_primitive load_struct store_primitive
  store_struct is_convert_underlying_same convert_same convert_pointer_same_underlying)

end defs
end go

/-- `@! func`: `#(functions func [])`. -/
scoped syntax:max "@! " term:max : term
/-- `rcvr @!! type @!! method`: `#(methods type method #rcvr)`. The operator is
`@!!` rather than `@!`, since `rcvr @! ...` parses as an application
of `rcvr` to `@! ...`. -/
scoped syntax:80 term:81 " @!! " term:81 " @!! " term:81 : term
/-- `![t] e`: typed load. -/
scoped syntax:max "![" term "] " term:max : term
/-- `e1 <-[t] e2`: typed store. -/
scoped syntax:40 term:41 " <-[" term "] " term:40 : term

macro_rules
  | `(@! $f) => `(intoVal (functions $f []))
  | `($r @!! $t @!! $m) => `(intoVal (methods $t $m (intoVal $r)))
  | `(![$t] $e) => `(App (Val (GoInstruction (GoLoad $t))) gl($e))
  | `($e1 <-[$t] $e2) => `(App (Val (GoInstruction (GoStore $t))) (Pair gl($e1) gl($e2)))

end Perennial
