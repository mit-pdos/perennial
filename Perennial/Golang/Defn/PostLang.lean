/-
Port of `new/golang/defn/postlang.v`: the core of Goose's Go semantics, stated
as typeclasses over an abstract `GoSemanticsFunctions`.

## Conventions used in `Perennial/Golang/Defn` and `Perennial/TrustedCode`

* **Sealing.** Rocq's
  ```
  Definition foo_def := ... .
  Program Definition foo := sealed @foo_def.
  Definition foo_unseal : foo = _ := seal_eq _.
  ```
  becomes
  ```
  def foo_def := ...
  @[irreducible] def foo := foo_def
  theorem foo_unseal : foo = foo_def := by with_unfolding_all rfl
  ```
  (`irreducible_def` is Mathlib-only). Rocq `Global Opaque foo` becomes
  `attribute [irreducible] foo`.
* **Typeclasses.** A Rocq `Class C : Prop := { #[global] f :: D; g : P }`
  becomes a Lean `class C : Prop` with fields `[f : D]` and `g : P`, followed by
  `attribute [instance] C.f`. Fields whose Rocq type is `A → B` with `A` a class
  (instance premise) take `A` as an instance-implicit binder. `Hint Mode`
  output positions become `outParam`s. The fields are re-`export`ed so that the
  Rocq names (`go.convert_underlying`, `go.alloc_struct`, ...) resolve.
* **Notation.** GooseLang code uses the notation of
  `Perennial/GooseLang/Notation.lean`; this file adds `⟦instr, args⟧ ⤳ e`,
  `⟦instr, args⟧ ⤳[tag] e` (whose `args` is in goose value mode and `e` in goose
  expression mode), `![t] e`, `e1 <-[t] e2`, `@! f`, `rcvr @!! t @!! m` (Rocq
  `rcvr @! t @! m`),
  `s ≤u t`, `s <u t`, `t ↓u u` and `a =→ a'`.
* `bool_decide P` is `decide P`; coqutil `word.*` operations are the
  corresponding `BitVec` operations; stdpp list lookups `l !! i` are `l[i]?`
  and list updates `<[i:=v]> l` are `l.set i v`.
-/
import Perennial.GooseLang.Notation

namespace Perennial

/-- Rocq `EqualsUnfold a a'`, written `a =→ a'`: a sealed definition `a`
unfolds to `a'`. -/
class EqualsUnfold {A : Type} (a : A) (a' : outParam A) : Prop where
  equals_unfold : a = a'

export EqualsUnfold (equals_unfold)

scoped infix:50 " =→ " => EqualsUnfold

set_option checkBinderAnnotations false in
/-- stdpp `TCForall`. -/
class inductive TCForall {A : Type} (P : A → Prop) : List A → Prop
  | nil : TCForall P []
  | cons {x : A} {xs : List A} [P x] [TCForall P xs] : TCForall P (x :: xs)

attribute [instance] TCForall.nil TCForall.cons

namespace map
abbrev t := loc
def nil : t := null
end map

class FloatOps where
  float64_neg : w64 → w64
  float64_add : w64 → w64 → w64
  float64_sub : w64 → w64 → w64
  float64_mul : w64 → w64 → w64
  float64_div : w64 → w64 → w64
  float64_leb : w64 → w64 → Bool

  float32_neg : w32 → w32
  float32_add : w32 → w32 → w32
  float32_sub : w32 → w32 → w32
  float32_mul : w32 → w32 → w32
  float32_div : w32 → w32 → w32
  float32_leb : w32 → w32 → Bool

  float64_to_float32 : w64 → w32

export FloatOps (float64_neg float64_add float64_sub float64_mul float64_div float64_leb
  float32_neg float32_add float32_sub float32_mul float32_div float32_leb float64_to_float32)

class GoSemanticsFunctions [ffi_syntax] where
  underlying : go.type → go.type
  global_addr : go_string → loc
  functions : go_string → List go.type → func.t
  methods : go.type → go_string → val → func.t

  method_set : go.type → gmap go_string go.signature

  /-- This uses a Lean `Type` because there are multiple `go.type`s that have
  the same `Type` representation (e.g. uint64/int64, *X/*Y), but offsets are
  only supposed to depend on the Lean representation. Use it through the class
  `TypeRepr`. -/
  TypeRepr : go.type → (V : Type) → [ZeroVal V] → Prop
  struct_field_ref : Type → go_string → loc → loc

  array_index_ref (elem_type : Type) (i : Int) (l : loc) : loc

  map_empty : val → val
  map_lookup : val → val → Bool × val
  map_insert : val → val → val → val
  map_delete : val → val → val
  is_map_domain : val → List val → Prop

  is_map_pure (v : val) (m : val → Bool × val) : Prop
  map_default : val → val
  [float_ops : FloatOps]

attribute [instance] GoSemanticsFunctions.float_ops

export GoSemanticsFunctions (underlying global_addr functions methods method_set struct_field_ref
  array_index_ref map_empty map_lookup map_insert map_delete is_map_domain is_map_pure map_default)

/-- Rocq `Existing Class TypeRepr` (with `Hint Mode TypeRepr - - + - -`): the
class form of `GoSemanticsFunctions.TypeRepr`. -/
class TypeRepr [ffi_syntax] [GoSemanticsFunctions] (t : go.type) (V : outParam Type) [ZeroVal V] :
    Prop where
  type_repr : GoSemanticsFunctions.TypeRepr t V

/-- Rocq `ptr .[ t , field ]`. -/
scoped notation:max ptr ".[" t ", " field "]" => struct_field_ref t field ptr

section unfolding_defs
variable [ffi_syntax] [GoSemanticsFunctions] [GoGlobalContext]

class FuncUnfold (f : go_string) (type_args : List go.type) (f_impl : outParam val) : Prop where
  func_unfold : #(functions f type_args) = f_impl

class MethodUnfold (t : go.type) (m : go_string) (m_impl : outParam val) : Prop where
  method_unfold : ∀ v, #(methods t m v) = (λ: "arg1", m_impl v "arg1" : val)

export FuncUnfold (func_unfold)
export MethodUnfold (method_unfold)
end unfolding_defs

inductive tag where
  | under
  | under_t (t : go.type)
  | internal
  | internal_under

export tag (under under_t internal internal_under)

namespace go
section defs
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext]

def GlobalAlloc_def (v : go_string) (t : go.type) : val :=
  λ: <>,
    let: "l" := GoAlloc t (GoZeroVal t #()) in
    if: "l" =⟨go.PointerType t⟩ (GlobalVarAddr v #()) then
      #()
    else AngelicExit #()
@[irreducible] def GlobalAlloc (v : go_string) (t : go.type) : val := GlobalAlloc_def v t
theorem GlobalAlloc_unseal : GlobalAlloc = GlobalAlloc_def := by with_unfolding_all rfl

/-- This semantics considers several Go types to be `primitive` in the sense
that they are modeled as taking a single heap location. Predeclared types are
in their own file. A `class` (Rocq: plain inductive) so that the premise
`[is_primitive u]` of `alloc_primitive` etc. is found by typeclass search. -/
class inductive is_primitive : go.type → Prop
  | is_primitive_pointer t : is_primitive (go.PointerType t)
  | is_primitive_function sig : is_primitive (go.FunctionType sig)
  | is_primitive_interface elems : is_primitive (go.InterfaceType elems)
  | is_primitive_slice elem : is_primitive (go.SliceType elem)
  | is_primitive_map kt vt : is_primitive (go.MapType kt vt)
  | is_primitive_channel dir t : is_primitive (go.ChannelType dir t)

attribute [instance] is_primitive.is_primitive_pointer is_primitive.is_primitive_function
  is_primitive.is_primitive_interface is_primitive.is_primitive_slice is_primitive.is_primitive_map
  is_primitive.is_primitive_channel
export is_primitive (is_primitive_pointer is_primitive_function is_primitive_interface
  is_primitive_slice is_primitive_map is_primitive_channel)

inductive is_primitive_zero_val : go.type → val → Prop
  | is_primitive_zero_val_pointer t : is_primitive_zero_val (go.PointerType t) #null
  | is_primitive_zero_val_function t : is_primitive_zero_val (go.FunctionType t) #func.nil
  | is_primitive_zero_valinterface elems :
      is_primitive_zero_val (go.InterfaceType elems) #interface.nil
  | is_primitive_zero_val_slice elem : is_primitive_zero_val (go.SliceType elem) #slice.nil
  | is_primitive_zero_val_map kt vt : is_primitive_zero_val (go.MapType kt vt) #null
  | is_primitive_zero_val_channel dir t : is_primitive_zero_val (go.ChannelType dir t) #null

export is_primitive_zero_val (is_primitive_zero_val_pointer is_primitive_zero_val_function
  is_primitive_zero_valinterface is_primitive_zero_val_slice is_primitive_zero_val_map
  is_primitive_zero_val_channel)

-- `interface.t_ok`, `interface.t` and `func.t` contain GooseLang syntax, whose
-- equality is decided classically (see `Lang.lean`).
noncomputable instance interface_ok_eq_dec : DecidableEq interface.t_ok :=
  fun a b => Classical.propDecidable (a = b)

noncomputable instance interface_eq_dec : DecidableEq interface.t :=
  fun a b => Classical.propDecidable (a = b)

instance array_eq_dec (V : Type) (n : Int) [DecidableEq V] : DecidableEq (array.t V n) :=
  fun a b =>
    if h : a.arr = b.arr then isTrue (by cases a; cases b; cases h; rfl)
    else isFalse (by intro e; cases e; exact h rfl)

noncomputable instance func_eq_dec : DecidableEq func.t :=
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
class IsGoStepPureDet (instr : go_instruction) (args : val) (e : outParam expr) : Prop where
  is_go_step_det : ∀ s s' e',
    is_go_step instr args e' s s' ↔ is_go_step_pure instr args e' ∧ s = s'
  is_go_step_pure_det : is_go_step_pure instr args = Eq e

export IsGoStepPureDet (is_go_step_det is_go_step_pure_det)

class IsGoStepPureDetTagged (t : tag) (instr : go_instruction) (args : val) (e : outParam expr) :
    Prop where
  is_go_step_det_internal : IsGoStepPureDet instr args e

export IsGoStepPureDetTagged (is_go_step_det_internal)

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
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext]

theorem tagged_steps (t : tag) :
    ∀ instr args e, ⟦instr, args⟧ ⤳[t] e → ⟦instr, args⟧ ⤳ e := by
  intro _ _ _ h; exact h.is_go_step_det_internal

class UnderlyingEq [GoSemanticsFunctions] (s : go.type) (t : outParam go.type) : Prop where
  underlying_eq : underlying s = underlying t

/-- This has a transitive instance, so only declare instances in a way that `t'`
is strictly "more underlying" than `t`. An instance with `t = t'` will cause an
infinite loop in typeclass search because of transitivity. -/
class UnderlyingDirectedEq [GoSemanticsFunctions] (t : go.type) (t' : outParam go.type) :
    Prop where
  underlying_unfold : underlying t = underlying t'

class NotNamed (t : go.type) : Prop where
  not_named : match t with | go.Named _ _ => False | _ => True

class NotInterface (t : go.type) : Prop where
  not_interface : match t with | go.InterfaceType _ => False | _ => True

class IsUnderlying [GoSemanticsFunctions] (t : go.type) (tunder : outParam go.type) : Prop where
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
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext]

class TypeReprUnderlying [GoSemanticsFunctions] (u : go.type) (V : outParam Type) [ZeroVal V] :
    Prop where
  type_repr_underlying_def : ∀ {t : go.type} [t ↓u u], TypeRepr t V

export TypeReprUnderlying (type_repr_underlying_def)

instance type_repr_underlying [GoSemanticsFunctions] {t u : go.type} {V : Type} [ZeroVal V]
    [t ↓u u] [TypeReprUnderlying u V] : TypeRepr t V :=
  TypeReprUnderlying.type_repr_underlying_def (u := u)

/-- Helper definition to cover types for which `a == b` always executes safely. -/
class IsStrictlyComparable [GoSemanticsFunctions] (t : go.type) (V : Type) [DecidableEq V] :
    Prop where
  is_strictly_comparable :
    ∀ (v1 v2 : V), ⟦GoOp GoEquals t, (#v1, #v2)⟧ ⤳[under] #(decide (v1 = v2))

attribute [instance] IsStrictlyComparable.is_strictly_comparable
export IsStrictlyComparable (is_strictly_comparable)

class CoreComparisonSemantics [GoSemanticsFunctions] : Prop where
  /-- special case equality for functions -/
  go_op_go_equals_func_nil_l (sig : go.signature) (f : func.t) :
    ⟦GoOp GoEquals (go.FunctionType sig), (#f, #func.nil)⟧ ⤳[under] #(decide (f = func.nil))
  go_op_go_equals_func_nil_r (sig : go.signature) (f : func.t) :
    ⟦GoOp GoEquals (go.FunctionType sig), (#func.nil, #f)⟧ ⤳[under] #(decide (f = func.nil))

  check_comparable_pointer (t : go.type) :
    ⟦CheckComparable (go.PointerType t), #()⟧ ⤳[under] #()
  go_eq_pointer (t : go.type) : IsStrictlyComparable (go.PointerType t) loc

  check_comparable_channel (dir : go.chan_dir) (t : go.type) :
    ⟦CheckComparable (go.ChannelType dir t), #()⟧ ⤳[under] #()
  go_eq_channel (t : go.chan_dir) (dir : go.type) :
    IsStrictlyComparable (go.ChannelType t dir) loc

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
      ) (#true : expr) fds_unsealed)

attribute [instance] CoreComparisonSemantics.go_op_go_equals_func_nil_l
  CoreComparisonSemantics.go_op_go_equals_func_nil_r CoreComparisonSemantics.check_comparable_pointer
  CoreComparisonSemantics.go_eq_pointer CoreComparisonSemantics.check_comparable_channel
  CoreComparisonSemantics.go_eq_channel CoreComparisonSemantics.struct_is_comparable
  CoreComparisonSemantics.go_eq_struct
export CoreComparisonSemantics (go_op_go_equals_func_nil_l go_op_go_equals_func_nil_r
  check_comparable_pointer go_eq_pointer check_comparable_channel go_eq_channel
  struct_is_comparable go_eq_struct)

def struct_field_type (f : go_string) : List go.field_decl → go.type
  | [] => go.Named go!"field not found" []
  | go.FieldDecl f' t :: fds
  | go.EmbeddedField f' t :: fds =>
      if f = f' then t
      else struct_field_type f fds

class IntoValUnfold (V : Type) (f : outParam (V → val)) : Prop where
  into_val_unfold : @into_val _ _ V = f

/-- Rocq `into_val_unfold` (with `V` explicit). -/
theorem into_val_unfold (V : Type) {f : V → val} [IntoValUnfold V f] : @into_val _ _ V = f :=
  IntoValUnfold.into_val_unfold

class IntoValInj (V : Type) : Prop where
  into_val_inj : Function.Injective (into_val (V := V))

export IntoValInj (into_val_inj)

class BasicIntoValInj : Prop where
  [into_val_inj_loc : IntoValInj loc]
  [into_val_inj_slice : IntoValInj slice.t]
  [into_val_inj_w64 : IntoValInj w64]
  [into_val_inj_w32 : IntoValInj w32]
  [into_val_inj_w16 : IntoValInj w16]
  [into_val_inj_w8 : IntoValInj w8]
  [into_val_inj_bool : IntoValInj Bool]
  [into_val_inj_string : IntoValInj go_string]
  [into_val_inj_interface : IntoValInj interface.t]
  [into_val_inj_proph_id : IntoValInj proph_id]

attribute [instance] BasicIntoValInj.into_val_inj_loc BasicIntoValInj.into_val_inj_slice
  BasicIntoValInj.into_val_inj_w64 BasicIntoValInj.into_val_inj_w32
  BasicIntoValInj.into_val_inj_w16 BasicIntoValInj.into_val_inj_w8
  BasicIntoValInj.into_val_inj_bool BasicIntoValInj.into_val_inj_string
  BasicIntoValInj.into_val_inj_interface BasicIntoValInj.into_val_inj_proph_id

/-- `go.CoreSemantics` defines the basics of when a GoContext is valid,
excluding predeclared types (including primitives), arrays, slice, map, and
channels, each of which is in their own file. -/
class CoreSemantics [GoSemanticsFunctions] : Prop where
  [basic_into_val_inj : BasicIntoValInj]

  underlying_not_named {t : go.type} [NotNamed t] : t ↓u t

  -- Underlying-respecting instructions
  convert_underlying {from_ from_under to to_under : go.type} [from_ ↓u from_under]
    [to ↓u to_under] (v : val) (e : expr) [⟦Convert from_under to_under, v⟧ ⤳[under] e] :
    ⟦Convert from_ to, v⟧ ⤳ e
  go_un_op_underlying (o : go_unary_operator) {t t_under : go.type} [t ↓u t_under] (v : val)
    (e : expr) [⟦GoUnOp o t_under, v⟧ ⤳[under] e] : ⟦GoUnOp o t, v⟧ ⤳ e
  go_op_underlying (o : go_operator) {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦GoOp o t_under, v⟧ ⤳[under] e] : ⟦GoOp o t, v⟧ ⤳ e
  composite_literal_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦CompositeLiteral t_under, v⟧ ⤳[under] e] : ⟦CompositeLiteral t, v⟧ ⤳ e
  slice_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦Slice t_under, v⟧ ⤳[under] e] : ⟦Slice t, v⟧ ⤳ e
  full_slice_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦FullSlice t_under, v⟧ ⤳[under] e] : ⟦FullSlice t, v⟧ ⤳ e
  index_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦Index t_under, v⟧ ⤳[under] e] : ⟦Index t, v⟧ ⤳ e
  index_ref_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦IndexRef t_under, v⟧ ⤳[under] e] : ⟦IndexRef t, v⟧ ⤳ e
  check_comparable_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦CheckComparable t_under, v⟧ ⤳[under] e] : ⟦CheckComparable t, v⟧ ⤳ e
  struct_field_get_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    (f : go_string) [⟦StructFieldGet t_under f, v⟧ ⤳[under] e] : ⟦StructFieldGet t f, v⟧ ⤳ e
  struct_field_set_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    (f : go_string) [⟦StructFieldSet t_under f, v⟧ ⤳[under] e] : ⟦StructFieldSet t f, v⟧ ⤳ e
  struct_field_ref_step_underlying {t t_under : go.type} [t ↓u t_under] (f : go_string)
    (v : val) (e : expr) [⟦StructFieldRef t_under f, v⟧ ⤳[under] e] : ⟦StructFieldRef t f, v⟧ ⤳ e
  go_zero_val_step_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦GoZeroVal t_under, v⟧ ⤳[under] e] : ⟦GoZeroVal t, v⟧ ⤳ e

  go_func_resolve_step (n : go_string) (ts : List go.type) :
    ⟦FuncResolve n ts, #()⟧ ⤳ #(functions n ts)
  go_method_resolve_step (m : go_string) (t : go.type) (rcvr : val) {tunder : go.type}
    [t ↓u tunder] [NotInterface tunder] :
    ⟦MethodResolve t m, rcvr⟧ ⤳ #(methods t m rcvr)
  go_global_var_addr_step (v : go_string) : ⟦GlobalVarAddr v, #()⟧ ⤳ #(global_addr v)

  /-- FIXME: unsound semantics: simply computing the struct field address will
  panic if the base address is nil. This is a bit of a headache because every
  program step executing `StructFieldRef` will need to have a precondition that
  `l ≠ null`. -/
  struct_field_ref_step (t : go.type) (f : go_string) (l : loc) {V : Type} [ZeroVal V]
    [TypeRepr t V] : ⟦StructFieldRef t f, #l⟧ ⤳[under] #(struct_field_ref V f l)

  /-- The language spec doesn't say anything about the addresses of zero-sized
  allocation. But, in the runtime, these addresses are non-nil, so the
  semantics assumes it here.
  https://cs.opensource.google/go/go/+/refs/tags/go1.25.5:src/runtime/malloc.go;l=927
  https://cs.opensource.google/go/go/+/refs/tags/go1.25.5:src/runtime/malloc.go;l=1023 -/
  go_prealloc_step : is_go_step_pure GoPrealloc #() = (fun (e : expr) => ∃ (l : loc), l ≠ null ∧ e = #l)
  angelic_exit_step : is_go_step_pure AngelicExit #() = (fun (e : expr) => e = AngelicExit #())

  into_val_unfold_func : IntoValUnfold func.t (fun f => RecV f.f f.x f.e)
  into_val_unfold_bool : IntoValUnfold Bool (fun x => LitV (LitBool x))

  -- Eventually want to get rid of these.
  into_val_unfold_w64 : IntoValUnfold w64 (fun x => LitV (LitInt x))
  into_val_unfold_w32 : IntoValUnfold w32 (fun x => LitV (LitInt32 x))
  into_val_unfold_w16 : IntoValUnfold w16 (fun x => LitV (LitInt16 x))
  into_val_unfold_w8 : IntoValUnfold w8 (fun x => LitV (LitByte x))
  into_val_unfold_string : IntoValUnfold go_string (fun x => LitV (LitString x))
  into_val_unfold_loc : IntoValUnfold loc (fun x => LitV (LitLoc x))
  into_val_unfold_unit : IntoValUnfold Unit (fun _ => LitV LitUnit)

  go_zero_val_step {V : Type} [ZeroVal V] {t : go.type} [TypeRepr t V] :
    ⟦GoZeroVal t, #()⟧ ⤳ #(zero_val V)

  go_zero_val_pointer (t : go.type) : TypeReprUnderlying (go.PointerType t) loc
  go_zero_val_function (sig : go.signature) : TypeReprUnderlying (go.FunctionType sig) func.t
  go_zero_val_slice (elem_type : go.type) : TypeReprUnderlying (go.SliceType elem_type) slice.t
  go_zero_val_interface (elems : List go.interface_elem) :
    TypeReprUnderlying (go.InterfaceType elems) interface.t
  go_zero_val_channel (dir : go.chan_dir) (elem_type : go.type) :
    TypeReprUnderlying (go.ChannelType dir elem_type) chan.t
  go_zero_val_map (key_type elem_type : go.type) :
    TypeReprUnderlying (go.MapType key_type elem_type) map.t

  [core_comparison_sem : CoreComparisonSemantics]

  composite_literal_pointer (elem_type : go.type) (l : val) :
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
                             (v, Convert from_ (struct_field_type field_name fds_unsealed) e))
                       | _ => Panic "invalid Go code"
                ) (GoZeroVal (go.StructType fds) #()) l)

  alloc_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦GoAlloc t_under, v⟧ ⤳[internal_under] e] : ⟦GoAlloc t, v⟧ ⤳[internal] e
  load_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦GoLoad t_under, v⟧ ⤳[internal_under] e] : ⟦GoLoad t, v⟧ ⤳[internal] e
  store_underlying {t t_under : go.type} [t ↓u t_under] (v : val) (e : expr)
    [⟦GoStore t_under, v⟧ ⤳[internal_under] e] : ⟦GoStore t, v⟧ ⤳[internal] e

  alloc_primitive (v : val) (u : go.type) [H : is_primitive u] :
    ⟦GoAlloc u, v⟧ ⤳[internal_under] Alloc v
  alloc_struct (v : val) {fds fds_unsealed : List go.field_decl} [fds =→ fds_unsealed] :
    ⟦GoAlloc (go.StructType fds), v⟧ ⤳[internal_under]
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
         ) (#() : expr) fds_unsealed ;;
       "l")

  load_primitive (u : go.type) [H : is_primitive u] (l : val) :
    ⟦GoLoad u, l⟧ ⤳[internal_under] Read l

  load_struct (fds : List go.field_decl) (l : val) {fds_unsealed : List go.field_decl}
    [fds =→ fds_unsealed] :
    ⟦GoLoad (go.StructType fds), l⟧ ⤳[internal_under]
      (List.foldl (fun struct_so_far fd =>
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => (n, t)
                                                | go.EmbeddedField n t => (n, t)
                let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                let field_val := gl(GoLoad field_type field_addr)
                gl(StructFieldSet (go.StructType fds) field_name (struct_so_far, field_val))
         ) (GoZeroVal (go.StructType fds) #()) fds_unsealed)

  store_primitive (u : go.type) [H : is_primitive u] (l v : val) :
    ⟦GoStore u, (l, v)⟧ ⤳[internal_under] Store l v
  store_struct {fds fds_unsealed : List go.field_decl} [fds =→ fds_unsealed] (l v : val) :
    ⟦GoStore (go.StructType fds), (l, v)⟧ ⤳[internal_under]
      (List.foldl (fun store_so_far fd =>
                gl(store_so_far ;;
                  (let (field_name, field_type) := match fd with
                                                  | go.FieldDecl n t => (n, t)
                                                  | go.EmbeddedField n t => (n, t)
                   let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                   let field_val := gl(StructFieldGet (go.StructType fds) field_name v)
                   gl(GoStore field_type (field_addr, field_val))))
         ) (#() : expr) fds_unsealed)

  is_convert_underlying_same (t : go.type) (v : val) : ⟦Convert t t, v⟧ ⤳[under] v
  convert_same (t : go.type) (v : val) : ⟦Convert t t, v⟧ ⤳ v

attribute [instance] CoreSemantics.basic_into_val_inj CoreSemantics.underlying_not_named
  CoreSemantics.convert_underlying CoreSemantics.go_un_op_underlying
  CoreSemantics.go_op_underlying CoreSemantics.composite_literal_underlying
  CoreSemantics.slice_underlying CoreSemantics.full_slice_underlying
  CoreSemantics.index_underlying CoreSemantics.index_ref_underlying
  CoreSemantics.check_comparable_underlying CoreSemantics.struct_field_get_underlying
  CoreSemantics.struct_field_set_underlying CoreSemantics.struct_field_ref_step_underlying
  CoreSemantics.go_zero_val_step_underlying CoreSemantics.go_func_resolve_step
  CoreSemantics.go_method_resolve_step CoreSemantics.go_global_var_addr_step
  CoreSemantics.struct_field_ref_step CoreSemantics.into_val_unfold_func
  CoreSemantics.into_val_unfold_bool CoreSemantics.into_val_unfold_w64
  CoreSemantics.into_val_unfold_w32 CoreSemantics.into_val_unfold_w16
  CoreSemantics.into_val_unfold_w8 CoreSemantics.into_val_unfold_string
  CoreSemantics.into_val_unfold_loc CoreSemantics.into_val_unfold_unit
  CoreSemantics.go_zero_val_step CoreSemantics.go_zero_val_pointer
  CoreSemantics.go_zero_val_function CoreSemantics.go_zero_val_slice
  CoreSemantics.go_zero_val_interface CoreSemantics.go_zero_val_channel
  CoreSemantics.go_zero_val_map CoreSemantics.core_comparison_sem
  CoreSemantics.composite_literal_pointer CoreSemantics.composite_literal_struct
  CoreSemantics.alloc_underlying CoreSemantics.load_underlying CoreSemantics.store_underlying
  CoreSemantics.alloc_primitive CoreSemantics.alloc_struct CoreSemantics.load_primitive
  CoreSemantics.load_struct CoreSemantics.store_primitive CoreSemantics.store_struct
  CoreSemantics.is_convert_underlying_same CoreSemantics.convert_same

export CoreSemantics (basic_into_val_inj underlying_not_named convert_underlying
  go_un_op_underlying go_op_underlying composite_literal_underlying slice_underlying
  full_slice_underlying index_underlying index_ref_underlying check_comparable_underlying
  struct_field_get_underlying struct_field_set_underlying struct_field_ref_step_underlying
  go_zero_val_step_underlying go_func_resolve_step go_method_resolve_step go_global_var_addr_step
  struct_field_ref_step go_prealloc_step angelic_exit_step into_val_unfold_func
  into_val_unfold_bool into_val_unfold_w64 into_val_unfold_w32 into_val_unfold_w16
  into_val_unfold_w8 into_val_unfold_string into_val_unfold_loc into_val_unfold_unit
  go_zero_val_step go_zero_val_pointer go_zero_val_function go_zero_val_slice
  go_zero_val_interface go_zero_val_channel go_zero_val_map core_comparison_sem
  composite_literal_pointer composite_literal_struct alloc_underlying load_underlying
  store_underlying alloc_primitive alloc_struct load_primitive load_struct store_primitive
  store_struct is_convert_underlying_same convert_same)

end defs
end go

/-- Rocq `@! func`: `#(functions func [])`. -/
scoped syntax:max "@! " term:max : term
/-- Rocq `rcvr @! type @! method`: `#(methods type method #rcvr)`. Written
`rcvr @!! type @!! method` in Lean, since `rcvr @! ...` parses as an application
of `rcvr` to `@! ...`. -/
scoped syntax:80 term:81 " @!! " term:81 " @!! " term:81 : term
/-- Rocq `![t] e`: typed load. -/
scoped syntax:max "![" term "] " term:max : term
/-- Rocq `e1 <-[t] e2`: typed store. -/
scoped syntax:40 term:41 " <-[" term "] " term:40 : term

macro_rules
  | `(@! $f) => `(into_val (functions $f []))
  | `($r @!! $t @!! $m) => `(into_val (methods $t $m (into_val $r)))
  | `(![$t] $e) => `(App (Val (GoInstruction (GoLoad $t))) gl($e))
  | `($e1 <-[$t] $e2) => `(App (Val (GoInstruction (GoStore $t))) (Pair gl($e1) gl($e2)))

end Perennial
