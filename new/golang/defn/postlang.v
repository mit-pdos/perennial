(* Trusted stuff that's conceptually part of the GooseLang semantics. E.g.
   assumptions about valid GoContext and definition of zero values via
   IntoVal. *)

From Perennial.goose_lang Require Export lang.
From Perennial Require Export base.

#[warning="-uniform-inheritance"]
Global Coercion GoInstruction : go_instruction >-> val.

Global Notation "()" := tt : val_scope.
Global Opaque into_val.

Global Notation "# x" := (into_val x%go).
Global Notation "#" := into_val (at level 0).

(* Shortcircuit Boolean connectives *)
Global Notation "e1 && e2" :=
  (If e1%E e2%E #false) (only parsing) : expr_scope.
Global Notation "e1 || e2" :=
  (If e1%E #true e2%E) (only parsing) : expr_scope.

Notation "e1 ≤⟨ t ⟩ e2" := (GoInstruction (GoLe t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ≤⟨ t ⟩  e2") : expr_scope.
Notation "e1 <⟨ t ⟩ e2" := (GoInstruction (GoLt t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  <⟨ t ⟩  e2") : expr_scope.
Notation "e1 ≥⟨ t ⟩ e2" := (GoInstruction (GoGe t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ≥⟨ t ⟩  e2") : expr_scope.
Notation "e1 >⟨ t ⟩ e2" := (GoInstruction (GoGt t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  >⟨ t ⟩  e2") : expr_scope.
Notation "e1 =⟨ t ⟩ e2" := (GoInstruction (GoEquals t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  =⟨ t ⟩  e2") : expr_scope.
Notation "e1 ≠⟨ t ⟩ e2" := (UnOp NegOp (e1%E =⟨t⟩ e2%E))
                             (at level 70, format "e1  ≠⟨ t ⟩  e2") : expr_scope.

Module map.
Definition t := loc.
Definition nil : t := null.
End map.

Module go.
Section defs.
Context {ext : ffi_syntax}.
(** This semantics considers several Go types to be [primitive] in the sense
    that they are modeled as taking a single heap location. Predeclared types
    and in their own file. *)
Inductive is_primitive : go.type → Prop :=
| is_primitive_pointer t : is_primitive (go.PointerType t)
| is_primitive_function sig : is_primitive (go.FunctionType sig)
| is_primitive_interface elems : is_primitive (go.InterfaceType elems)
| is_primitive_slice elem : is_primitive (go.SliceType elem)
| is_primitive_map kt vt : is_primitive (go.MapType kt vt)
| is_primitive_channel dir t : is_primitive (go.ChannelType dir t).

Inductive is_primitive_zero_val : go.type → val → Prop :=
| is_primitive_zero_val_pointer t : is_primitive_zero_val (go.PointerType t) #null
| is_primitive_zero_val_function t : is_primitive_zero_val (go.FunctionType t) #func.nil
| is_primitive_zero_valinterface elems : is_primitive_zero_val (go.InterfaceType elems) #interface.nil
| is_primitive_zero_val_slice elem : is_primitive_zero_val (go.SliceType elem) #slice.nil
| is_primitive_zero_val_map kt vt : is_primitive_zero_val (go.MapType kt vt) #null
| is_primitive_zero_val_channel dir t : is_primitive_zero_val (go.ChannelType dir t) #null.

Global Instance interface_eq_dec : EqDecision interface.t.
Proof. solve_decision. Qed.

Global Instance array_eq_dec t V n `{!EqDecision V} : EqDecision (array.t t V n).
Proof. solve_decision. Qed.

Global Instance func_eq_dec : EqDecision func.t.
Proof. solve_decision. Qed.

(* [go_eq_top_level] includes special cases for slice, map, and func comparison.
   [go_eq] does not. This helps define the semantics of comparing interface
   values. *)
Class CoreComparisonDefinition {go_ctx : GoContext} :=
{
  go_eq : go.type → val → val → expr;
}.

(* These types support actually exeucting `a == b`. E.g. slices, maps, funcs do
   not support this; they only support some special cases in go_eq_top_level. *)
Definition is_comparable t `{!GoContext} `{!CoreComparisonDefinition} : Prop :=
  ∀ (v1 v2 : val), go_eq_top_level t v1 v2 = go_eq t v1 v2.

(* These types have the semantics that `a == b` reduces to true if the semantic
   representation of `a` is equal to `b` and false otherwise. *)
Definition is_always_comparable t V `{!EqDecision V} `{!IntoVal V}
  `{!GoContext} `{!CoreComparisonDefinition} : Prop :=
  ∀ (v1 v2 : V), go_eq t #v1 #v2 = #(bool_decide (v1 = v2)).

(* Here's an example exhibiting struct comparison subtleties:

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
*)
Class CoreComparisonSemantics {go_ctx : GoContext} :=
{
  #[global] core_comp_def :: CoreComparisonDefinition;
  go_eq_top_level_underlying t : go_eq_top_level t = go_eq_top_level (to_underlying t);
  go_eq_underlying t : go_eq t = go_eq (to_underlying t);

  (* special cases *)
  go_eq_func_nil_l sig f :
    go_eq_top_level (go.FunctionType sig) #f #func.nil = #(bool_decide (f = func.nil));
  go_eq_func_nil_r sig f :
    go_eq_top_level (go.FunctionType sig) #func.nil #f = #(bool_decide (f = func.nil));
  go_eq_slice_nil_l t s :
    go_eq_top_level (go.SliceType t) #s #slice.nil = #(bool_decide (s = slice.nil));
  go_eq_slice_nil_r t s :
    go_eq_top_level (go.SliceType t) #slice.nil #s = #(bool_decide (s = slice.nil));
  go_eq_map_nil_l kt vt m :
    go_eq_top_level (go.MapType kt vt) #m #map.nil = #(bool_decide (m = map.nil));
  go_eq_map_nil_r kt vt m :
    go_eq_top_level (go.MapType kt vt) #map.nil #m = #(bool_decide (m = map.nil));

  is_comparable_pointer t : is_comparable (go.PointerType t);
  go_eq_pointer t : is_always_comparable (go.PointerType t) loc;

  is_comparable_channel t dir : is_comparable (go.ChannelType dir t);
  go_eq_channel t dir : is_always_comparable (go.ChannelType dir t) chan.t;

  is_comparable_interface elems : is_comparable (go.InterfaceType elems);
  go_eq_interface_ne elems t1 t2 v1 v2 (H : t1 ≠ t2) :
    go_eq (go.InterfaceType elems) #(interface.mk t1 v1) #(interface.mk t2 v2) = #false;
  go_eq_interface elems t v1 v2 :
    go_eq (go.InterfaceType elems) #(interface.mk t v1) #(interface.mk t v2) = go_eq t v1 v2;
  go_eq_interface_nil_r elems i :
    go_eq (go.InterfaceType elems) #i #interface.nil = #(bool_decide (i = interface.nil));
  go_eq_interface_nil_l elems i :
    go_eq (go.InterfaceType elems) #interface.nil #i = #(bool_decide (i = interface.nil));

  is_comparable_struct fds :
    is_comparable (go.StructType fds) ↔
    Forall (λ fd,
              is_comparable (
                  match fd with go.FieldDecl n t => t | go.EmbeddedField n t => t end
      )) fds;
  _go_eq_struct fds v1 v2 :
    go_eq (go.StructType fds) v1 v2 =
    foldl (λ cmp_so_far fd,
             let (field_name, field_type) :=
               match fd with go.FieldDecl n t => (n, t) | go.EmbeddedField n t => (n, t) end in
             (if: cmp_so_far then
                GoEquals field_type (StructFieldGet field_name v1, StructFieldGet field_name v2)
              else #false)%E
      ) #true fds
}.

(** [go.CoreSemantics] defines the basics of when a GoContext is valid,
    excluding predeclared types (including primitives), arrays, slice, map, and
    channels, each of which is in their own file.

    The rules prefixed with [_] should not be used in any program proofs. *)
Class CoreSemantics {go_ctx : GoContext} :=
{
  #[global] core_comparison_sem :: CoreComparisonSemantics;

  alloc_underlying t : alloc t = alloc (to_underlying t);
  alloc_primitive t v (H : is_primitive_zero_val t v) : alloc t = (λ: <>, ref v)%V;
  alloc_struct fds :
    alloc (go.StructType fds) =
    (λ: <>,
        let: "l" := GoPrealloc #() in
        foldl (λ alloc_so_far fd,
                 alloc_so_far ;;
                 let (field_name, field_type) := match fd with
                                                 | go.FieldDecl n t => pair n t
                                                 | go.EmbeddedField n t => pair n t
                                                 end in
                let field_addr := StructFieldRef (go.StructType fds) field_name "l" in
                let: "l_field" := GoAlloc field_type #() in
                if: ("l_field" ≠⟨go.PointerType field_type⟩ field_addr) then AngelicExit #()
                else #()
          ) #() fds ;;
        "l")%V;

  load_underlying t : load t = load (to_underlying t);
  load_primitive t (H : is_primitive t) : load t = (λ: "l", Read "l")%V;
  load_struct fds :
    load (go.StructType fds) =
    (λ: "l",
       foldl (λ struct_so_far fd,
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef (go.StructType fds) field_name "l" in
                let field_val := GoLoad field_type field_addr in
                StructFieldSet field_name (struct_so_far, field_val)
         ) (StructV ∅) fds)%V;

  store_underlying t : store t = store (to_underlying t);
  store_primitive t (H : is_primitive t) : store t = (λ: "l" "v", "l" <- "v")%V;
  store_struct fds :
    store (go.StructType fds) =
    (λ: "l" "v",
       foldl (λ store_so_far fd,
                store_so_far;;
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef (go.StructType fds) field_name "l" in
                let field_val := StructFieldGet field_name "v" in
                GoStore field_type (field_addr, field_val)
         ) (StructV ∅) fds)%V;

  struct_field_ref_underlying t : struct_field_ref t = struct_field_ref (to_underlying t);
  index_ref_underlying t : index_ref t = index_ref (to_underlying t);
  index_underlying t : index t = index (to_underlying t);

  method_interface t m (H : is_interface_type t = true) :
    #(methods t m) = (InterfaceGet m);
}.

End defs.
End go.

Notation "@! func" :=
  #(functions func []) (at level 1, no associativity, format "@! func") : expr_scope.

Notation "![ t ] e" := (GoInstruction (GoLoad t) e%E)
                         (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Notation "e1 <-[ t ] e2" := (GoInstruction (GoStore t) (Pair e1%E e2%E))
                             (at level 80, format "e1  <-[ t ]  e2") : expr_scope.
