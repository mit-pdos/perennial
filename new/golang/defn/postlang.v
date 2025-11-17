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

Inductive is_primitive_zero_val : go.type → ∀ {V} `{!IntoVal V}, V → Prop :=
| is_primitive_zero_val_pointer t : is_primitive_zero_val (go.PointerType t) null
| is_primitive_zero_val_function t : is_primitive_zero_val (go.FunctionType t) func.nil
(* | is_primitive_interface elems : is_primitive (go.InterfaceType elems) *)
| is_primitive_zero_val_slice elem : is_primitive_zero_val (go.SliceType elem) slice.nil
| is_primitive_zero_val_map kt vt : is_primitive_zero_val (go.MapType kt vt) null
| is_primitive_zero_val_channel dir t : is_primitive_zero_val (go.ChannelType dir t) null.

Global Instance interface_eq_dec : EqDecision interface.t.
Proof. solve_decision. Qed.

Global Instance array_eq_dec t V n `{!EqDecision V} : EqDecision (array.t t V n).
Proof. solve_decision. Qed.

Global Instance func_eq_dec : EqDecision func.t.
Proof. solve_decision. Qed.

Definition is_strictly_comparable t V `{!EqDecision V} `{!IntoVal V} `{!GoContext} : Prop :=
  ∀ (v1 v2 : V), go_equals t #v1 #v2 = Some $ bool_decide (v1 = v2).

Class CoreComparisonSemantics {go_ctx : GoContext} :=
{
  equals_underlying t : go_equals t = go_equals (to_underlying t);
  equals_pointer t : is_strictly_comparable (go.PointerType t) loc;
  equals_channel t dir : is_strictly_comparable (go.ChannelType dir t) chan.t;
  equals_interface_nil_r elems i :
    go_equals (go.InterfaceType elems) #i #interface.nil = Some $ bool_decide (i = interface.nil);
  equals_interface_nil_l elems i :
    go_equals (go.InterfaceType elems) #interface.nil #i = Some $ bool_decide (i = interface.nil);
  equals_interface elems t v1 v2 :
    go_equals (go.InterfaceType elems) #(interface.mk t v1) #(interface.mk t v2) =
    go_equals t v1 v2;

  equals_func_l sig f :
    go_equals (go.FunctionType sig) #f #func.nil = Some $ bool_decide (f = func.nil);
  equals_func_r sig f :
    go_equals (go.FunctionType sig) #func.nil #f = Some $ bool_decide (f = func.nil);
}.

(** [go.CoreSemantics] defines the basics of when a GoContext is valid,
    excluding predeclared types (including primitives), slice, map, and
    channels, each of which is in their own file.

    The rules prefixed with [_] should not be used in any program proofs. *)
Class CoreSemantics {go_ctx : GoContext} :=
{
  #[global] core_comparison_sem :: CoreComparisonSemantics;

  alloc_underlying t : alloc t = alloc (to_underlying t);
  alloc_primitive t {V} (v : V) `{!IntoVal V} (H : is_primitive_zero_val t v) :
    alloc t = (λ: <>, ref #v)%V;
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
