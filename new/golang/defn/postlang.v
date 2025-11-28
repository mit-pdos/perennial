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

(** [IsComparable t] means that semantics for `==` is defined for the type [t].
    Corresponds to _comparable_ as defined in
    https://go.dev/ref/spec#Comparison_operators. This does not mean that `==`
    will run safely for [t]; specifically, interfaces are comparable but
    `==` can still panic. The types for which this holds is specified
    in recursive way in [CoreSemantics]. *)
Class IsComparable t `{!GoContext} `{!CoreComparisonDefinition} : Prop :=
  {
    is_comparable : ∀ (v1 v2 : val), go_eq_top_level t v1 v2 = go_eq t v1 v2;
  }.

(* Helper definition to cover types for whom `a == b` always executes safely. *)
Definition is_always_safe_to_compare t V `{!EqDecision V} `{!IntoVal V}
  `{!GoContext} `{!CoreComparisonDefinition} : Prop :=
  ∀ (v1 v2 : V), go_eq t #v1 #v2 = #(bool_decide (v1 = v2)).

Definition AllocValue_def t : val :=
  λ: "v", let: "l" := GoAlloc t #() in GoStore t ("l", "v");; "l".
Program Definition AllocValue := sealed AllocValue_def.
Definition AllocValue_unseal : AllocValue = _ := seal_eq _.

Definition ZeroVal_def t : val :=
  λ: <>, let: "l" := GoAlloc t #() in GoLoad t "l".
Program Definition ZeroVal := sealed ZeroVal_def.
Definition ZeroVal_unseal : ZeroVal = _ := seal_eq _.

Definition ElementListNil_def (key_type : option go.type) (elem_type : go.type) : val :=
  λ: <>, ArrayV [].
Program Definition ElementListNil := sealed ElementListNil_def.
Definition ElementListNil_unseal : ElementListNil = _ := seal_eq _.

Definition ElementListApp_def : val :=
  λ: "v" "l", ArrayAppend ("l", "v").
Program Definition ElementListApp := sealed ElementListApp_def.
Definition ElementListApp_unseal : ElementListApp = _ := seal_eq _.

Definition StructElementListNil_def : val :=
  λ: <>, ArrayV [].
Program Definition StructElementListNil := sealed StructElementListNil_def.
Definition StructElementListNil_unseal : StructElementListNil = _ := seal_eq _.

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

  #[global]
  is_comparable_pointer t :: IsComparable (go.PointerType t);
  go_eq_pointer t : is_always_safe_to_compare (go.PointerType t) loc;

  #[global]
  is_comparable_channel t dir :: IsComparable (go.ChannelType t dir);
  go_eq_channel t dir : is_always_safe_to_compare (go.ChannelType t dir) loc;

  #[global]
  is_comparable_interface elems :: IsComparable (go.InterfaceType elems);
  go_eq_interface elems i1 i2 :
    go_eq (go.InterfaceType elems) #i1 #i2 =
      match i1, i2 with
      | interface.nil, interface.nil => #true
      | (interface.mk t1 v1), (interface.mk t2 v2) =>
          if decide (t1 = t2) then go_eq t1 v1 v2
          else #false
      | _, _ => #false
      end;

  is_comparable_struct fds :
    IsComparable (go.StructType fds) ↔
    Forall (λ fd,
              IsComparable (
                  match fd with go.FieldDecl n t => t | go.EmbeddedField n t => t end
      )) fds;
  go_eq_struct fds v1 v2 :
    go_eq (go.StructType fds) v1 v2 =
    foldl (λ cmp_so_far fd,
             let (field_name, field_type) :=
               match fd with go.FieldDecl n t => (n, t) | go.EmbeddedField n t => (n, t) end in
             (if: cmp_so_far then
                (StructFieldGet (go.StructType fds) field_name v1) =⟨field_type⟩
                (StructFieldGet (go.StructType fds) field_name v2)
              else #false)%E
      ) #true fds
}.

Fixpoint struct_field_type (f : go_string) (fds : list go.field_decl) : go.type :=
  match fds with
  | [] => go.Named "field not found"%go []
  | go.FieldDecl f' t :: fds
  | go.EmbeddedField f' t :: fds =>
      if (ByteString.eqb f f') then t
      else struct_field_type f fds
  end.

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
                StructFieldSet (go.StructType fds) field_name (struct_so_far, field_val)
         ) (go_zero_val (go.StructType fds)) fds)%V;

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
                let field_val := StructFieldGet (go.StructType fds) field_name "v" in
                GoStore field_type (field_addr, field_val)
         ) (go_zero_val (go.StructType fds)) fds)%V;

  struct_field_ref_underlying t : struct_field_ref t = struct_field_ref (to_underlying t);
  index_ref_underlying t : index_ref t = index_ref (to_underlying t);
  index_underlying t : index t = index (to_underlying t);

  method_interface t m (H : is_interface_type t = true) :
    #(methods t m) = (InterfaceGet m);

  composite_literal_underlying t :
    composite_literal t = composite_literal (to_underlying t);

  composite_literal_pointer elem_type l :
    composite_literal (go.PointerType elem_type) l  =
    AllocValue elem_type (CompositeLiteral elem_type l);

  composite_literal_struct fds l :
    composite_literal (go.StructType fds) (LiteralValue l)  =
    match l with
    | [] => go_zero_val $ go.StructType fds
    | KeyedElement None _ :: _ =>
        (* unkeyed struct literal *)
        foldl (λ v '(fd, ke),
                 let (field_name, field_type) :=
                   match fd with
                   | go.FieldDecl n t | go.EmbeddedField n t => pair n t
                   end in
                 match ke with
                 | KeyedElement None (ElementExpression e) =>
                     StructFieldSet (go.StructType fds) field_name (v, e)%E
                 | KeyedElement None (ElementLiteralValue el) =>
                     StructFieldSet (go.StructType fds) field_name
                       (v, (CompositeLiteral field_type (LiteralValue el)))%E
                       (* NOTE: if field_type is `*A`, then this will be
                           *A {...}, which the semantics can interpret as &A{...} *)
                 | _ => Panic "invalid Go code"
                 end
          ) (Val $ go_zero_val $ go.StructType fds) (zip fds l)
    | KeyedElement (Some _) _ :: _ =>
        (* keyed struct literal *)
        foldl (λ v ke,
                 match ke with
                 | KeyedElement (Some (KeyField field_name)) (ElementExpression e) =>
                     StructFieldSet (go.StructType fds) field_name (v, e)%E
                 | KeyedElement (Some (KeyField field_name)) (ElementLiteralValue el) =>
                     StructFieldSet (go.StructType fds) field_name
                       (v, (CompositeLiteral (struct_field_type field_name fds) (LiteralValue el)))%E
                 | _ => Panic "invalid Go code"
                 end
          ) (Val $ go_zero_val $ go.StructType fds) l
    end
}.

End defs.
End go.

Notation "@! func" :=
  #(functions func []) (at level 1, no associativity, format "@! func") : expr_scope.

Notation "![ t ] e" := (GoInstruction (GoLoad t) e%E)
                         (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Notation "e1 <-[ t ] e2" := (GoInstruction (GoStore t) (Pair e1%E e2%E))
                             (at level 80, format "e1  <-[ t ]  e2") : expr_scope.
