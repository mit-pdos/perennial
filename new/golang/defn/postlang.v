(* Trusted stuff that's conceptually part of the GooseLang semantics. E.g.
   assumptions about valid GoLocalContext. *)

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

Notation "e1 ≤⟨ t ⟩ e2" := (GoInstruction (GoOp GoLe t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ≤⟨ t ⟩  e2") : expr_scope.
Notation "e1 <⟨ t ⟩ e2" := (GoInstruction (GoOp GoLt t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  <⟨ t ⟩  e2") : expr_scope.
Notation "e1 ≥⟨ t ⟩ e2" := (GoInstruction (GoOp GoGe t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ≥⟨ t ⟩  e2") : expr_scope.
Notation "e1 >⟨ t ⟩ e2" := (GoInstruction (GoOp GoGt t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  >⟨ t ⟩  e2") : expr_scope.
Notation "e1 =⟨ t ⟩ e2" := (GoInstruction (GoOp GoEquals t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  =⟨ t ⟩  e2") : expr_scope.
Notation "e1 ≠⟨ t ⟩ e2" := (UnOp NegOp (e1%E =⟨t⟩ e2%E))
                             (at level 70, format "e1  ≠⟨ t ⟩  e2") : expr_scope.

Notation "e1 +⟨ t ⟩ e2" := (GoInstruction (GoOp GoPlus t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  +⟨ t ⟩  e2") : expr_scope.
Notation "e1 -⟨ t ⟩ e2" := (GoInstruction (GoOp GoSub t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  -⟨ t ⟩  e2") : expr_scope.
Notation "e1 *⟨ t ⟩ e2" := (GoInstruction (GoOp GoMul t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  *⟨ t ⟩  e2") : expr_scope.
Notation "e1 /⟨ t ⟩ e2" := (GoInstruction (GoOp GoDiv t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  /⟨ t ⟩  e2") : expr_scope.
Notation "e1 %⟨ t ⟩ e2" := (GoInstruction (GoOp GoRemainder t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  %⟨ t ⟩  e2") : expr_scope.

Notation "e1 &⟨ t ⟩ e2" := (GoInstruction (GoOp GoAnd t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  &⟨ t ⟩  e2") : expr_scope.
Notation "e1 |⟨ t ⟩ e2" := (GoInstruction (GoOp GoOr t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  |⟨ t ⟩  e2") : expr_scope.
Notation "e1 ^⟨ t ⟩ e2" := (GoInstruction (GoOp GoXor t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ^⟨ t ⟩  e2") : expr_scope.
Notation "e1 &^⟨ t ⟩ e2" := (GoInstruction (GoOp GoBitClear t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  &^⟨ t ⟩  e2") : expr_scope.
Notation "e1 <<⟨ t ⟩ e2" := (GoInstruction (GoOp GoShiftl t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  <<⟨ t ⟩  e2") : expr_scope.
Notation "e1 >>⟨ t ⟩ e2" := (GoInstruction (GoOp GoShiftr t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  >>⟨ t ⟩  e2") : expr_scope.

Module map.
Definition t := loc.
Definition nil : t := null.
End map.

Class GoSemanticsFunctions {ext : ffi_syntax} :=
  {
    to_underlying : go.type → go.type;
    global_addr : go_string → loc;
    functions : go_string → list go.type → func.t;
    methods : go.type → go_string → func.t;
    go_op : go_operator → go.type → val → expr;
    go_zero_val : go.type → val;

    (* Go equality function without special cases; e.g. any slice comparison will
       panic here. *)
    go_eq : go.type → val → val → expr;

    method_set : go.type → gmap go_string go.signature;

    alloc : go.type → val;
    load : go.type → val;
    store : go.type → val;

    struct_field_ref : go.type → go_string → loc → loc;
    struct_field_get : go.type → go_string → val → expr;
    struct_field_set : go.type → go_string → val → val → expr;

    (* map index expressions have their own implementation that does not use the
       `Index` primitive. It's statically (even with type parameters) known
       whether an index expression is a map index expression or not a map index
       expression. https://go.dev/ref/spec#Index_expressions *)
    index (container_type : go.type) (i : Z) (v : val) : expr;
    index_ref (container_type : go.type) (i : Z) (v : val) : expr;
    array_index_ref (elem_type : go.type) (i : Z) (l : loc) : loc;

    map_empty : val → val;
    map_lookup : val → val → bool * val;
    map_insert : val → val → val → val;
    map_delete : val → val → val;
    is_map_domain : val → list val → Prop;
    composite_literal : go.type → val → expr;

    is_map_pure (v : val) (m : val → bool * val) : Prop;
    map_default : val → val;
  }.

Section unfolding_defs.
Context {ext : ffi_syntax} `{!GoSemanticsFunctions} {go_gctx : GoGlobalContext}.

Class FuncUnfold f type_args f_impl : Prop :=
  {
    func_unfold : #(functions f type_args) = f_impl;
  }.
Global Hint Mode FuncUnfold ! ! - : typeclass_instances.

Class MethodUnfold t m m_impl : Prop :=
  {
    method_unfold : #(methods t m) = m_impl;
  }.
Global Hint Mode MethodUnfold ! ! - : typeclass_instances.
End unfolding_defs.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.
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

Definition ref_one : val :=
  λ: "v", let: "l" := ref (LitV $ LitString "") in "l" <- "v";; "l".

Definition AllocValue_def t : val :=
  λ: "v", let: "l" := GoAlloc t #() in GoStore t ("l", "v");; "l".
Program Definition AllocValue := sealed AllocValue_def.
Definition AllocValue_unseal : AllocValue = _ := seal_eq _.

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

Class IsGoStepPureDet instr args e : Prop :=
  {
    is_go_step_det s s' e' :
      is_go_step instr args e' s s' ↔ is_go_step_pure instr args e' ∧ s = s';
    is_go_step_pure_det : is_go_step_pure instr args = eq e;
  }.

(* No-op steps are for producing later credits. Doesn't really change the semantics *)
Class GoExprEq (e e' : expr) : Prop :=
  {
    go_expr_eq : e = (#();; e')%E;
  }.

#[global] Hint Mode GoExprEq ! - : typeclass_instances.

Class IsGoOp op t args v `{!GoSemanticsFunctions} : Prop :=
  {
    #[global] is_go_op :: GoExprEq (go_op op t args) v;
  }.

Class IsComparable t `{!GoSemanticsFunctions} : Prop :=
  {
    is_comparable v1 v2  :: IsGoOp GoEquals t (v1, v2)%V (go_eq t v1 v2)
  }.

(* Helper definition to cover types for which `a == b` always executes safely. *)
Class AlwaysSafelyComparable t V `{!EqDecision V} `{!GoSemanticsFunctions} : Prop :=
  {
    #[global] is_safely_comparable ::
      ∀ (v1 v2 : V), GoExprEq (go_eq t #v1 #v2) (#(bool_decide (v1 = v2)))%E;
  }.

Class CoreComparisonSemantics `{!GoSemanticsFunctions} : Prop :=
{
  go_op_underlying o t args : go_op o t args = go_op o (to_underlying t) args;
  go_eq_underlying t : go_eq t = go_eq (to_underlying t);

  (* special case equality for functions *)
  #[global] is_go_op_go_equals_func_nil_l sig f ::
    IsGoOp GoEquals (go.FunctionType sig) (#f, #func.nil)%V #(bool_decide (f = func.nil));
  #[global] is_go_op_go_equals_func_nil_r sig f ::
    IsGoOp GoEquals (go.FunctionType sig) (#func.nil, #f)%V #(bool_decide (f = func.nil));

  #[global] is_comparable_pointer t :: IsComparable (go.PointerType t);
  #[global] go_eq_pointer t :: AlwaysSafelyComparable (go.PointerType t) loc;

  #[global] is_comparable_channel t dir :: IsComparable (go.ChannelType t dir);
  #[global] go_eq_channel t dir :: AlwaysSafelyComparable (go.ChannelType t dir) loc;

  #[global] is_comparable_interface elems :: IsComparable (go.InterfaceType elems);
  #[global] go_eq_interface elems i1 i2 ::
    GoExprEq (go_eq (go.InterfaceType elems) #i1 #i2)
      (match i1, i2 with
       | interface.nil, interface.nil => #true
       | (interface.mk t1 v1), (interface.mk t2 v2) =>
           if decide (t1 = t2) then go_eq t1 v1 v2
           else #false
       | _, _ => #false
       end);

  is_comparable_struct fds :
    IsComparable (go.StructType fds) ↔
    Forall (λ fd,
              IsComparable (
                  match fd with go.FieldDecl n t => t | go.EmbeddedField n t => t end
      )) fds;
  go_eq_struct fds v1 v2 ::
    GoExprEq (go_eq (go.StructType fds) v1 v2)
    (foldl (λ cmp_so_far fd,
             let (field_name, field_type) :=
               match fd with go.FieldDecl n t => (n, t) | go.EmbeddedField n t => (n, t) end in
             (if: cmp_so_far then
                (StructFieldGet (go.StructType fds) field_name v1) =⟨field_type⟩
                (StructFieldGet (go.StructType fds) field_name v2)
              else #false)%E
      ) #true fds);
}.

Fixpoint struct_field_type (f : go_string) (fds : list go.field_decl) : go.type :=
  match fds with
  | [] => go.Named "field not found"%go []
  | go.FieldDecl f' t :: fds
  | go.EmbeddedField f' t :: fds =>
      if (ByteString.eqb f f') then t
      else struct_field_type f fds
  end.

Class IntoValUnfold V f :=
  {
    into_val_unfold : @into_val _ _ V = f;
  }.
Global Hint Mode IntoValUnfold ! - : typeclass_instances.
Global Arguments into_val_unfold (V) {_}.

Class GoZeroValEq t V `{!ZeroVal V} `{!GoSemanticsFunctions} :=
  {
    go_zero_val_eq : go_zero_val t = #(zero_val V);
  }.
Global Hint Mode GoZeroValEq ! - - - : typeclass_instances.
Global Arguments go_zero_val_eq (t) V {_ _ _}.

Class BasicIntoValInj :=
  {
    #[global] into_val_loc_inj :: Inj eq eq (into_val (V:=loc));
    #[global] into_val_slice_inj :: Inj eq eq (into_val (V:=slice.t));
    #[global] into_val_w64_inj :: Inj eq eq (into_val (V:=w64));
    #[global] into_val_w32_inj :: Inj eq eq (into_val (V:=w32));
    #[global] into_val_w16_inj :: Inj eq eq (into_val (V:=w16));
    #[global] into_val_w8_inj :: Inj eq eq (into_val (V:=w8));
    #[global] into_val_bool_inj :: Inj eq eq (into_val (V:=bool));
    #[global] into_val_string_inj :: Inj eq eq (into_val (V:=go_string));
    #[global] interface_into_val_inj :: Inj eq eq (into_val (V:=interface.t));
  }.

(** [go.CoreSemantics] defines the basics of when a GoContext is valid,
    excluding predeclared types (including primitives), arrays, slice, map, and
    channels, each of which is in their own file.

    The rules prefixed with [_] should not be used in any program proofs. *)
Class CoreSemantics :=
{
  (* FIXME: maybe don't put GoSemanticsFunctions in here? *)
  #[global] core_semantics_data :: GoSemanticsFunctions;
  #[global] basic_into_val_inj :: BasicIntoValInj;

  #[global] go_op_step o t args :: IsGoStepPureDet (GoOp o t) args (go_op o t args);
  #[global] go_alloc_step t args :: IsGoStepPureDet (GoAlloc t) args (alloc t args);
  #[global] go_load_step t (l : loc) :: IsGoStepPureDet (GoLoad t) #l (load t #l);
  #[global] go_store_step t (l : loc) v :: IsGoStepPureDet (GoStore t) (#l, v)%V (store t #l v);
  #[global] go_func_resolve_step n ts :: IsGoStepPureDet (FuncResolve n ts) #() #(functions n ts);
  #[global] go_method_resolve_step m t :: IsGoStepPureDet (MethodResolve t m) #() #(methods t m);
  #[global] go_global_var_addr_step v :: IsGoStepPureDet (GlobalVarAddr v) #() #(global_addr v);
  #[global] struct_field_ref_step t f l :: IsGoStepPureDet (StructFieldRef t f) #l #(struct_field_ref t f l);
  #[global] go_interface_make_step t v :: IsGoStepPureDet (InterfaceMake t) v #(interface.mk t v);
  #[global] composite_literal_step t (v : val) :: IsGoStepPureDet (CompositeLiteral t) v (composite_literal t v);
  go_prealloc_step : is_go_step_pure GoPrealloc #() = (λ e, ∃ (l : loc), e = #l);
  angelic_exit_step : is_go_step_pure AngelicExit #() = (λ e, e = AngelicExit #());

  #[global] into_val_unfold_func ::
    IntoValUnfold func.t (λ f, (rec: f.(func.f) f.(func.x) := f.(func.e))%V);
  #[global] into_val_unfold_bool :: IntoValUnfold _ (λ x, LitV $ LitBool x);

  (* TODO: get rid of these. *)
  #[global] into_val_unfold_w64 :: IntoValUnfold _ (λ x, LitV $ LitInt x);
  #[global] into_val_unfold_w32 :: IntoValUnfold _ (λ x, LitV $ LitInt32 x);
  #[global] into_val_unfold_w16 :: IntoValUnfold _ (λ x, LitV $ LitInt16 x);
  #[global] into_val_unfold_w8 :: IntoValUnfold _ (λ x, LitV $ LitByte x);
  #[global] into_val_unfold_string :: IntoValUnfold _ (λ x, LitV $ LitString x);
  #[global] into_val_unfold_loc :: IntoValUnfold _ (λ x, LitV $ LitLoc x);
  #[global] into_val_unfold_unit :: IntoValUnfold unit (λ _, LitV LitUnit);

  go_zero_val_underlying t : go_zero_val t = go_zero_val (to_underlying t);
  #[global] go_zero_val_eq_pointer t :: GoZeroValEq (go.PointerType t) loc;
  #[global] go_zero_val_eq_function sig :: GoZeroValEq (go.FunctionType sig) func.t;
  #[global] go_zero_val_eq_slice elem_type :: GoZeroValEq (go.SliceType elem_type) slice.t;
  #[global] go_zero_val_eq_channel dir elem_type :: GoZeroValEq (go.ChannelType dir elem_type) chan.t;

  #[global] core_comparison_sem :: CoreComparisonSemantics;

  alloc_underlying t : alloc t = alloc (to_underlying t);
  alloc_primitive t v (H : is_primitive_zero_val t v) : alloc t = (λ: <>, ref_one v)%V;
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

  #[global] index_ref_step t (j : w64) (v : val) ::
    IsGoStepPureDet (IndexRef t) (v, #j)%V (index_ref t (sint.Z j) v);

  #[global] index_step t (j : w64) (v : val) ::
    IsGoStepPureDet (Index t) (v, #j)%V (index t (sint.Z j) v);

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
    end;

  to_underlying_not_named t :
    to_underlying t = match t with | go.Named _ _ => to_underlying t | _ => t end;
}.

End defs.
End go.

Notation "@! func" :=
  #(functions func []) (at level 1, no associativity, format "@! func") : expr_scope.

Notation "![ t ] e" := (GoInstruction (GoLoad t) e%E)
                         (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Notation "e1 <-[ t ] e2" := (GoInstruction (GoStore t) (Pair e1%E e2%E))
                             (at level 80, format "e1  <-[ t ]  e2") : expr_scope.
