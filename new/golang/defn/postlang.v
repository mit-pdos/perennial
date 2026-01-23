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

Global Notation "e1 ≤⟨ t ⟩ e2" := (GoInstruction (GoOp GoLe t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ≤⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 <⟨ t ⟩ e2" := (GoInstruction (GoOp GoLt t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  <⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 ≥⟨ t ⟩ e2" := (GoInstruction (GoOp GoGe t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ≥⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 >⟨ t ⟩ e2" := (GoInstruction (GoOp GoGt t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  >⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 =⟨ t ⟩ e2" := (GoInstruction (GoOp GoEquals t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  =⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 ≠⟨ t ⟩ e2" := (UnOp NegOp (e1%E =⟨t⟩ e2%E))
                             (at level 70, format "e1  ≠⟨ t ⟩  e2") : expr_scope.

Global Notation "e1 +⟨ t ⟩ e2" := (GoInstruction (GoOp GoPlus t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  +⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 -⟨ t ⟩ e2" := (GoInstruction (GoOp GoSub t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  -⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 *⟨ t ⟩ e2" := (GoInstruction (GoOp GoMul t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  *⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 /⟨ t ⟩ e2" := (GoInstruction (GoOp GoDiv t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  /⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 %⟨ t ⟩ e2" := (GoInstruction (GoOp GoRemainder t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  %⟨ t ⟩  e2") : expr_scope.

Global Notation "e1 &⟨ t ⟩ e2" := (GoInstruction (GoOp GoAnd t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  &⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 |⟨ t ⟩ e2" := (GoInstruction (GoOp GoOr t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  |⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 ^⟨ t ⟩ e2" := (GoInstruction (GoOp GoXor t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  ^⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 &^⟨ t ⟩ e2" := (GoInstruction (GoOp GoBitClear t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  &^⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 <<⟨ t ⟩ e2" := (GoInstruction (GoOp GoShiftl t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  <<⟨ t ⟩  e2") : expr_scope.
Global Notation "e1 >>⟨ t ⟩ e2" := (GoInstruction (GoOp GoShiftr t) (e1%E, e2%E)%E)
                             (at level 70, format "e1  >>⟨ t ⟩  e2") : expr_scope.

Global Notation "⟨ t ⟩- e" := (GoInstruction (GoUnOp GoNeg t) e%E)
                                (at level 70, format "⟨ t ⟩-  e") : expr_scope.

Global Notation "⟨ t ⟩! e" := (GoInstruction (GoUnOp GoNot t) e%E)
                                (at level 70, format "⟨ t ⟩!  e") : expr_scope.

Global Notation "⟨ t ⟩^ e" := (GoInstruction (GoUnOp GoComplement t) e%E)
                                (at level 70, format "⟨ t ⟩^  e") : expr_scope.

Module map.
Definition t := loc.
Definition nil : t := null.
End map.

Class GoSemanticsFunctions {ext : ffi_syntax} :=
  {
    underlying : go.type → go.type;
    global_addr : go_string → loc;
    functions : go_string → list go.type → func.t;
    methods : go.type → go_string → val → func.t;
    go_op : go_operator → go.type → val → expr;
    go_zero_val : go.type → val;

    (* Go equality function without special cases; e.g. any slice comparison will
       panic here. *)
    go_eq : go.type → val → val → expr;

    method_set : go.type → gmap go_string go.signature;

    alloc : go.type → val;
    load : go.type → val;
    store : go.type → val;

    (* This uses a Gallina [Type] because there are multiple [go.type]s that
       have the same [Type] representation (e.g. uint64/int64, *X/*Y), but
       offsets are only supposed to depend on the Gallina representation. *)
    is_type_repr : go.type → Type → Prop;
    struct_field_ref : Type → go_string → loc → loc;

    (* map index expressions have their own implementation that does not use the
       `Index` primitive. It's statically (even with type parameters) known
       whether an index expression is a map index expression or not a map index
       expression. https://go.dev/ref/spec#Index_expressions *)
    index (container_type : go.type) (i : Z) (v : val) : expr;
    index_ref (container_type : go.type) (i : Z) (v : val) : expr;
    array_index_ref (elem_type : Type) (i : Z) (l : loc) : loc;

    map_empty : val → val;
    map_lookup : val → val → bool * val;
    map_insert : val → val → val → val;
    map_delete : val → val → val;
    is_map_domain : val → list val → Prop;
    composite_literal : go.type → val → expr;

    is_map_pure (v : val) (m : val → bool * val) : Prop;
    map_default : val → val;
  }.

Global Notation "ptr .[ t , field ]" := (struct_field_ref t field ptr)
  (at level 1, format "ptr .[ t ,  field ]").

Section unfolding_defs.
Context {ext : ffi_syntax} `{!GoSemanticsFunctions} {go_gctx : GoGlobalContext}.

Class FuncUnfold f type_args f_impl : Prop :=
  {
    func_unfold : #(functions f type_args) = f_impl;
  }.
Global Hint Mode FuncUnfold ! ! - : typeclass_instances.

Class MethodUnfold t m (m_impl : val) : Prop :=
  {
    method_unfold : ∀ v, #(methods t m v) = (λ: "arg1", m_impl v "arg1")%V;
  }.
Global Hint Mode MethodUnfold ! ! - : typeclass_instances.
End unfolding_defs.

Module go.
Section defs.
Context {ext : ffi_syntax}.
Context {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.

Definition GlobalAlloc_def (v : go_string) (t : go.type) : val :=
  λ: <>,
    let: "l" := GoAlloc t (GoZeroVal t #()) in
    if: "l" ≠⟨go.PointerType t⟩ (GlobalVarAddr v #()) then
      AngelicExit #()
    else #().
Program Definition GlobalAlloc := sealed GlobalAlloc_def.
Definition GlobalAlloc_unseal : GlobalAlloc = _ := seal_eq _.

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

Global Instance interface_ok_eq_dec : EqDecision interface.t_ok.
Proof. solve_decision. Qed.

Global Instance interface_eq_dec : EqDecision interface.t.
Proof. solve_decision. Qed.

Global Instance array_eq_dec V n `{!EqDecision V} : EqDecision (array.t V n).
Proof. solve_decision. Qed.

Global Instance func_eq_dec : EqDecision func.t.
Proof. solve_decision. Qed.

Definition ref_one : val :=
  λ: "v", let: "l" := ref (LitV $ LitString "") in "l" <- "v";; "l".

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

Class UnderlyingEq s t `{!GoSemanticsFunctions} : Prop :=
  { underlying_eq : underlying s = underlying t }.
Global Hint Mode UnderlyingEq + - - : typeclass_instances.

(* This has a transitive instance, so only declare instances in a way that [t']
   is strictly "more underlying" than [t]. An instance with [t = t'] will cause
   an infinite loop in typeclass search because of transitivity. *)
Class UnderlyingDirectedEq t t' `{!GoSemanticsFunctions} : Prop :=
  { underlying_unfold : underlying t = underlying t' }.
Global Hint Mode UnderlyingDirectedEq + - - : typeclass_instances.

Class NotNamed (t : go.type) : Prop :=
  { not_named : match t with go.Named _ _ => False | _ => True end }.

Class NotInterface (t : go.type) : Prop :=
  { not_interface : match t with go.InterfaceType _ => False | _ => True end }.

Class IsUnderlying t tunder `{!GoSemanticsFunctions} : Prop :=
  { is_underlying : underlying t = tunder }.
Global Hint Mode IsUnderlying + - - : typeclass_instances.

Notation "s  ≤u  t" := (UnderlyingEq s t) (at level 70).
Notation "s  <u  t" := (UnderlyingDirectedEq s t) (at level 70).
Notation "t  ↓u  tunder" := (IsUnderlying t tunder) (at level 70).

Class ConvertUnderlying from_under to_under (v v' : val) `{!GoSemanticsFunctions} : Prop :=
{
  convert_underlying_def `{!from ↓u from_under} `{!to ↓u to_under} :
    GoExprEq (Convert from to v) v'
}.
Global Hint Mode ConvertUnderlying + + + - - : typeclass_instances.

Global Instance convert_underlying from to v from_under to_under v' `{!GoSemanticsFunctions} :
  from ↓u from_under → to ↓u to_under → ConvertUnderlying from_under to_under v v' →
  GoExprEq (Convert from to v) v'.
Proof. intros. apply convert_underlying_def. Qed.

Class CoreComparisonSemantics `{!GoSemanticsFunctions} : Prop :=
{
  #[global] go_op_underlying `{!t <u tunder} `{!GoExprEq (go_op o tunder args) e} ::
    GoExprEq (go_op o t args) e;
  #[global] go_eq_underlying `{!t <u tunder} `{!GoExprEq (go_eq tunder v1 v2) e} ::
    GoExprEq (go_eq t v1 v2) e;

  (* special case equality for functions *)
  #[global] is_go_op_go_equals_func_nil_l sig f ::
    IsGoOp GoEquals (go.FunctionType sig) (#f, #func.nil)%V #(bool_decide (f = func.nil));
  #[global] is_go_op_go_equals_func_nil_r sig f ::
    IsGoOp GoEquals (go.FunctionType sig) (#func.nil, #f)%V #(bool_decide (f = func.nil));

  #[global] is_comparable_underlying `{!t <u tunder} `{!IsComparable tunder} ::
    IsComparable t;
  #[global] is_comparable_pointer t :: IsComparable (go.PointerType t);
  #[global] go_eq_pointer t :: AlwaysSafelyComparable (go.PointerType t) loc;

  #[global] is_comparable_channel t dir :: IsComparable (go.ChannelType t dir);
  #[global] go_eq_channel t dir :: AlwaysSafelyComparable (go.ChannelType t dir) loc;

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

Class IntoValInj V :=
  {
    #[global] into_val_inj :: Inj eq eq (into_val (V:=V));
  }.
Global Hint Mode IntoValInj ! : typeclass_instances.

Class BasicIntoValInj :=
  {
    #[global] into_val_inj_loc :: IntoValInj loc;
    #[global] into_val_inj_slice :: IntoValInj slice.t;
    #[global] into_val_inj_w64 :: IntoValInj w64;
    #[global] into_val_inj_w32 :: IntoValInj w32;
    #[global] into_val_inj_w16 :: IntoValInj w16;
    #[global] into_val_inj_w8 :: IntoValInj w8;
    #[global] into_val_inj_bool :: IntoValInj bool;
    #[global] into_val_inj_string :: IntoValInj go_string;
    #[global] into_val_inj_interface :: IntoValInj interface.t;
  }.

Class TypeRepr t V `{!ZeroVal V} `{!GoSemanticsFunctions} : Prop :=
  {
    type_repr : is_type_repr t V;
    go_zero_val_eq : go_zero_val t = #(zero_val V);
    #[global] go_zero_val_step :: IsGoStepPureDet (GoZeroVal t) #() #(zero_val V);
  }.
Global Hint Mode TypeRepr ! - - - : typeclass_instances.

(** [go.CoreSemantics] defines the basics of when a GoContext is valid,
    excluding predeclared types (including primitives), arrays, slice, map, and
    channels, each of which is in their own file.

    The rules prefixed with [_] should not be used in any program proofs. *)
Class CoreSemantics `{!GoSemanticsFunctions} : Prop :=
{
  #[global] basic_into_val_inj :: BasicIntoValInj;

  #[global] underlying_not_named `{!NotNamed t} :: t ↓u t;

  #[global] go_op_step o t args :: IsGoStepPureDet (GoOp o t) args (go_op o t args);
  #[global] go_alloc_step t args :: IsGoStepPureDet (GoAlloc t) args (alloc t args);
  #[global] go_load_step t (l : loc) :: IsGoStepPureDet (GoLoad t) #l (load t #l);
  #[global] go_store_step t (l : loc) v :: IsGoStepPureDet (GoStore t) (#l, v)%V (store t #l v);
  #[global] go_func_resolve_step n ts :: IsGoStepPureDet (FuncResolve n ts) #() #(functions n ts);
  #[global] go_method_resolve_step m t rcvr `{!t ↓u tunder} `{!NotInterface tunder} ::
    IsGoStepPureDet (MethodResolve t m) rcvr #(methods t m rcvr);
  #[global] go_global_var_addr_step v :: IsGoStepPureDet (GlobalVarAddr v) #() #(global_addr v);

  (* FIXME: unsound semantics: simply computing the struct field address will
     panic if the base address is nil. This is a bit of a headache because every
     program step executing [StructFieldRef] will not have a precondition that
     [l ≠ null]. *)
  #[global] struct_field_ref_step t f l V `{!ZeroVal V} `{!TypeRepr t V} ::
    IsGoStepPureDet (StructFieldRef t f) #l #(struct_field_ref V f l);
  #[global] composite_literal_step t (v : val) :: IsGoStepPureDet (CompositeLiteral t) v (composite_literal t v);

  (* The language spec doesn't say anything about the addresses of zero-sized
     allocation. But, in the runtime, these addresses are non-nil, so the
     semantics assumes it here.
     https://cs.opensource.google/go/go/+/refs/tags/go1.25.5:src/runtime/malloc.go;l=927
     https://cs.opensource.google/go/go/+/refs/tags/go1.25.5:src/runtime/malloc.go;l=1023 *)
  go_prealloc_step : is_go_step_pure GoPrealloc #() = (λ e, ∃ (l : loc), l ≠ null ∧ e = #l);
  angelic_exit_step : is_go_step_pure AngelicExit #() = (λ e, e = AngelicExit #());

  #[global] into_val_unfold_func ::
    IntoValUnfold func.t (λ f, (rec: f.(func.f) f.(func.x) := f.(func.e))%V);
  #[global] into_val_unfold_bool :: IntoValUnfold _ (λ x, LitV $ LitBool x);

  (* Eventually want to get rid of these. *)
  #[global] into_val_unfold_w64 :: IntoValUnfold _ (λ x, LitV $ LitInt x);
  #[global] into_val_unfold_w32 :: IntoValUnfold _ (λ x, LitV $ LitInt32 x);
  #[global] into_val_unfold_w16 :: IntoValUnfold _ (λ x, LitV $ LitInt16 x);
  #[global] into_val_unfold_w8 :: IntoValUnfold _ (λ x, LitV $ LitByte x);
  #[global] into_val_unfold_string :: IntoValUnfold _ (λ x, LitV $ LitString x);
  #[global] into_val_unfold_loc :: IntoValUnfold _ (λ x, LitV $ LitLoc x);
  #[global] into_val_unfold_unit :: IntoValUnfold unit (λ _, LitV LitUnit);

  go_zero_val_underlying `{!t ≤u t'} : go_zero_val t = go_zero_val t';
  #[global] type_repr_pointer t :: TypeRepr (go.PointerType t) loc;
  #[global] type_repr_function sig :: TypeRepr (go.FunctionType sig) func.t;
  #[global] type_repr_slice elem_type :: TypeRepr (go.SliceType elem_type) slice.t;
  #[global] type_repr_interface elems :: TypeRepr (go.InterfaceType elems) interface.t;
  #[global] type_repr_channel dir elem_type :: TypeRepr (go.ChannelType dir elem_type) chan.t;
  #[global] type_repr_map key_type elem_type :: TypeRepr (go.MapType key_type elem_type) map.t;

  #[global] core_comparison_sem :: CoreComparisonSemantics;

  alloc_underlying `{!t ≤u tunder} : alloc t = alloc tunder;
  alloc_primitive t (H : is_primitive t) : alloc t = (λ: "v", ref_one "v")%V;
  alloc_struct `{!t ≤u go.StructType fds} :
    alloc t =
    (λ: "v",
        let: "l" := GoPrealloc #() in
        foldr (λ fd alloc_rest,
                 let (field_name, field_type) := match fd with
                                                 | go.FieldDecl n t => pair n t
                                                 | go.EmbeddedField n t => pair n t
                                                 end in
                 let field_addr := StructFieldRef t field_name "l" in
                 let: "l_field" := GoAlloc field_type (StructFieldGet t field_name "v") in
                 (if: ("l_field" ≠⟨go.PointerType field_type⟩ field_addr) then AngelicExit #()
                  else #());;
                 alloc_rest
          ) #() fds ;;
        "l")%V;

  load_underlying `{!t ≤u tunder} : load t = load tunder;
  load_primitive t (H : is_primitive t) : load t = (λ: "l", Read "l")%V;
  load_struct `{!t ≤u go.StructType fds} :
    load t =
    (λ: "l",
       foldl (λ struct_so_far fd,
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef t field_name "l" in
                let field_val := GoLoad field_type field_addr in
                StructFieldSet t field_name (struct_so_far, field_val)
         ) (GoZeroVal t #()) fds)%V;

  store_underlying `{!t ≤u tunder} : store t = store tunder;
  store_primitive t (H : is_primitive t) : store t = (λ: "l" "v", "l" <- "v")%V;
  store_struct `{!t ≤u go.StructType fds} :
    store t =
    (λ: "l" "v",
       foldl (λ store_so_far fd,
                store_so_far;;
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef t field_name "l" in
                let field_val := StructFieldGet t field_name "v" in
                GoStore field_type (field_addr, field_val)
         ) (#()) fds)%V;

  index_ref_underlying `{!t ≤u t'} : index_ref t = index_ref t';
  index_underlying `{!t ≤u t'} : index t = index t';

  #[global] index_ref_step t (j : w64) (v : val) ::
    IsGoStepPureDet (IndexRef t) (v, #j)%V (index_ref t (sint.Z j) v);

  #[global] index_step t (j : w64) (v : val) ::
    IsGoStepPureDet (Index t) (v, #j)%V (index t (sint.Z j) v);

  #[global] composite_literal_pointer elem_type l ::
    GoExprEq (composite_literal (go.PointerType elem_type) l)
    (GoAlloc elem_type (CompositeLiteral elem_type l));

  #[global] composite_literal_struct `{!t ≤u go.StructType fds} l ::
    GoExprEq (composite_literal t (LiteralValueV l))
    (match l with
     | [] => GoZeroVal t #()
     | KeyedElement None _ :: _ =>
         (* unkeyed struct literal *)
         foldl (λ v '(fd, ke),
                  let (field_name, field_type) :=
                    match fd with go.FieldDecl n t | go.EmbeddedField n t => (n, t) end in
                  match ke with
                  | KeyedElement None (ElementExpression from e) =>
                      StructFieldSet t field_name (v, Convert from field_type e)%E
                  | _ => Panic "invalid Go code"
                  end
           ) (GoZeroVal t #()) (zip fds l)
     | KeyedElement (Some _) _ :: _ =>
         (* keyed struct literal *)
         foldl (λ v ke,
                  match ke with
                  | KeyedElement (Some (KeyField field_name)) (ElementExpression from e) =>
                      StructFieldSet t field_name (v, Convert from (struct_field_type field_name fds) e)%E
                  | _ => Panic "invalid Go code"
                  end
           ) (GoZeroVal t #()) l
     end);

  #[global] convert_underlying_same t v :: ConvertUnderlying t t v v;
  #[global] convert_same t v :: GoExprEq (Convert t t v) v;
}.

End defs.
End go.

Global Notation "@! func" :=
  #(functions func []) (at level 1, no associativity, format "@! func") : expr_scope.

Global Notation "rcvr @! type @! method" :=
  (#(methods type method #rcvr))
    (at level 1, type at next level, no associativity) : expr_scope.

Global Notation "![ t ] e" := (GoInstruction (GoLoad t) e%E)
                                (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Global Notation "e1 <-[ t ] e2" := (GoInstruction (GoStore t) (Pair e1%E e2%E))
                                     (at level 80, format "e1  <-[ t ]  e2") : expr_scope.

Global Notation "s  ≤u  t" := (go.UnderlyingEq s t) (at level 70).
Global Notation "s  <u  t" := (go.UnderlyingDirectedEq s t) (at level 70).
Global Notation "t  ↓u  tunder" := (go.IsUnderlying t tunder) (at level 70).
