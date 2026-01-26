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

Class FloatOps :=
  {
    float64_neg : w64 → w64;
    float64_add : w64 → w64 → w64;
    float64_sub : w64 → w64 → w64;
    float64_mul : w64 → w64 → w64;
    float64_div : w64 → w64 → w64;
    float64_leb : w64 → w64 → bool;

    float32_neg : w32 → w32;
    float32_add : w32 → w32 → w32;
    float32_sub : w32 → w32 → w32;
    float32_mul : w32 → w32 → w32;
    float32_div : w32 → w32 → w32;
    float32_leb : w32 → w32 → bool;

    float64_to_float32 : w64 → w32;
  }.
Class GoSemanticsFunctions {ext : ffi_syntax} :=
  {
    underlying : go.type → go.type;
    global_addr : go_string → loc;
    functions : go_string → list go.type → func.t;
    methods : go.type → go_string → val → func.t;

    method_set : go.type → gmap go_string go.signature;

    (* This uses a Gallina [Type] because there are multiple [go.type]s that
       have the same [Type] representation (e.g. uint64/int64, *X/*Y), but
       offsets are only supposed to depend on the Gallina representation. *)
    is_type_repr : go.type → Type → Prop;
    struct_field_ref : Type → go_string → loc → loc;

    array_index_ref (elem_type : Type) (i : Z) (l : loc) : loc;

    map_empty : val → val;
    map_lookup : val → val → bool * val;
    map_insert : val → val → val → val;
    map_delete : val → val → val;
    is_map_domain : val → list val → Prop;

    is_map_pure (v : val) (m : val → bool * val) : Prop;
    map_default : val → val;
    #[global] float_ops :: FloatOps;
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

(* Typeclasses to help semantics for underlying-respecting Go semantics. Automation will
   try to apply the explicit instance (e.g., [is_convert_step]), which first
   requires using typeclass search to determine the underlying type(s) (e.g., [t_under]),
   and lastly requires looking for an instance of the typeclass (e.g.,
   [IsConvert go.int go.uint]). *)
Class IsConvert from_under to_under (v v' : val) `{!GoSemanticsFunctions} : Prop :=
{ is_convert_step_def `{!from ↓u from_under} `{!to ↓u to_under} :
  IsGoStepPureDet (Convert from to) v v' }.
Global Hint Mode IsConvert + + + - - : typeclass_instances.
Global Instance is_convert_step from to v from_under to_under v' `{!GoSemanticsFunctions} :
  from ↓u from_under → to ↓u to_under → IsConvert from_under to_under v v' →
  IsGoStepPureDet (Convert from to) v v'.
Proof. intros. apply is_convert_step_def. Qed.

Class IsGoOp (o : go_operator) (t_under : go.type) v1 v2 e' `{!GoSemanticsFunctions} : Prop :=
  { is_go_op_step_def `{!t ↓u t_under} : IsGoStepPureDet (GoOp o t) (v1, v2)%V e' }.
Global Hint Mode IsGoOp + + + + - - : typeclass_instances.
Global Instance is_go_op_step o t t_under v1 v2 e' `{!GoSemanticsFunctions} :
  t ↓u t_under → IsGoOp o t_under v1 v2 e' →
  IsGoStepPureDet (GoOp o t) (v1, v2)%V e'.
Proof. intros. apply is_go_op_step_def. Qed.

Class IsCompositeLiteral (t_under : go.type) v e' `{!GoSemanticsFunctions} : Prop :=
  { is_composite_literal_step_def `{!t ↓u t_under} : IsGoStepPureDet (CompositeLiteral t) v (e' t) }.
Global Hint Mode IsCompositeLiteral + + - - : typeclass_instances.
Global Instance is_composite_literal_step t t_under v e' `{!GoSemanticsFunctions} :
  t ↓u t_under → IsCompositeLiteral t_under v e' →
  IsGoStepPureDet (CompositeLiteral t) v (e' t).
Proof. intros. apply is_composite_literal_step_def. Qed.

Class IsComparable (t_under : go.type) `{!GoSemanticsFunctions} : Prop :=
  { is_comparable_check_step_def `{!t ↓u t_under} :: IsGoStepPureDet (CheckComparable t) #() #() }.
Global Hint Mode IsComparable + - : typeclass_instances.
Global Instance is_comparable_step t t_under `{!GoSemanticsFunctions} :
  t ↓u t_under → IsComparable t_under →
  IsGoStepPureDet (CheckComparable t) #() #().
Proof. intros. apply is_comparable_check_step_def. Qed.

(* Helper definition to cover types for which `a == b` always executes safely. *)
Class IsStrictlyComparable t V `{!EqDecision V} `{!GoSemanticsFunctions} : Prop :=
  {
    #[global] is_strictly_comparable ::
      ∀ (v1 v2 : V), IsGoOp GoEquals t #v1 #v2 #(bool_decide (v1 = v2));
  }.

Class CoreComparisonSemantics `{!GoSemanticsFunctions} : Prop :=
{
  #[global] primitive_is_comparable t (H : is_primitive t) :: IsComparable t;

  (* special case equality for functions *)
  #[global] is_go_op_go_equals_func_nil_l sig f ::
    IsGoOp GoEquals (go.FunctionType sig) #f #func.nil #(bool_decide (f = func.nil));
  #[global] is_go_op_go_equals_func_nil_r sig f ::
    IsGoOp GoEquals (go.FunctionType sig) #func.nil #f #(bool_decide (f = func.nil));

  #[global] pointer_is_comparable t :: IsComparable (go.PointerType t);
  #[global] go_eq_pointer t :: IsStrictlyComparable (go.PointerType t) loc;
  #[global] channel_is_comparable dir t :: IsComparable (go.ChannelType dir t);
  #[global] go_eq_channel t dir :: IsStrictlyComparable (go.ChannelType t dir) loc;

  #[global] struct_is_comparable fds
    `{!TCForall (λ fd, IsComparable (match fd with go.FieldDecl _ t | go.EmbeddedField _ t => t end)) fds} ::
    IsComparable (go.StructType fds);
  #[global] go_eq_struct fds v1 v2 ::
    IsGoOp GoEquals (go.StructType fds) v1 v2
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

Class TypeRepr t V `{!ZeroVal V} `{!GoSemanticsFunctions} : Prop :=
  {
    type_repr : is_type_repr t V;
    #[global] go_zero_val_step :: IsGoStepPureDet (GoZeroVal t) #() #(zero_val V);
  }.
Global Hint Mode TypeRepr ! - - - : typeclass_instances.

End defs.

Global Notation "s  ≤u  t" := (go.UnderlyingEq s t) (at level 70).
Global Notation "s  <u  t" := (go.UnderlyingDirectedEq s t) (at level 70).
Global Notation "t  ↓u  tunder" := (go.IsUnderlying t tunder) (at level 70).

Module mem.
Section defs.
Context {ext : ffi_syntax} {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.
Class MemSemantics `{!GoSemanticsFunctions} : Prop :=
{
  #[export] alloc_primitive `[!t ↓u tunder] v (H : is_primitive tunder) ::
    IsGoStepPureDet (GoAlloc t) v (ref_one v)%E;
  #[export] alloc_struct `[!t ↓u go.StructType fds] v ::
    IsGoStepPureDet (GoAlloc t) v
      (let: "l" := GoPrealloc #() in
       foldr (λ fd alloc_rest,
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef t field_name "l" in
                let: "l_field" := GoAlloc field_type (StructFieldGet t field_name v) in
                (if: ("l_field" ≠⟨go.PointerType field_type⟩ field_addr) then AngelicExit #()
                 else #());;
                alloc_rest
         ) #() fds ;;
       "l")%E;

  #[export] load_primitive `[!t ↓u tunder] (H : is_primitive tunder) l ::
    IsGoStepPureDet (GoLoad t) l (Read l)%E;

  #[export] load_struct `[!t ↓u go.StructType fds] l ::
    IsGoStepPureDet (GoLoad t) l
      (foldl (λ struct_so_far fd,
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef t field_name l in
                let field_val := GoLoad field_type field_addr in
                StructFieldSet t field_name (struct_so_far, field_val)
         )%E (GoZeroVal t #()) fds)%V;

  #[export] store_primitive `[!t ↓u tunder] (H : is_primitive t) l v ::
    IsGoStepPureDet (GoStore t) (l, v)%V (l <- v)%E;
  store_struct `[!t ↓u go.StructType fds] l v :
    IsGoStepPureDet (GoStore t) (l, v)
      (foldl (λ store_so_far fd,
                store_so_far;;
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => pair n t
                                                | go.EmbeddedField n t => pair n t
                                                end in
                let field_addr := StructFieldRef t field_name l in
                let field_val := StructFieldGet t field_name v in
                GoStore field_type (field_addr, field_val)
         )%E (#()) fds)%V;

}.
End defs.
End mem.

Section defs.
Context {ext : ffi_syntax} {go_lctx : GoLocalContext} {go_gctx : GoGlobalContext}.
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
    #[global] into_val_inj_proph_id :: IntoValInj proph_id;
  }.
(** [go.CoreSemantics] defines the basics of when a GoContext is valid,
    excluding predeclared types (including primitives), arrays, slice, map, and
    channels, each of which is in their own file. *)
Class CoreSemantics `{!GoSemanticsFunctions} : Prop :=
{
  #[global] basic_into_val_inj :: BasicIntoValInj;

  #[global] underlying_not_named `{!NotNamed t} :: t ↓u t;

  #[global] go_func_resolve_step n ts :: IsGoStepPureDet (FuncResolve n ts) #() #(functions n ts);
  #[global] go_method_resolve_step m t rcvr `{!t ↓u tunder} `{!NotInterface tunder} ::
    IsGoStepPureDet (MethodResolve t m) rcvr #(methods t m rcvr);
  #[global] go_global_var_addr_step v :: IsGoStepPureDet (GlobalVarAddr v) #() #(global_addr v);

  (* FIXME: unsound semantics: simply computing the struct field address will
     panic if the base address is nil. This is a bit of a headache because every
     program step executing [StructFieldRef] will need to have a precondition
     that [l ≠ null]. *)
  #[global] struct_field_ref_step t f l V `{!ZeroVal V} `{!TypeRepr t V} ::
    IsGoStepPureDet (StructFieldRef t f) #l #(struct_field_ref V f l);

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

  #[global] type_repr_pointer t :: TypeRepr (go.PointerType t) loc;
  #[global] type_repr_function sig :: TypeRepr (go.FunctionType sig) func.t;
  #[global] type_repr_slice elem_type :: TypeRepr (go.SliceType elem_type) slice.t;
  #[global] type_repr_interface elems :: TypeRepr (go.InterfaceType elems) interface.t;
  #[global] type_repr_channel dir elem_type :: TypeRepr (go.ChannelType dir elem_type) chan.t;
  #[global] type_repr_map key_type elem_type :: TypeRepr (go.MapType key_type elem_type) map.t;

  #[global] core_comparison_sem :: CoreComparisonSemantics;
  #[global] core_mem_sem :: mem.MemSemantics;

  #[global] composite_literal_pointer elem_type l ::
    IsCompositeLiteral (go.PointerType elem_type) l
    (λ _, GoAlloc elem_type (CompositeLiteral elem_type l));

  #[global] composite_literal_struct l fds ::
    IsCompositeLiteral (go.StructType fds) (LiteralValueV l)
    (λ t, match l with
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

  #[global] is_convert_underlying_same t v :: IsConvert t t v v;
  #[global] convert_same t v :: IsGoStepPureDet (Convert t t) v v;
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
