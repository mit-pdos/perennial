From Perennial.goose_lang Require Import lifting.
From New.golang Require defn.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import mem exception list typing.
From Perennial.Helpers Require Import NamedProps.
From RecordUpdate Require Export RecordUpdate.
From Perennial Require Import base.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Module struct.
Section goose_lang.
Context `{ffi_syntax}.

Implicit Types (d : struct.descriptor).
Infix "=?" := (ByteString.eqb).

(* FIXME: what does _f mean? Want better name. *)
Definition field_get_f t f0: val -> val :=
  match t with
  | structT d =>
      (fix go d v :=
         match d with
         | [] => #()
         | (f,_)::fs =>
             match v with
             | PairV v1 v2 => if f =? f0 then v1 else go fs v2
             | _ => #()
             end
         end) d
  | _ => λ v, LitV LitPoison
  end.

Definition field_set_f t f0 fv: val -> val :=
  match t with
  | structT d =>
      (fix go d v :=
         match d with
         | [] => v
         | (f,_)::fs =>
             match v with
             | PairV v1 v2 =>
                 if f =? f0
                 then PairV fv v2
                 else PairV v1 (go d v2)
             | _ => v
             end
         end) d
  | _ => λ v, LitV LitPoison
  end
  .

Definition field_ref_f_def t f0 l: loc := l +ₗ (struct.field_offset t f0).1.
Program Definition field_ref_f := sealed @field_ref_f_def.
Definition field_ref_f_unseal : field_ref_f = _ := seal_eq _.

Class Wf (t : go_type) : Set :=
  {
    descriptor_NoDup: match t with
    | structT d => NoDup d.*1
    | _ => False
    end
  }.

End goose_lang.
End struct.

Notation "l ↦s[ t :: f ] dq v" := (struct.field_ref_f t f l ↦{dq} v)%I
  (at level 50, dq custom dfrac at level 70, t at level 59, f at level 59,
     format "l  ↦s[ t  ::  f ] dq  v").

Definition option_descriptor_wf (d : struct.descriptor) : option (struct.Wf (structT d)).
  destruct (decide (NoDup d.*1)); [ apply Some | apply None ].
  constructor; auto.
Defined.

Definition proj_descriptor_wf (d : struct.descriptor) :=
  match option_descriptor_wf d as mwf return match mwf with
                                             | Some _ => struct.Wf (structT d)
                                             | None => True
                                             end  with
  | Some pf => pf
  | None => I
  end.

(* This hint converts [someStructType] into [structT blah] *)
Global Hint Extern 10 (struct.Wf ?t) =>
         progress (let t' := (eval hnf in t) in
                   change t with t') : typeclass_instances.
Global Hint Extern 10 (struct.Wf ?t) => unfold t : typeclass_instances.
Global Hint Extern 3 (struct.Wf (structT ?d)) => exact (proj_descriptor_wf d) : typeclass_instances.

Section lemmas.
Context `{heapGS Σ}.

Class IntoValStructField (f : go_string) (t : go_type) {V Vf : Type} {tf}
  (field_proj : V → Vf)
  `{!IntoVal V} `{!IntoVal Vf}
  `{!IntoValTyped Vf tf}
  :=
  {
    field_proj_eq_field_get : ∀ v, #(field_proj v) = (struct.field_get_f t f #v);
  }.

Definition struct_fields `{!IntoVal V} `{!IntoValTyped V t} l dq
  (fs : struct.descriptor) (v : V) : iProp Σ :=
  [∗ list] '(f, _) ∈ fs,
    ∀ `(H:IntoValStructField f t V Vf tf field_proj), ("H" +:+
                                                         (String.string_of_list_byte $
                                                            w8_to_byte <$> f)) ∷ l ↦s[t :: f]{dq} (field_proj v).

Lemma struct_val_inj d fvs1 fvs2 :
  struct.val_aux (structT d) fvs1 = struct.val_aux (structT d) fvs2 →
  ∀ f, In f d.*1 →
       match (alist_lookup_f f fvs1), (alist_lookup_f f fvs2) with
       | Some v1, Some v2 => v1 = v2
       | _, _ => True
       end.
Proof.
  rewrite struct.val_aux_unseal.
  induction d as [|[]].
  { done. }
  intros Heq ? [].
  - subst. simpl in Heq.
    injection Heq as ??.
    repeat destruct alist_lookup_f; naive_solver.
  - simpl in *. injection Heq as ??. by apply IHd.
Qed.

Class StructFieldsSplit `{!IntoVal V} `{!IntoValTyped V t} {dwf : struct.Wf t}
                        (dq : dfrac) (l : loc) (v : V) (Psplit : iProp Σ)
  :=
  {
    struct_fields_split : l ↦{dq} v ⊢ Psplit ;
    struct_fields_combine : Psplit ⊢ l ↦{dq} v
  }.

Lemma flatten_struct_tt : flatten_struct #() = [].
Proof. rewrite to_val_unseal //. Qed.

Lemma struct_fields_split_intro `{!IntoVal V} `{!IntoValTyped V t} {dwf: struct.Wf t}
  (dq: dfrac) (l: loc) (v: V) Psplit :
  (l ↦{dq} v ⊣⊢ Psplit) → StructFieldsSplit dq l v Psplit.
Proof.
  intros Heq.
  constructor; rewrite Heq //.
Qed.

(* A specialized version of [big_sepL_app] that simplifies some loc_add-related
expressions. Not strictly about heap_pointsto, but specialized with a dfrac so
higher-order unification works properly. *)
Lemma heap_pointsto_app (vs1 vs2: list val) (l: loc) dq (f: loc → dfrac → val → iProp Σ) :
  ([∗ list] j↦vj ∈ (vs1 ++ vs2), f (l +ₗ j) dq vj) ⊣⊢
  ([∗ list] j↦vj ∈ vs1, f (l +ₗ j) dq vj) ∗
  ([∗ list] j↦vj ∈ vs2, f (l +ₗ (Z.of_nat (length vs1)) +ₗ Z.of_nat j) dq vj).
Proof.
  rewrite big_sepL_app.
  f_equiv.
  setoid_rewrite Nat2Z.inj_add.
  setoid_rewrite loc_add_assoc.
  reflexivity.
Qed.

Theorem struct_fields_acc_update f t V Vf
  l dq {dwf : struct.Wf t} (v : V)
  `{IntoValStructField f t V Vf tf field_proj} `{!SetterWf field_proj} :
  typed_pointsto l dq v -∗
  l ↦s[t :: f]{dq} (field_proj v) ∗
  (∀ fv', l ↦s[t :: f]{dq} fv' -∗
          typed_pointsto l dq (set field_proj (λ _, fv') v)).
Proof.
Admitted.

Theorem struct_fields_acc f t V Vf
  l dq {dwf : struct.Wf t} (v : V)
  `{IntoValStructField f t V Vf tf field_proj} `{!SetterWf field_proj} :
  typed_pointsto l dq v -∗
  l ↦s[t :: f]{dq} (field_proj v) ∗
  (l ↦s[t :: f]{dq} (field_proj v) -∗ typed_pointsto l dq v).
Proof.
  iIntros "Hl".
  iDestruct (struct_fields_acc_update with "[$]") as "[$ H]".
  iIntros "* Hl".
  iSpecialize ("H" with "[$]").
  erewrite set_eq.
  2:{ done. } iFrame.
Qed.

End lemmas.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance pure_struct_field_ref_wp t f (l : loc) :
  PureWp True (struct.field_ref t f #l) #(struct.field_ref_f t f l).
Proof.
  iIntros (?????) "HΦ".
  wp_call_lc "?".
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ". rewrite struct.field_ref_f_unseal /struct.field_ref_f_def.
  repeat (f_equal; try word).
Qed.

Definition is_structT (t : go_type) : Prop :=
  match t with
  | structT d => True
  | _ => False
  end.

Definition wp_struct_make (t : go_type) (l : list (go_string*val)) :
  is_structT t →
  PureWp True
  (struct.make t (alist_val l))
  (struct.val_aux t l).
Proof.
  intros ?.
  pure_wp_start.
  rewrite struct.make_unseal struct.val_aux_unseal.
  destruct t; try by exfalso.
  unfold struct.make_def.
  iInduction decls as [] "IH" forall (Φ).
  - wp_pure_lc "?". wp_pures. by iApply "HΦ".
  - destruct a.
    wp_pure_lc "?". wp_pures.
    unfold struct.val_aux_def.
    destruct (alist_lookup_f _ _); wp_pures.
    + unshelve wp_apply "IH"; first done.
      iIntros "_". wp_pures. by iApply "HΦ".
    + unshelve wp_apply "IH"; first done.
      iIntros "_".
      simpl fill. wp_pures. by iApply "HΦ".
Qed.

Lemma struct_val_aux_nil fvs :
  (struct.val_aux (structT $ []) fvs) = #().
Proof. rewrite struct.val_aux_unseal //=. Qed.

Lemma struct_val_aux_cons decls f t fvs :
  (struct.val_aux (structT $ (f,t) :: decls) fvs) =
  (default (zero_val t) (alist_lookup_f f fvs), (struct.val_aux (structT decls) fvs))%V.
Proof. rewrite struct.val_aux_unseal //=. Qed.

Global Instance points_to_access_struct_field_ref {V Vf} l f v (proj : V → Vf) dq {t tf : go_type}
  `{!IntoVal V} `{!IntoValTyped V t}
  `{!IntoVal Vf} `{!IntoValTyped Vf tf}
  `{!IntoValStructField f t proj} `{!SetterWf proj}
  `{!struct.Wf t}
  : PointsToAccess (struct.field_ref_f t f l) (proj v)
                   dq
                   (l ↦{dq} v)%I
                   (λ vf', l ↦{dq} (set proj (λ _, vf') v))%I.
Proof.
  constructor.
  - intros. by iApply struct_fields_acc_update.
  - by rewrite RecordSet.set_eq.
Qed.
End wps.

(* Specialized simplification for the tactics below. Normally these tactics
solve the goal and this isn't necessary, but debugging is way easier if they
fail with the goal in a readable state. *)
Ltac cbn_w8 :=
  with_strategy transparent [w8_word_instance]
    (with_strategy opaque [loc_add] cbn).

(* TODO: maybe should re-implement this in a more principled way *)
Ltac _solve_has_go_type_step :=
  match goal with
  | |- has_go_type (zero_val _) _ => apply zero_val_has_go_type
  | |- has_go_type _ _ => solve [ apply to_val_has_go_type ]
  | |- has_go_type _ _ => try assumption; constructor
  | |- ∀ _, _ => intros
  | H: In _ _ |- _ => destruct H
  | H: (@eq (go_string * go_type) (_, _) _) |- _ =>
      (* replaces solve_has_go_type_step's use of inversion_clear with the more
      powerful inversion; subst; clear pattern *)
      inversion H; subst; clear H
  | _ => contradiction
  | _ => progress cbn_w8
  end.

(* extend typing's solve_has_go_type to general goals *)
Ltac solve_has_go_type' :=
  repeat _solve_has_go_type_step.

(* solve ∀ v, has_go_type (#v) t in IntoValTyped *)
Ltac solve_to_val_type :=
  lazymatch goal with
  | |- forall (_: ffi_syntax), _ => let H := fresh "H" in intros H
  | _ => idtac
  end;
  intros v;
  rewrite to_val_unseal /=;
  destruct v; cbn_w8;
  solve_has_go_type'.

(* solve #default_val = zero_val t in IntoValTyped *)
Ltac solve_zero_val :=
  intros;
  (* unfold and simpify, resulting in goal like
   [struct.val_aux t [a:=#(default_val A); ...; y:=#(default_val Y)] = struct.val_aux t []]. *)
  rewrite zero_val_eq to_val_unseal; with_strategy opaque [default_val] cbn;
  (* replace the [default_val] field values with [zero_val], then unfold
   [struct.val_aux], at which point there should be values with no [to_val] at
   all, which are definitionally equal. *)
  rewrite ?default_val_eq_zero_val ?struct.val_aux_unseal //.

Ltac solve_to_val_inj :=
  (* prove Inj (=) (=) (λ v, #v) *)
  intros;
  intros [] [];
  rewrite to_val_unseal /= ?struct.val_aux_unseal /=;
    cbn_w8;
  inv 1;
  try reflexivity.

Ltac solve_into_val_struct_field :=
  (* prove IntoValStructField *)
  constructor; intros v;
  lazymatch goal with
  | |- _ = ?rhs =>
      rewrite [in rhs]to_val_unseal /= struct.val_aux_unseal /=
  end;
  destruct v; try reflexivity; cbn_w8.

Ltac solve_struct_make_pure_wp :=
  intros;
  (* BUG: ssreflect has rewrite [in v in PureWp _ _ v]to_val_unseal that would
  do this directly, but Coq incorrectly flags v as an unbound variable when
  trying to use it in an Ltac. *)
  lazymatch goal with
  | |- PureWp _ _ ?v =>
      rewrite [in v]to_val_unseal;
      apply wp_struct_make; cbn; auto
  end.

Lemma pointsto_loc_add_equiv `{ffi_syntax} `{!ffi_interp ffi} `{!heapGS Σ}
  l dq (off1 off2: Z) `{!IntoVal V} (v: V) :
  off1 = off2 →
  (l +ₗ off1) ↦{dq} v ⊣⊢ (l +ₗ off2) ↦{dq} v.
Proof. intros; subst; rewrite //. Qed.

Lemma pointsto_loc_add0_equiv `{ffi_syntax} `{!ffi_interp ffi} `{!heapGS Σ}
  l dq (off2: Z) `{!IntoVal V} (v: V) :
  0 = off2 →
  l ↦{dq} v ⊣⊢ (l +ₗ off2) ↦{dq} v.
Proof. intros; subst; rewrite loc_add_0 //. Qed.

Lemma has_bounded_type_size_def (t: go_type) `{BoundedTypeSize t} :
  go_type_size_def t < 2^32.
Proof.
  destruct H as [H].
  rewrite go_type_size_unseal in H.
  auto.
Qed.

Lemma has_bounded_type_size_intro {t} :
  match decide (Z.of_nat (go_type_size_def t) < 2^32) with
  | left _ => True
  | right _ => False
  end → BoundedTypeSize t.
Proof.
  destruct (decide _); intros; [ | contradiction ].
  constructor.
  rewrite go_type_size_unseal //.
Qed.

(* only works if type size can be computed *)
Ltac solve_bounded_type_size :=
  apply (has_bounded_type_size_intro);
  try exact I.

#[global] Hint Extern 10 (BoundedTypeSize _) => solve [ solve_bounded_type_size ] : typeclass_instances.

(* solves goals of the form l ↦{dq} v ⊣⊢ l' ↦{dq} v, where the locations involve
offset calculations. *)
Ltac solve_field_ref_f :=
  rewrite struct.field_ref_f_unseal /struct.field_ref_f_def;
  with_strategy transparent [w8_word_instance] (with_strategy opaque [loc_add] cbn);
  rewrite ?loc_add_assoc;
  lazymatch goal with
  | |- typed_pointsto (_ +ₗ _) _ _ ⊣⊢ _ => apply pointsto_loc_add_equiv
  | |- typed_pointsto _ _ _ ⊣⊢ _ => apply pointsto_loc_add0_equiv
  | _ => idtac
  end;
  rewrite ?go_type_size_unseal //=;
  repeat
    match goal with
    | |- context[go_type_size_def ?t] =>
        learn_hyp (has_bounded_type_size_def t)
    end;
  try word.

Lemma sep_equiv_split Σ (P1 P2 Q1 Q2: iProp Σ) :
  P1 ⊣⊢ Q1 →
  P2 ⊣⊢ Q2 →
  (P1 ∗ P2 ⊣⊢ Q1 ∗ Q2).
Proof.
  intros H1 H2. f_equiv; auto.
Qed.

(* To prove StructFieldsSplit we need to prove equivalence if a split based on
[flatten_struct] and one based on a field offset for each field.

This tactic converts one [length (flatten_struct x)] to [go_type_size t]. The
parameters give it the right value and go_type to relate.

*)
Ltac simpl_one_flatten_struct x go_t f :=
  rewrite (@has_go_type_len _ x (struct.field_offset go_t f).2); [ | by solve_has_go_type' ];
  (* this [solve_field_ref_f] should solve the subgoal, but it does not fail
  otherwise if there are bugs; it's nice for the tactic to leave the simplified
  state for debugging *)
  apply sep_equiv_split; [ solve_field_ref_f | ].

Ltac unfold_typed_pointsto :=
  rewrite typed_pointsto_unseal /typed_pointsto_def to_val_unseal /=
    struct.val_aux_unseal /=;
    with_strategy transparent [w8_word_instance]
    (with_strategy opaque [loc_add] cbn).

Ltac split_pointsto_app :=
  rewrite !heap_pointsto_app;
  rewrite ?flatten_struct_tt ?big_sepL_nil ?(right_id bi_emp).

(* use the above automation the way proofgen does (approximately, not kept in sync) *)
Module __struct_automation_test.

Import New.golang.defn.

(* TEST *)
Module time.

Definition Time : go_type := structT [
  "wall" :: uint64T;
  "ext" :: int64T;
  "loc" :: ptrT
]%struct.

Module Time.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  wall' : w64;
  ext' : w64;
  loc' : loc;
}.
End def.
End Time.

Section instances.

Global Instance settable_Time `{ffi_syntax} : Settable _ :=
  settable! Time.mk < Time.wall'; Time.ext'; Time.loc' >.
Global Instance into_val_Time `{ffi_syntax} : IntoVal Time.t :=
  {| to_val_def v := struct.val_aux time.Time
                       ["wall" ::= #(Time.wall' v);
                        "ext" ::= #(Time.ext' v);
                        "loc" ::= #(Time.loc' v)
                       ]%struct |}.

Global Program Instance into_val_typed_Time `{ffi_syntax} : IntoValTyped Time.t time.Time :=
{|
  default_val := Time.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_Time_wall `{ffi_syntax} : IntoValStructField "wall" time.Time Time.wall'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Time_ext `{ffi_syntax} : IntoValStructField "ext" time.Time Time.ext'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_Time_loc `{ffi_syntax} : IntoValStructField "loc" time.Time Time.loc'.
Proof. solve_into_val_struct_field. Qed.

Context `{!ffi_syntax} `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Time wall' ext' loc':
  PureWp True
    (struct.make time.Time (alist_val [
      "wall" ::= #wall';
      "ext" ::= #ext';
      "loc" ::= #loc'
    ]))%struct
    #(Time.mk wall' ext' loc').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance Time_struct_fields_split dq l (v : Time.t) :
  StructFieldsSplit dq l v (
    "Hwall" ∷ l ↦s[time.Time :: "wall"]{dq} v.(Time.wall') ∗
    "Hext" ∷ l ↦s[time.Time :: "ext"]{dq} v.(Time.ext') ∗
    "Hloc" ∷ l ↦s[time.Time :: "loc"]{dq} v.(Time.loc')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.

  simpl_one_flatten_struct (#(Time.wall' v)) time.Time "wall"%go.
  simpl_one_flatten_struct (#(Time.ext' v)) time.Time "ext"%go.

  solve_field_ref_f.
Qed.

End instances.
End time.

(* TEST *)
Module empty_struct.
Definition empty_struct : go_type := structT [].

Module unit.
Section def.
Context `{ffi_syntax}.
Record t := mk {
}.
End def.
End unit.

Section instances.
Context `{ffi_syntax}.
Global Instance into_val_unit : IntoVal unit.t :=
  {| to_val_def v :=
    struct.val_aux empty_struct [
    ]%struct
  |}.

Global Program Instance into_val_typed_unit : IntoValTyped unit.t empty_struct :=
{|
  default_val := unit.mk;
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_unit:
  PureWp True
    (struct.make empty_struct (alist_val [
    ]))%struct
    #(unit.mk).
Proof. solve_struct_make_pure_wp. Qed.

End instances.

End empty_struct.

(* TEST *)
Module generic_struct.

Definition Box `{ffi_syntax} (T : go_type) : go_type := structT [
      "Value" :: T
  ]%struct.
Module Box.
Record t `{ffi_syntax} `{!IntoVal T'} `{!IntoValTyped T' T} := mk {
  Value' : T';
}.
End Box.
Arguments Box.mk {_} {T'} {_ T _}.
Arguments Box.t {_} T' {_ T _}.

Section instances.
Context `{ffi_syntax}.

Context `{!IntoVal T'} `{!IntoValTyped T' T}.

Global Instance Box_ty_wf : struct.Wf (Box T).
Proof. apply _. Qed.

Global Instance settable_Box : Settable (Box.t T') :=
  settable! (Box.mk (T:=T)) < Box.Value' >.
Global Instance into_val_Box : IntoVal (Box.t T') :=
  {| to_val_def v :=
    struct.val_aux (Box T) [
    "Value" ::= #(Box.Value' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_Box : IntoValTyped (Box.t T') (Box T) :=
{|
  default_val := Box.mk (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_Box_Value : IntoValStructField "Value" (Box T) Box.Value'.
Proof. solve_into_val_struct_field. Qed.

Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.

Global Instance wp_struct_make_Box Value':
  PureWp True
    (struct.make (Box T) (alist_val [
      "Value" ::= #Value'
    ]))%struct
    #(Box.mk Value').
Proof. solve_struct_make_pure_wp. Qed.

Global Instance Box_struct_fields_split dq l (v : Box.t T') :
  StructFieldsSplit dq l v (
    "HValue" ∷ l ↦s[Box T :: "Value"]{dq} v.(Box.Value')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.

  solve_field_ref_f.
Qed.

End instances.
End generic_struct.

End __struct_automation_test.

From New.golang.defn Require Import pkg.
Module __pkg_test.

Section defs.
Context `{!ffi_syntax}.
Definition test_pkg : go_string := "test_pkg".
Definition foo : go_string := "foo".
Definition bar : go_string := "bar".
Definition fooGeneric (T : go_string) : go_string := ("fooGeneric[" ++ T ++ "]")%go.

Definition fooⁱᵐᵖˡ : val := λ: <>, #"foo".
Definition barⁱᵐᵖˡ : val := λ: <>, #"bar".

(*
From Stdlib Require Import VectorDef.
Import VectorNotations.
Program Definition fooGenericⁱᵐᵖˡ (T : vec go_type 1) : val :=
  match T with
  | [T]%vector =>
      (λ: "b" "l" "r",
        let: "ret_ptr" := mem.alloc T #() in
        (if: "b" then "ret_ptr" <-[T] "l" else "ret_ptr" <-[T] "r");;
        ![T]"ret_ptr")%V
  | _ => _
  end.
(* Error: Anomaly "Instance and signature do not match." Please report at http://coq.inria.fr/bugs/. *) *)

Inductive func_id :=
| Basic : go_string → func_id
| Generic : go_string → func_id.

Definition fooGenericⁱᵐᵖˡ' (T : go_type) : val :=
  λ: "b" "l" "r",
    let: "ret_ptr" := mem.alloc T #() in
    (if: "b" then "ret_ptr" <-[T] "l" else "ret_ptr" <-[T] "r");;
    ![T]"ret_ptr".

Definition fooGenericⁱᵐᵖˡ (T : list go_type) : val :=
  match T with
  | [T] =>
      λ: "b" "l" "r",
        let: "ret_ptr" := mem.alloc T #() in
        (if: "b" then "ret_ptr" <-[T] "l" else "ret_ptr" <-[T] "r");;
        ![T]"ret_ptr"
  | _ => (LitV LitPoison)
  end.

Inductive func_id_expr :=
| FuncId : go_string → func_id_expr
| FuncIdGeneric : go_string → list go_string → func_id_expr.

(*
  alist is list (go_string * val)
  Here, want list (go_string * (A → val))
  func_id
*)

Definition functions' (func_name : go_string) (f : val) : Prop :=
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = bar ∧ f = barⁱᵐᵖˡ) ∨
  (func_name = foo ∧ f = fooⁱᵐᵖˡ) ∨
    False
.

Lemma x g :
  (∀ func_name f, functions' func_name f → g func_name = Some f) →
  g foo = Some fooⁱᵐᵖˡ.
Proof. unfold functions'. intros Hf. naive_solver.
Qed.
