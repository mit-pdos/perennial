From Perennial.goose_lang Require Import lifting.
From New.golang Require defn.
From New.golang.defn Require Export struct.
From New.golang.theory Require Import typed_pointsto exception list typing dynamic_typing.
From Perennial.Helpers Require Import NamedProps.
From RecordUpdate Require Export RecordUpdate.
From Perennial Require Import base.

Set Default Proof Using "Type".

Module struct.
Section goose_lang.
Context `{ffi_syntax}.

Implicit Types (d : struct.descriptor).
Infix "=?" := (ByteString.eqb).

(* FIXME: what does _f mean? Want better name. *)
Definition field_offset_f (t : go_type) f : (w64 * go_type) :=
  let missing := W64 (2^64-1) in
  match t with
  | structT d =>
      (fix field_offset_struct (d : struct.descriptor) : (w64 * go_type) :=
         match d with
         | [] => (missing, badT)
         | (f',t)::fs => if f' =? f then (W64 0, t)
                         else match field_offset_struct fs with
                              | (off, t') => (word.add (go_type_size t) off, t')
                              end
         end) d
  | _ => (missing, badT)
  end .

Definition field_ty_f t f : go_type := (field_offset_f t f).2.

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

Definition field_ref_f_def t f0 l: loc := l +ₗ uint.Z (field_offset_f t f0).1.
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

#[global] Instance field_offset_into_val : IntoVal (w64 * go_type) :=
  { to_val_def := fun '(off, t) => (#off, #t)%V; }.

Lemma field_off_to_val_unfold (p: w64 * go_type) :
  #p = (#p.1, #p.2)%V.
Proof.
  destruct p.
  rewrite {1}to_val_unseal //=.
Qed.

Global Instance pure_struct_field_offset_wp (t: go_type) f :
  PureWp True (struct.field_offset #t #f) (#(struct.field_offset_f t f)).
Proof.
  apply pure_wp_val. iIntros (??).
  induction t using go_type_ind;
    try solve [
        iIntros (Φ) "_ HΦ"; wp_call_lc "?";
        rewrite [in #(_, _)]to_val_unseal /=;
          iApply "HΦ"; done
      ].
  iIntros (Φ) "_ HΦ"; wp_call_lc "?".
  iSpecialize ("HΦ" with "[$]").
  iInduction decls as [|[f' ft] decls] forall (Φ).
  - wp_pures.
    rewrite field_off_to_val_unfold /=.
    iApply "HΦ".
  - match goal with
    | |- context[environments.Esnoc _ (INamed "IHdecls") ?P] =>
        set (IHdeclsP := P)
    end.
    wp_pures.
    rewrite !field_off_to_val_unfold !desc_to_val_unfold /=.
    wp_pures.
    destruct (bool_decide_reflect (f' = f)); subst.
    + rewrite -> bool_decide_eq_true_2 by auto; wp_pures.
      rewrite -> ByteString.eqb_eq by auto.
      iApply "HΦ".
    + rewrite -> bool_decide_eq_false_2 by auto; wp_pures.
      rewrite -> ByteString.eqb_ne by auto.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      iApply "IHdecls".
      { naive_solver. }
      wp_pures.
      rewrite field_off_to_val_unfold.
      destruct ((fix field_offset_struct (d : struct.descriptor) :=
                  match d with
                  | nil => _
                  | cons _ _ => _
                  end)
        decls) eqn:Hoff.
      wp_pures.
      wp_apply wp_type_size.
      iIntros "_".
      wp_pures.
      iApply "HΦ".
Qed.

Global Instance pure_struct_field_ref_wp (t: go_type) f (l : loc) :
  PureWp True (struct.field_ref #t #f #l) #(struct.field_ref_f t f l).
Proof.
  pure_wp_start.
  destruct (struct.field_offset_f t f) eqn:Hoff.
  rewrite field_off_to_val_unfold /=; wp_pures.
  iExactEq "HΦ".
  repeat f_equal.
  rewrite struct.field_ref_f_unseal /struct.field_ref_f_def.
  rewrite Hoff /=.
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
  (struct.make #t (alist_val l))
  (struct.val_aux t l).
Proof.
  intros ?.
  pure_wp_start.
  rewrite struct.make_unseal /struct.make_def struct.val_aux_unseal.
  destruct t; try by exfalso.
  wp_pures.
  iInduction decls as [|[f ft] decls] "IH" forall (Φ).
  - wp_pure_lc "?". wp_pures. by iApply "HΦ".
  - wp_pure_lc "?"; wp_pures.
    rewrite !desc_to_val_unfold /=; wp_pures.
    destruct (alist_lookup_f _ _).
    + wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      unshelve iApply "IH"; first done.
      iIntros "_".
      simpl fill. wp_pures. by iApply "HΦ".
    + wp_pures.
      wp_bind (match decls with | nil => _ | cons _ _ => _ end).
      unshelve iApply "IH"; first done.
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

(* solve #default_val = zero_val t in IntoValTyped *)
Ltac solve_zero_val :=
  intros;
  rewrite zero_val_eq to_val_unseal /= struct.val_aux_unseal /=;
  rewrite zero_val_eq /= !to_val_unseal //=;
  cbn_w8.

Ltac solve_to_val_inj :=
  (* prove Inj (=) (=) (λ v, #v) *)
  intros;
  intros [] [];
  rewrite to_val_unseal /= struct.val_aux_unseal /=;
    cbn_w8;
  inv 1;
  try reflexivity.

Ltac solve_into_val_struct_field :=
  (* prove IntoValStructField *)
  constructor; intros ?;
  rewrite to_val_unseal /= struct.val_aux_unseal /= to_val_unseal //=;
  cbn_w8.

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

Ltac simpl_field_ref_f :=
  rewrite struct.field_ref_f_unseal /struct.field_ref_f_def;
  with_strategy transparent [w8_word_instance] (with_strategy opaque [loc_add] cbn);
  rewrite ?go_type_size_unseal /= ?loc_add_assoc ?loc_add_0 //.

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

Module time.

Definition Time : go_type := structT [
  "wall" :: uint64T;
  "ext" :: int64T;
  "loc" :: ptrT
].

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
Next Obligation. rewrite to_val_unseal /=; solve_has_go_type. Qed.
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
Global Instance wp_struct_make_Time `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} wall' ext' loc':
  PureWp True
    (struct.make #time.Time (alist_val [
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
  rewrite (@has_go_type_len _ (# (Time.wall' v)) int64T); [ | by solve_has_go_type ].
  rewrite (@has_go_type_len _ (# (Time.ext' v)) int64T); [ | by solve_has_go_type ].
  simpl_field_ref_f.
Qed.

End instances.
End time.

End __struct_automation_test.
