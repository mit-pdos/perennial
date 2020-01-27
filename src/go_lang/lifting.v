From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap excl.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From Perennial.Helpers Require Import Transitions.
From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import tactics notation map.
From Perennial.go_lang Require Import typing.
Set Default Proof Using "Type".

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=nonAtomic val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=nonAtomic val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section StructMapsto.
  Context {ext:ext_op}.
  Context {ext_ty:ext_types ext}.

  Theorem ty_size_gt0 t : 0 <= ty_size t.
  Proof.
    induction t; simpl; lia.
  Qed.

  Definition val_ty (v: val) (t:ty) := val_hasTy ∅ v t.

  Theorem val_ty_len {v t} : val_ty v t -> length (flatten_struct v) = Z.to_nat (ty_size t).
  Proof.
    unfold val_ty; intros H.
    induction H; simpl; rewrite -> ?app_length in *; auto.
    - inversion H; subst; auto.
    - pose proof (ty_size_gt0 t1).
      pose proof (ty_size_gt0 t2).
      lia.
  Qed.

  Context {Σ} {hG: gen_heapG loc (nonAtomic val) Σ}.

  Definition struct_mapsto l q (t:ty) (v: val): iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{q} Free vj) ∗ ⌜val_ty v t⌝)%I.

  Theorem struct_mapsto_singleton l q t v v0 :
    flatten_struct v = [v0] ->
    struct_mapsto l q t v -∗ l ↦{q} Free v0.
  Proof.
    intros Hv.
    rewrite /struct_mapsto Hv /=.
    rewrite loc_add_0 right_id.
    by iIntros "[$ _]".
  Qed.

End StructMapsto.

Notation "l ↦[ ty ]{ q } v" := (struct_mapsto l q ty v%V)
                                  (at level 20, q at level 50, ty at level 50,
                                   format "l  ↦[ ty ]{ q }  v") : bi_scope.
Notation "l ↦[ ty ] v" := (struct_mapsto l 1 ty v%V)
                             (at level 20, ty at level 50,
                              format "l  ↦[ ty ]  v") : bi_scope.

Class ffi_interp (ffi: ffi_model) :=
  { ffiG: gFunctors -> Set;
    ffi_ctx: forall `{ffiG Σ}, ffi_state -> iProp Σ; }.

Arguments ffi_ctx {ffi FfiInterp Σ} fG : rename.

Section go_lang.
  Context `{ffi_semantics: ext_semantics}.
  Context {ext_tys: ext_types ext}.
  Context `{!ffi_interp ffi}.

Definition traceO := leibnizO (list event).
Definition OracleO := leibnizO (Oracle).
Class traceG (Σ: gFunctors) := {
  trace_inG :> inG Σ (authR (optionUR (exclR traceO)));
  oracle_inG :> inG Σ (authR (optionUR (exclR OracleO)));
  trace_name : gname;
  oracle_name : gname
}.
Arguments trace_name {_} _.
Arguments oracle_name {_} _.

Class trace_preG (Σ: gFunctors) := {
  trace_preG_inG :> inG Σ (authR (optionUR (exclR traceO)));
  oracle_preG_inG :> inG Σ (authR (optionUR (exclR OracleO)));
}.

Definition traceΣ : gFunctors :=
  #[GFunctor (authR (optionUR (exclR traceO)));
      GFunctor (authR (optionUR (exclR OracleO)))].

Global Instance subG_crashG {Σ} : subG traceΣ Σ → trace_preG Σ.
Proof using Type. solve_inG. Qed.

Definition trace_auth `{hT: traceG Σ} (l: Trace) :=
  own (trace_name hT) (● (Excl' (l: traceO))).
Definition trace_frag `{hT: traceG Σ} (l: Trace) :=
  own (trace_name hT) (◯ (Excl' (l: traceO))).
Definition oracle_auth `{hT: traceG Σ} (o: Oracle) :=
  own (oracle_name hT) (● (Excl' (o: OracleO))).
Definition oracle_frag `{hT: traceG Σ} (o: Oracle) :=
  own (oracle_name hT) (◯ (Excl' (o: OracleO))).

Lemma trace_init `{hT: trace_preG Σ} (l: list event) (o: Oracle):
  (|==> ∃ H : traceG Σ, trace_auth l ∗ trace_frag l ∗ oracle_auth o ∗ oracle_frag o)%I.
Proof using Type.
  iMod (own_alloc (● (Excl' (l: traceO)) ⋅ ◯ (Excl' (l: traceO)))) as (γ) "[H1 H2]".
  { apply auth_both_valid; split; eauto. econstructor. }
  iMod (own_alloc (● (Excl' (o: OracleO)) ⋅ ◯ (Excl' (o: OracleO)))) as (γ') "[H1' H2']".
  { apply auth_both_valid; split; eauto. econstructor. }
  iModIntro. iExists {| trace_name := γ; oracle_name := γ' |}. iFrame.
Qed.

Lemma trace_update `{hT: traceG Σ} (l: Trace) (x: event):
  trace_auth l -∗ trace_frag l ==∗ trace_auth (add_event x l) ∗ trace_frag (add_event x l).
Proof using Type.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' _ ⋅ ◯ Excl' _) with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.

Lemma trace_agree `{hT: traceG Σ} (l l': list event):
  trace_auth l -∗ trace_frag l' -∗ ⌜ l = l' ⌝.
Proof using Type.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  done.
Qed.

Lemma oracle_agree `{hT: traceG Σ} (o o': Oracle):
  oracle_auth o -∗ oracle_frag o' -∗ ⌜ o = o' ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  done.
Qed.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_ffiG : ffiG Σ;
  heapG_gen_heapG :> gen_heapG loc (nonAtomic val) Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ;
  heapG_oracleG :> proph_mapG proph_id (val * val) Σ;
  heapG_traceG :> traceG Σ;
}.

Global Instance heapG_irisG `{!heapG Σ} :
  irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id) ∗ ffi_ctx heapG_ffiG σ.(world)
      ∗ trace_auth σ.(trace) ∗ oracle_auth σ.(oracle))%I;
  fork_post _ := True%I;
}.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
    rewrite /head_step /= in H;
    monad_inv; repeat (simpl in H; monad_inv)
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => rewrite /head_step /= : core.
Local Hint Extern 1 (relation.bind _ _ _ _ _) => monad_simpl; simpl : core.
Local Hint Extern 1 (relation.runF _ _ _ _) => monad_simpl; simpl : core.
(* Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : core. *)
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (head_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Resolve to_of_val : core.

Global Instance into_val_val v : IntoVal (Val v) v.
Proof using Type. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof using Type. by eexists. Qed.

Theorem heap_head_atomic e :
  (forall σ κ e' σ' efs,
      relation.denote (head_trans e) σ σ' (κ, e', efs) -> is_Some (to_val e')) ->
  head_atomic StronglyAtomic e.
Proof using Type.
  intros Hdenote.
  hnf; intros * H%Hdenote.
  auto.
Qed.

Theorem atomically_is_val Σ (tr: transition Σ val) σ σ' κ e' efs :
  relation.denote (atomically tr) σ σ' (κ, e', efs) ->
  is_Some (to_val e').
Proof using Type.
  intros.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H; subst.
  eexists; eauto.
Qed.

Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_head_atomic; cbn [relation.denote head_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Global Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof using Type.
  solve_atomic.
Qed.

(* PrepareWrite and Store are individually atomic, but the two need to be
combined to actually write to the heap and that is not atomic. *)
Global Instance prepare_write_atomic s v : Atomic s (PrepareWrite (Val v)).
Proof using Type. solve_atomic. Qed.
Global Instance load_atomic s v : Atomic s (Load (Val v)).
Proof using Type. solve_atomic. Qed.
Global Instance finish_store_atomic s v1 v2 : Atomic s (FinishStore (Val v1) (Val v2)).
Proof using Type. solve_atomic. Qed.
Global Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof using Type. solve_atomic. Qed.
Global Instance fork_atomic s e : Atomic s (Fork e).
Proof using Type. solve_atomic.
       simpl in H; monad_inv.
       eexists; eauto.
Qed.
Global Instance skip_atomic s  : Atomic s Skip.
Proof using Type. solve_atomic.
       simpl in H; monad_inv.
       eexists; eauto.
Qed.
Global Instance new_proph_atomic s : Atomic s NewProph.
Proof using Type. solve_atomic. Qed.
Global Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof using Type. solve_atomic. Qed.
Global Instance ext_atomic s op v : Atomic s (ExternalOp op (Val v)).
Proof using Type. solve_atomic. Qed.
Global Instance input_atomic s v : Atomic s (Input (Val v)).
Proof using Type. solve_atomic. Qed.
Global Instance output_atomic s v : Atomic s (Output (Val v)).
Proof using Type. solve_atomic. Qed.

Global Instance proph_resolve_atomic s e v1 v2 :
  Atomic s e → Atomic s (Resolve e (Val v1) (Val v2)).
Proof using Type.
  rename e into e1. intros H σ1 e2 κ σ2 efs [Ks e1' e2' Hfill -> step].
  simpl in *. induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
  - subst. rewrite /head_step /= in step.
    repeat inv_undefined.
    inversion_clear step.
    repeat inv_undefined.
    inversion_clear H1.
    inversion_clear H2.
    destruct s.
    + eexists; eauto.
    + eapply val_irreducible; simpl.
      eexists; eauto.
  - rewrite fill_app. rewrite fill_app in Hfill.
    assert (∀ v, Val v = fill Ks e1' → False) as fill_absurd.
    { intros v Hv. assert (to_val (fill Ks e1') = Some v) as Htv by by rewrite -Hv.
      apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step; contradiction. }
    destruct K; (inversion Hfill; clear Hfill; subst; try
      match goal with | H : Val ?v = fill Ks e1' |- _ => by apply fill_absurd in H end).
    refine (_ (H σ1 (fill (Ks ++ [K]) e2') _ σ2 efs _)).
    + destruct s; intro Hs; simpl in *.
      * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, Ks.
      * apply irreducible_resolve. by rewrite fill_app in Hs.
    + econstructor 1 with (K := Ks ++ [K]); try done. simpl. by rewrite fill_app.
Qed.

Global Instance resolve_proph_atomic s v1 v2 : Atomic s (ResolveProph (Val v1) (Val v2)).
Proof using Type. by apply proph_resolve_atomic, skip_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; cbn; repeat (monad_simpl; simpl).
Local Ltac solve_exec_puredet := rewrite /= /head_step /=; intros; repeat (monad_inv; simpl in * ); eauto.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Global Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof using Type. solve_pure_exec. Qed.
Global Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof using Type. solve_pure_exec. Qed.
Global Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof using Type. solve_pure_exec. Qed.
Global Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof using Type. solve_pure_exec. Qed.

Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof using Type. unfold AsRecV in *. solve_pure_exec. Qed.

Global Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof using Type. solve_pure_exec. Qed.

Global Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof using Type. solve_pure_exec. Qed.
(* Higher-priority instance for EqOp. *)
Global Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof using Type.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

Global Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof using Type. solve_pure_exec. Qed.

Global Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof using Type. solve_pure_exec. Qed.

Global Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof using Type. solve_pure_exec. Qed.

Global Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof using Type. solve_pure_exec. Qed.

Global Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof using Type. solve_pure_exec. Qed.

Global Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof using Type. solve_pure_exec. Qed.

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma wp_panic s msg E Φ :
  ▷ False -∗ WP Panic msg @ s; E {{ Φ }}.
Proof using Type.
  iIntros ">[] HΦ".
Qed.

Lemma wp_output s E tr lit :
  {{{ trace_frag tr }}}
     Output (LitV lit) @ s; E
  {{{ RET (LitV LitUnit); trace_frag (add_event (Out_ev lit) tr)}}}.
Proof using Type.
  iIntros (Φ) "Htr HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "(Hσ&?&?&Htr_auth&?) !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iFrame.
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iMod (trace_update with "[$] [$]") as "(?&?)".
  iModIntro. iFrame; iSplitL; last done. by iApply "HΦ".
Qed.

Lemma wp_input s E tr sel Or :
  {{{ trace_frag tr ∗ oracle_frag Or }}}
     Input (LitV sel) @ s; E
  {{{ RET (LitV (LitInt (Or tr sel))); trace_frag (add_event (In_ev sel (LitInt (Or tr sel))) tr)}}}.
Proof using Type.
  iIntros (Φ) "(Htr&Hor) HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "(Hσ&?&?&Htr_auth&Hor_auth) !>"; iSplit.
  { iPureIntro. unshelve (by eauto); apply (U64 0). }
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iDestruct (oracle_agree with "[$] [$]") as %?; subst.
  iFrame. iMod (trace_update with "[$] [$]") as "(?&?)".
  iModIntro. iFrame; iSplitL; last done. by iApply "HΦ".
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof using Type.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

Lemma twp_fork s E e Φ :
  WP e @ s; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ WP Fork e @ s; E [{ Φ }].
Proof using Type.
  iIntros "He HΦ". iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1 κs n) "Hσ !>"; iSplit; first by eauto.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

(** Heap *)
(** The "proper" [allocN] are derived in [array]. *)

Lemma heap_array_to_seq_meta {V} l (vs: list V) (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof using Type.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Theorem heap_array_app V l (vs1 vs2: list V) :
  heap_array l (vs1 ++ vs2) = heap_array l vs1 ∪ heap_array (l +ₗ (length vs1)) vs2.
Proof.
  revert l.
  induction vs1; simpl; intros.
  - rewrite left_id loc_add_0 //.
  - rewrite IHvs1.
    rewrite loc_add_assoc.
    replace (1 + strings.length vs1) with (Z.of_nat (S (strings.length vs1))) by lia.
    (* true, but only due to disjointness *)
    admit.
Admitted.

Theorem concat_replicate_S A n (vs: list A) :
  concat_replicate (S n) vs = vs ++ concat_replicate n vs.
Proof.
  reflexivity.
Qed.

Theorem concat_replicate_length A n (vs: list A) :
  length (concat_replicate n vs) = (n * length vs)%nat.
Proof.
  induction n; simpl; auto.
  rewrite concat_replicate_S app_length IHn //.
Qed.

Lemma heap_array_to_seq_mapsto l vs :
  ([∗ map] l' ↦ vm ∈ heap_array l (fmap Free vs), l' ↦ vm) -∗
  [∗ list] j ↦ v ∈ vs, (l +ₗ j) ↦ Free v.
Proof using Type.
  iIntros "Hvs". iInduction vs as [|vs] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Theorem big_opL_add (M: ofeT) (o: M -> M -> M) {mon:monoid.Monoid o} f start off n :
  big_opL o f (seq (start + off) n) ≡
  big_opL o (fun i x => f i (x + off)%nat) (seq start n).
Proof.
  revert start off.
  induction n; simpl; auto; intros.
  (* seems not the right proof strategy; also don't seem to know that op is
  proper *)
Abort.

Lemma heap_array_replicate_to_nested_mapsto l vs (n : nat) :
  ([∗ map] l' ↦ vm ∈ heap_array l (fmap Free (concat_replicate n vs)), l' ↦ vm) -∗
  [∗ list] i ∈ seq 0 n, [∗ list] j ↦ v ∈ vs, (l +ₗ ((i : nat) * Z.of_nat (length vs)) +ₗ j)%nat ↦ Free v.
Proof using Type.
  iIntros "Hmap".
  iDestruct (heap_array_to_seq_mapsto with "Hmap") as "Hvs".
  iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite concat_replicate_S.
  iDestruct (big_sepL_app with "Hvs") as "[Hvs Hconcat]".
  iSplitL "Hvs".
  - rewrite loc_add_0.
    iFrame.
  - setoid_rewrite Nat2Z.inj_add.
    setoid_rewrite <- loc_add_assoc.
    iDestruct ("IH" with "Hconcat") as "Hseq".
    admit. (* need to move between seq 0 and seq 1 *)
Admitted.

Lemma wp_allocN_seq s E t v (n: u64) :
  (0 < int.val n)%Z →
  val_ty v t ->
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (int.nat n),
                              ((l +ₗ[t] Z.of_nat i) ↦[t] v) }}}.
Proof using Type.
  iIntros (Hn Hty Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs k) "[Hσ Hκs] !>"; iSplit; first by auto with lia.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_alloc_gen
          _ (heap_array
               l (fmap Free (concat_replicate (int.nat n) (flatten_struct v)))) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite map_length concat_replicate_length. auto with lia. }
  iModIntro; iSplit; first done.
  iFrame "Hσ Hκs". iApply "HΦ".
  unfold struct_mapsto.
  iDestruct (heap_array_replicate_to_nested_mapsto with "Hl") as "Hl".
  rewrite (val_ty_len Hty).
  iApply (big_sepL_mono with "Hl").
  iIntros (k0 j _) "H".
  setoid_rewrite Z.mul_comm at 1.
  setoid_rewrite Z2Nat.id.
  { by iFrame. }
  apply ty_size_gt0.
Qed.
(*
Lemma twp_allocN_seq s E v (n: u64) :
  (0 < int.val n)%Z →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (int.nat n),
      (l +ₗ (i : nat)) ↦ Free v ∗ meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof using Type.
  iIntros (Hn Φ) "_ HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs k) "[Hσ Hκs] !>"; iSplit; first by destruct_with_eqn (int.val n); auto with lia.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_alloc_gen
          _ (heap_array
               l (fmap Free (replicate (int.nat n) v))) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite map_length replicate_length u64_Z_through_nat; auto with lia. }
  iModIntro; do 2 (iSplit; first done).
  iFrame "Hσ Hκs". iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_mapsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite map_length replicate_length.
Qed.
*)

Lemma wp_alloc stk E ty v :
  val_ty v ty ->
  {{{ True }}} Alloc (Val v) @ stk; E {{{ l, RET LitV (LitLoc l); l ↦[ty] v }}}.
Proof using Type.
  iIntros (Hty Φ) "_ HΦ". iApply wp_allocN_seq; eauto with lia.
  { constructor. }
  iIntros "!>" (l) "/= (? & _)". rewrite Z.mul_0_r loc_add_0. iApply "HΦ"; iFrame.
Qed.
(*
Lemma twp_alloc s E v :
  [[{ True }]] Alloc (Val v) @ s; E [[{ l, RET LitV (LitLoc l); l ↦ Free v ∗ meta_token l ⊤ }]].
Proof using Type.
  iIntros (Φ) "_ HΦ". iApply twp_allocN_seq; auto with lia.
  { constructor. }
  iIntros (l) "/= (? & _)". rewrite loc_add_0. iApply "HΦ"; iFrame.
Qed.
*)

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} Free v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{q} Free v }}}.
Proof using Type.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma twp_load s E l q v :
  [[{ l ↦{q} Free v }]] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{q} Free v }]].
Proof using Type.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iSplit; first done. iFrame. by iApply "HΦ".
Qed.

Theorem is_Writing_Some A (mna: option (nonAtomic A)) :
  mna = Some Writing ->
  is_Writing mna.
Proof using Type.
  rewrite /is_Writing; auto.
Qed.

Hint Resolve is_Writing_Some.

Lemma wp_prepare_write s E l v :
  {{{ ▷ l ↦ Free v }}} PrepareWrite (Val $ LitV (LitLoc l)) @ s; E
  {{{ RET LitV LitUnit; l ↦ Writing }}}.
Proof using Type.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma twp_prepare_write s E l v :
  [[{ l ↦ Free v }]] PrepareWrite (Val $ LitV $ LitLoc l) @ s; E
  [[{ RET LitV LitUnit; l ↦ Writing }]].
Proof using Type.
  iIntros (Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.

Lemma wp_finish_store s E l v :
  {{{ ▷ l ↦ Writing }}} FinishStore (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ Free v }}}.
Proof using Type.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma twp_finish_store s E l v :
  [[{ l ↦ Writing }]] FinishStore (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ Free v }]].
Proof using Type.
  iIntros (Φ) "Hl HΦ".
  iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.

Definition mapsto_vals (l: loc) (q: Qp) (vs: list (nonAtomic val)) :=
  ([∗ map] l ↦ nav ∈ heap_array l vs, l ↦{q} nav)%I.

Theorem gen_heap_valid_map (σ: gmap _ _) l q vs :
  gen_heap_ctx σ -∗
               ([∗ map] l↦v ∈ heap_array l vs, l ↦{q} v) -∗
               ⌜forall i, (i < (length vs))%nat -> is_Some (σ !! (l +ₗ i))⌝.
Proof using Type.
  iIntros "Hctx Hmap".
  iIntros (i Hi).
  apply lookup_lt_is_Some_2 in Hi.
  destruct Hi as [v ?].
  assert (heap_array l vs !! (l +ₗ i) = Some v).
  { apply heap_array_lookup.
    exists (Z.of_nat i).
    rewrite Nat2Z.id; intuition eauto.
    lia. }
  iDestruct (big_sepM_lookup _ _ _ _ H0 with "Hmap") as "H".
  iDestruct (gen_heap_valid with "Hctx H") as %?.
  eauto.
Qed.

Definition map_mapsto l q m_def :=
  (∃ vs, l ↦{q} Free vs ∗ ⌜ map_val vs = Some m_def ⌝)%I.

Lemma wp_map_get s E l q m_def k :
  {{{ ▷ map_mapsto l q m_def }}} MapGet (Val $ LitV (LitLoc l)) (Val $ LitV $ LitInt k) @ s; E
  {{{ r ok, RET PairV r (LitV $ LitBool ok); ⌜ map_get m_def k = (r, ok) ⌝ ∗ map_mapsto l q m_def }}}.
Proof using Type.
  iIntros (Φ) ">Hl HΦ".
  iDestruct "Hl" as (vs) "(Hl&Hmap)".
  iDestruct "Hmap" as %Hmap.
Abort.

Theorem map_cons_insert k v vs m_def :
  map_val vs = Some m_def ->
  map_val (MapConsV k v vs) = Some (map_insert m_def k v).
Proof using Type.
  destruct m_def; simpl.
  by intros ->.
Qed.

Lemma wp_map_insert s E l m_def k v :
  {{{ ▷ map_mapsto l 1 m_def }}} MapInsert (Val $ LitV (LitLoc l)) (Val $ LitV $ LitInt k) (Val v) @ s; E
  {{{ RET LitV LitUnit; map_mapsto l 1 (map_insert m_def k v) }}}.
Proof using Type.
  iIntros (Φ) ">Hl HΦ".
  iDestruct "Hl" as (vs) "(Hl&Hmap)".
  iDestruct "Hmap" as %Hmap.
Abort.

Lemma wp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} Free v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} Free v' }}}.
Proof using Type.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma twp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{q} Free v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{q} Free v' }]].
Proof using Type.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iSplit; first done. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ Free v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ Free v2 }}}.
Proof using Type.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma twp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ Free v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ Free v2 }]].
Proof using Type.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto 8. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof using Type.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "(Hσ&HR&Hffi) !>". iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep). inv_head_step.
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof using Type.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply Ectx_step with (K:=[]); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl.
  rewrite /head_step /=.
  econstructor.
  - by apply prim_step_to_val_is_head_step.
  - simpl.
    econstructor; auto.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  head_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof using Type.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst.
    inv_head_step. repeat inv_undefined.
    inversion_clear step. repeat inv_undefined.
    simpl in H0; monad_inv.
    rewrite /head_step /=.
    econstructor; eauto; simpl.
    econstructor; auto.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - assert (fill_item K (fill Ks e1') = fill (Ks ++ [K]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item K (fill Ks e2') = fill (Ks ++ [K]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [K]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply Ectx_step with (K0 := Ks ++ [K]); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - assert (to_val (fill Ks e1') = Some vp); first by rewrite -H1 //.
      apply to_val_fill_some in H. destruct H as [-> ->].
      rewrite /head_step /= in step; monad_inv.
    - assert (to_val (fill Ks e1') = Some vt); first by rewrite -H2 //.
      apply to_val_fill_some in H. destruct H as [-> ->].
      rewrite /head_step /= in step; monad_inv.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof using Type.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 κ κs n) "(Hσ&Hκ&Hw)". destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 [] κs n with "[$Hσ $Hκ $Hw]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    rewrite /head_step /= in step.
    inversion_clear step.
    repeat inv_undefined.
    simpl in H0; monad_inv.
    match goal with H: [] = ?κs ++ [_] |- _ => by destruct κs end.
  - rewrite -app_assoc.
    iMod ("WPe" $! σ1 _ _ n with "[$Hσ $Hκ $Hw]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    rewrite /head_step /= in step.
    inversion_clear step.
    repeat inv_undefined.
    simpl in H0; monad_inv.
    simplify_list_eq.
    rename v0 into w', s2 into σ2, l into efs.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "[[$ (Hκ&Hw)] WPe]".
    iMod (proph_map_resolve_proph p (w',v) κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iFrame.
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof using Type.
  iIntros (Φ) "Hp HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply wp_pure_step_later=> //=. iApply wp_value.
  iIntros "!>" (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma wp_resolve_cmpxchg_suc s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ Free v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ Free v2 }}}.
Proof using Type.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (wp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_fail s E l (p : proph_id) (pvs : list (val * val)) q v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{q} Free v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} Free v' }}}.
Proof using Type.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

End lifting.
End go_lang.

Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.
