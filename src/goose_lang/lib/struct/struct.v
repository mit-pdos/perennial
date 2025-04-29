From iris.proofmode Require Import coq_tactics reduction.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.goose_lang Require Import proofmode typing.
From Perennial.goose_lang.lib Require Export
     typed_mem persistent_readonly struct.impl.
From Perennial.Helpers Require Import NamedProps.

Local Close Scope struct_scope.

Set Default Proof Using "Type".

Reserved Notation "l ↦[ d :: f ] dq v"
    (at level 20, dq custom dfrac at level 1, d at level 50, f at level 50,
       format "l  ↦[ d :: f ] dq  v").

Lemma bient_pure_wlog (p: Prop) {Σ} (P Q: iProp Σ) :
  (P -∗ ⌜p⌝) ->
  (Q -∗ ⌜p⌝) ->
  (p -> P ⊣⊢ Q) ->
  (P ⊣⊢ Q).
Proof.
  intros HP HQ Heq.
  iSplit.
  - iIntros "HP".
    iDestruct (HP with "HP") as %?.
    iApply (Heq with "HP"); auto.
  - iIntros "HQ".
    iDestruct (HQ with "HQ") as %?.
    iApply (Heq with "HQ"); auto.
Qed.

Theorem inv_readonly_acc {Σ} `{invGS Σ}
        (P: Qp -> iProp Σ)
        `{fractional.Fractional _ P} {Htimeless: forall q, Timeless (P q)}
        N E :
  ↑N ⊆ E →
  ⊢ inv N (∃ q, P q) ={E}=∗ ∃ q, P q.
Proof.
  iIntros (HN) "#Hinv".
  iInv N as (q) ">H" "Hclose".
  rewrite -(Qp.div_2 q).
  iDestruct (H0 (q/2)%Qp (q/2)%Qp with "H") as "[H1 H2]".
  iExists _; iFrame.
  iApply "Hclose".
  iExists _; iFrame.
Qed.

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

Implicit Types (t : ty).
Implicit Types (stk : stuckness).

Transparent struct.alloc.

Theorem wp_allocStruct_meta d stk E v :
  val_ty v (struct.t d) ->
  0 < ty_size (struct.t d) →
  {{{ True }}}
    struct.alloc d v @ stk; E
  {{{ l, RET #l; l ↦[struct.t d] v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Hty Hsize_gt0 Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_apply wp_ref_to_meta; auto.
Qed.

Theorem wp_allocStruct d stk E v :
  val_ty v (struct.t d) ->
  {{{ True }}}
    struct.alloc d v @ stk; E
  {{{ l, RET #l; l ↦[struct.t d] v }}}.
Proof.
  iIntros (Hty Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_apply wp_ref_to; auto.
Qed.

Opaque struct.alloc.

(* TODO: move this to common tactics *)
Ltac invc H := inversion H; subst; clear H.

Ltac inv_ty H :=
  match type of H with
  | val_ty _ _ =>
    inversion H; subst; clear H;
    try match goal with
        | [ H: lit_ty _ _ |- _ ] =>
          inversion H;
          let n := numgoals in
          guard n <= 1;
          subst; clear H
        end
  end.

Theorem getField_f_wt d f0 v :
  val_ty v (struct.t d) ->
  forall z t, field_offset d f0 = Some (z, t) ->
         val_ty (getField_f d f0 v) t.
Proof.
  revert v.
  induction d as [|[f t] fs]; simpl; intros.
  - congruence.
  - destruct (f =? f0)%string.
    + invc H0.
      inv_ty H.
      eauto.
    + destruct_with_eqn (field_offset fs f0); try congruence.
      destruct p as [off t'].
      invc H0.
      inv_ty H.
      eauto.
Qed.

Theorem setField_f_wt d f0 v fv' :
  val_ty v (struct.t d) ->
  forall z t, field_offset d f0 = Some (z, t) ->
         val_ty fv' t ->
         val_ty (setField_f d f0 fv' v) (struct.t d).
Proof.
  revert v.
  revert fv'.
  induction d as [|[f t] fs]; simpl; intros.
  - congruence.
  - destruct (f =? f0)%string.
    + invc H0.
      inv_ty H.
      eauto.
    + destruct_with_eqn (field_offset fs f0); try congruence.
      destruct p as [off t'].
      invc H0.
      inv_ty H.
      econstructor; eauto.
Qed.

Definition struct_field_pointsto_def l q (d: descriptor) (f0: string) (fv:val): iProp Σ :=
  match field_offset d f0 with
  | Some (off, t) =>
    (* this struct is for the field type *)
    struct_pointsto (l +ₗ off) q t fv
  | None => ⌜fv = #()⌝
  end.

Definition struct_field_pointsto_aux : seal (@struct_field_pointsto_def). Proof. by eexists. Qed.
Definition struct_field_pointsto := struct_field_pointsto_aux.(unseal).
Definition struct_field_pointsto_eq : @struct_field_pointsto = @struct_field_pointsto_def := struct_field_pointsto_aux.(seal_eq).

Ltac unseal :=
  rewrite struct_field_pointsto_eq /struct_field_pointsto_def.

Global Instance struct_field_pointsto_timeless l d f q v : Timeless (struct_field_pointsto l q d f v).
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p. refine _.
  - refine _.
Qed.

Global Instance struct_field_pointsto_fractional l d f v : fractional.Fractional (λ q : Qp, struct_field_pointsto l (DfracOwn q) d f v).
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p. refine _.
  - refine _.
Qed.

Global Instance struct_field_pointsto_as_fractional l q d f v : fractional.AsFractional (struct_field_pointsto l (DfracOwn q) d f v) (λ q0 : Qp, struct_field_pointsto l (DfracOwn q0) d f v) q.
Proof.
  split; [ done | apply _ ].
Qed.

Global Instance struct_field_pointsto_persistent l d f v : Persistent (struct_field_pointsto l DfracDiscarded d f v).
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p. refine _.
  - refine _.
Qed.

Lemma struct_field_pointsto_persist l q d f v :
  struct_field_pointsto l q d f v ==∗ struct_field_pointsto l DfracDiscarded d f v.
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p.
    apply struct_pointsto_persist.
  - iIntros "%". done.
Qed.

#[global]
Instance struct_field_pointsto_persistently l q d f v :
  UpdateIntoPersistently (struct_field_pointsto l q d f v)
    (struct_field_pointsto l DfracDiscarded d f v).
Proof.
  rewrite /UpdateIntoPersistently.
  iIntros "H".
  by iMod (struct_field_pointsto_persist with "H") as "#H".
Qed.

(* only works for first field *)
Lemma struct_field_pointsto_not_null l q (d:descriptor) f v ft :
  field_offset d f = Some (0, ft) →
  0 < ty_size ft →
  struct_field_pointsto l q d f v -∗ ⌜l ≠ null⌝.
Proof.
  unseal.
  intros -> Hsize.
  rewrite loc_add_0.
  iIntros "H".
  iApply (struct_pointsto_not_null with "H"). auto.
Qed.

Local Fixpoint struct_big_sep l q (d:descriptor) (v:val): iProp Σ :=
  match d with
  | [] => ⌜v = #()⌝
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => struct_pointsto l q t v1 ∗
                    struct_big_sep (l +ₗ ty_size t) q fs v2
    | _ => False
    end
  end.

Local Lemma struct_big_sep_ty l q d v :
  struct_big_sep l q d v ⊢@{_} ⌜val_ty v (struct.t d)⌝.
Proof.
  revert v l.
  induction d as [|[f t] fs]; simpl; intros.
  - iIntros (->) "!%".
    val_ty.
  - destruct v; auto.
    iIntros "[Hv1 Hv2]".
    iDestruct (struct_pointsto_ty with "Hv1") as %Hv1ty.
    iDestruct (IHfs with "Hv2") as %Hv2ty.
    iPureIntro.
    constructor; auto.
Qed.

Local Lemma struct_pointsto_to_big l q d v :
  struct_pointsto l q (struct.t d) v ⊣⊢ struct_big_sep l q d v.
Proof.
  apply (bient_pure_wlog (val_ty v (struct.t d))).
  { iApply struct_pointsto_ty. }
  { iApply struct_big_sep_ty. }
  intros Hty.
  (iInduction (d) as [| [f t] fs] "IH" forall (l v Hty)); simpl.
  - inv_ty Hty.
    rewrite struct_pointsto_eq /struct_pointsto_def /flatten_struct /=.
    rewrite left_id.
    auto.
  - inv_ty Hty.
    rewrite struct_pointsto_prod.
    iSplit; iIntros "[$ Hv2]".
    + iApply ("IH" with "[//] Hv2").
    + iApply ("IH" with "[//] Hv2").
Qed.

Local Fixpoint struct_big_fields_rec l q (d: descriptor) (fs:descriptor) (v:val): iProp Σ :=
  match fs with
  | [] => "_" ∷ ⌜v = #()⌝
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => f ∷ struct_field_pointsto l q d f v1 ∗
                    struct_big_fields_rec l q d fs v2
    | _ => False
    end
  end.

(** [struct_fields] is the desired function to describe a struct in terms of all
of its field points-to facts. *)
Definition struct_fields l q d v : iProp Σ := struct_big_fields_rec l q d d v.

Lemma field_offset_prefix (fs1: descriptor) f t (fs: descriptor) :
  f ∉ (fs1.*1) ->
  field_offset (fs1 ++ [(f, t)] ++ fs) f =
  Some (ty_size (struct.t fs1), t).
Proof.
  generalize dependent f.
  induction fs1 as [|[f' t'] fs1]; simpl; intros.
  - rewrite String.eqb_refl; auto.
  - apply not_elem_of_cons in H; destruct H.
    destruct (String.eqb_spec f' f); subst; try congruence.
    rewrite IHfs1; eauto.
Qed.

Lemma NoDup_app_singleton A l (x:A) :
  NoDup (l ++ [x]) ->
  x ∉ l.
Proof.
  intros Hnodup%NoDup_app.
  destruct Hnodup as (_&Hnotin&_).
  intros H%Hnotin.
  apply H.
  constructor.
Qed.

Lemma ty_size_struct_app d1 d2 :
  ty_size (struct.t (d1 ++ d2)) =
  ty_size (struct.t d1) + ty_size (struct.t d2).
Proof.
  induction d1 as [|[f t] fs]; simpl; auto.
  rewrite IHfs; lia.
Qed.

Local Lemma struct_big_sep_to_big_fields_gen l q fs1 fs v :
  NoDup ((fs1 ++ fs).*1) ->
  struct_big_fields_rec l q (fs1 ++ fs) fs v = struct_big_sep (l +ₗ ty_size (struct.t fs1)) q fs v.
Proof.
  revert fs1 v.
  induction fs as [|[f t] fs]; simpl; auto; intros.
  destruct v; auto.
  change (fs1 ++ (f,t)::fs) with (fs1 ++ [(f,t)] ++ fs).
  rewrite app_assoc in H |- *.
  rewrite IHfs; eauto.
  f_equal.
  - unseal.
    rewrite -app_assoc.
    erewrite field_offset_prefix; eauto.
    rewrite ?fmap_app in H.
    apply NoDup_app in H.
    destruct H as [H _].
    simpl in H.
    apply NoDup_app_singleton in H; auto.
  - rewrite ty_size_struct_app; simpl.
    rewrite Z.add_0_r.
    rewrite loc_add_assoc.
    reflexivity.
Qed.

Local Lemma struct_big_sep_to_fields l q d {dwf: struct.wf d} v :
  struct_big_sep l q d v = struct_fields l q d v.
Proof.
  intros.
  rewrite /struct_fields.
  change d with (nil ++ d) at 2.
  rewrite -> struct_big_sep_to_big_fields_gen by apply descriptor_NoDup.
  simpl.
  rewrite loc_add_0 //.
Qed.

Lemma struct_fields_ty l q d {dwf: struct.wf d} v :
  struct_fields l q d v -∗ ⌜val_ty v (struct.t d)⌝.
Proof.
  rewrite -struct_big_sep_to_fields.
  iApply struct_big_sep_ty.
Qed.

(** This is the big splitting theorem, for converting from a monolithic struct
points-to fact to the individual field pointers. *)
Theorem struct_fields_split l q d {dwf: struct.wf d} v :
  struct_pointsto l q (struct.t d) v ⊣⊢ struct_fields l q d v.
Proof.
  rewrite struct_pointsto_to_big struct_big_sep_to_fields //.
Qed.

Transparent structFieldRef.

Lemma wp_struct_fieldRef d f0 (l: loc) :
  match field_offset d f0 with
  | Some _ => True
  | None => False
  end →
  {{{ True }}}
    struct.fieldRef d f0 #l
  {{{ RET #(struct.fieldRef_f d f0 l); True }}}.
Proof.
  iIntros (Hoff_valid Φ) "_ HΦ".
  rewrite /struct.fieldRef /struct.fieldRef_f.
  destruct (field_offset d f0) as [[off t]|] eqn:Hoff; [|by destruct Hoff_valid]; wp_pures.
  iModIntro. iSpecialize ("HΦ" with "[//]").
  iExactEq "HΦ".
  f_equal. f_equal.
  change (uint.Z 1) with 1.
  rewrite Z.mul_1_r //.
Qed.

Opaque structFieldRef.

Lemma struct_field_pointsto_unfold l q d f v off t :
  field_offset d f = Some (off, t) →
  struct_field_pointsto l q d f v = ((l +ₗ off) ↦[t]{q} v)%I.
Proof. unseal. by intros ->. Qed.

Lemma wp_struct_fieldRef_pointsto l q d f off t v :
  field_offset d f = Some (off, t) →
  {{{ struct_field_pointsto l q d f v  }}}
    struct.fieldRef d f #l
  {{{ fl, RET #fl; ⌜∀ v', fl ↦[t]{q} v' ⊣⊢ struct_field_pointsto l q d f v'⌝ ∗ fl ↦[t]{q} v }}}.
Proof.
  iIntros (Hoff Φ) "Hf HΦ".
  erewrite struct_field_pointsto_unfold; eauto.
  wp_apply wp_struct_fieldRef.
  { rewrite Hoff //. }
  rewrite /struct.fieldRef_f Hoff.
  iApply "HΦ"; iFrame.
  iIntros "!%" (v').
  erewrite struct_field_pointsto_unfold; eauto.
Qed.

Lemma struct_pointsto_field_offset_acc l q d f0 (off: Z) t0 v :
  field_offset d f0 = Some (off, t0) ->
  struct_pointsto l q (struct.t d) v ⊢@{_}
  (struct_pointsto (l +ₗ off) q t0 (getField_f d f0 v) ∗
   (∀ fv', struct_pointsto (l +ₗ off) q t0 fv' -∗ struct_pointsto l q (struct.t d) (setField_f d f0 fv' v))).
Proof.
  revert l v off t0.
  induction d as [|[f t] fs]; simpl; intros.
  - congruence.
  - iIntros "Hl".
    iDestruct (struct_pointsto_ty with "Hl") as %Hty.
    inv_ty Hty.
    destruct (f =? f0)%string.
    + invc H; simpl.
      rewrite loc_add_0.
      iDestruct (struct_pointsto_prod with "Hl") as "[Hv1 Hv2]".
      iFrame.
      iIntros (fv') "Hv1".
      iDestruct (struct_pointsto_prod with "[$Hv1 $Hv2]") as "$".
    + destruct_with_eqn (field_offset fs f0); try congruence.
      destruct p as [off' t'].
      invc H.
      iDestruct (struct_pointsto_prod with "Hl") as "[Hv1 Hv2]".
      erewrite IHfs by eauto.
      rewrite loc_add_assoc.
      iDestruct "Hv2" as "[Hf Hupd]".
      iFrame "Hf".
      iIntros (fv') "Hf".
      iApply struct_pointsto_prod; iFrame.
      iApply ("Hupd" with "[$]").
Qed.

Theorem setField_getField_f_id d f0 v :
  setField_f d f0 (getField_f d f0 v) v = v.
Proof.
  revert v.
  induction d as [|[f t] fs]; simpl; eauto.
  - destruct v; auto.
    destruct (f =? f0)%string; congruence.
Qed.

Lemma struct_pointsto_acc_offset_read l q d f0 (off: Z) t0 v :
  field_offset d f0 = Some (off, t0) ->
  struct_pointsto l q (struct.t d) v -∗
  (struct_pointsto (l +ₗ off) q t0 (getField_f d f0 v) ∗
   (struct_pointsto (l +ₗ off) q t0 (getField_f d f0 v) -∗ struct_pointsto l q (struct.t d) v)).
Proof.
  iIntros (Hf) "Hl".
  iDestruct (struct_pointsto_field_offset_acc with "Hl") as "[Hf Hupd]"; [ eauto | .. ].
  iFrame.
  iIntros "Hf".
  iSpecialize ("Hupd" with "Hf").
  rewrite setField_getField_f_id //.
Qed.

Notation "l ↦[ d :: f ] dq v" := (struct_field_pointsto l dq d f%string v%V).

Theorem getField_f_none d f0 v :
  field_offset d f0 = None ->
  getField_f d f0 v = #().
Proof.
  revert v.
  induction d as [|[f t] fs]; simpl; auto; intros.
  destruct (f =? f0)%string.
  - congruence.
  - destruct_with_eqn (field_offset fs f0).
    + destruct p; congruence.
    + destruct v; auto.
Qed.

Theorem setField_f_none d f0 fv' v :
  field_offset d f0 = None ->
  setField_f d f0 fv' v = v.
Proof.
  revert v.
  induction d as [|[f t] fs]; simpl; auto; intros.
  destruct (f =? f0)%string.
  - congruence.
  - destruct_with_eqn (field_offset fs f0).
    + destruct p; congruence.
    + destruct v; auto.
      rewrite IHfs //.
Qed.

Lemma struct_pointsto_q l q t v :
  struct_pointsto l (DfracOwn q) t v ⊣⊢
  struct_pointsto l (DfracOwn (q/2)) t v ∗
  struct_pointsto l (DfracOwn (q/2)) t v.
Proof.
  rewrite -typed_mem.struct_pointsto_fractional Qp.div_2. auto.
Qed.

Global Instance struct_pointsto_as_pointsto d l v :
  AsMapsTo (struct_pointsto l (DfracOwn 1) d v)
           (fun q => struct_pointsto l (DfracOwn q) d v).
Proof.
  split; [ done | apply _ | apply _ ].
Qed.

Lemma struct_field_pointsto_q l q d f v :
  struct_field_pointsto l (DfracOwn q) d f v ⊣⊢
  struct_field_pointsto l (DfracOwn (q/2)) d f v ∗
  struct_field_pointsto l (DfracOwn (q/2)) d f v.
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p.
    rewrite struct_pointsto_q. done.
  - iSplit; iIntros; iPureIntro; intuition.
Qed.

Theorem struct_field_pointsto_agree l d f q1 v1 q2 v2 :
  struct_field_pointsto l q1 d f v1 -∗
  struct_field_pointsto l q2 d f v2 -∗
  ⌜v1 = v2⌝.
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p.
    apply struct_pointsto_agree.
  - iIntros; iPureIntro; subst; intuition.
Qed.

Global Instance struct_field_pointsto_as_pointsto d f l v :
  AsMapsTo (struct_field_pointsto l (DfracOwn 1) d f v)
           (fun q => struct_field_pointsto l (DfracOwn q) d f v).
Proof.
  split; [ done | apply _ | apply _ ].
Qed.

Lemma struct_pointsto_acc f0 l q d v :
  struct_pointsto l q (struct.t d) v -∗
  (struct_field_pointsto l q d f0 (getField_f d f0 v) ∗
   (∀ fv', struct_field_pointsto l q d f0 fv' -∗ struct_pointsto l q (struct.t d) (setField_f d f0 fv' v))).
Proof.
  destruct (field_offset d f0) as [[off t0]|] eqn:Hf.
  - iIntros "Hl".
    iDestruct (struct_pointsto_field_offset_acc with "Hl") as "[Hf Hupd]"; [ eauto | ].
    unseal; rewrite Hf.
    iFrame.
  - unseal; rewrite Hf.
    iIntros "Hl".
    iSplitR; auto.
    { rewrite getField_f_none; auto. }
    iIntros (fv') "_".
    rewrite -> setField_f_none by auto; auto.
Qed.

Lemma struct_pointsto_acc_read f0 l q d v :
  struct_pointsto l q (struct.t d) v -∗
  (struct_field_pointsto l q d f0 (getField_f d f0 v) ∗
   (struct_field_pointsto l q d f0 (getField_f d f0 v) -∗ struct_pointsto l q (struct.t d) v)).
Proof.
  destruct (field_offset d f0) as [[off t0]|] eqn:Hf.
  - iIntros "Hl".
    iDestruct (struct_pointsto_acc_offset_read with "Hl") as "[Hf Hupd]"; [ eauto | ].
    unseal; rewrite Hf.
    iFrame.
  - unseal; rewrite Hf.
    iIntros "Hl".
    rewrite getField_f_none; auto.
Qed.

Theorem struct_field_pointsto_ty l q d z t f v :
  field_offset d f = Some (z, t) ->
  struct_field_pointsto l q d f v -∗ ⌜val_ty v t⌝.
Proof.
  unseal.
  intros ->.
  iIntros "Hl".
  iDestruct (struct_pointsto_ty with "Hl") as %Hty.
  auto.
Qed.

Theorem struct_field_pointsto_none l q d f v :
  field_offset d f = None ->
  struct_field_pointsto l q d f v -∗ ⌜v = #()⌝.
Proof.
  unseal.
  intros ->.
  auto.
Qed.

Theorem wp_getField stk E d f0 (v: val) :
  val_ty v (struct.t d) ->
  {{{ True }}}
    getField d f0 v @ stk; E
  {{{ RET (getField_f d f0 v); True }}}.
Proof.
  iIntros (Hty Φ) "_ HΦ".
  iSpecialize ("HΦ" with "[//]").
  iInduction d as [|[f t] fs] "IH" forall (v Hty); simpl.
  - wp_rec. wp_pures; auto.
  - inv_ty Hty.
    destruct (f =? f0)%string.
    + wp_rec. wp_pures; auto.
    + wp_apply "IH"; auto.
Qed.

Transparent loadField storeField.

Theorem wp_loadField stk E l q d f fv :
  {{{ ▷ struct_field_pointsto l q d f fv }}}
    struct.loadF d f #l @ stk; E
  {{{ RET fv; struct_field_pointsto l q d f fv }}}.
Proof.
  rewrite /loadField.
  destruct (field_offset d f) as [[z t]|] eqn:Hf.
  - iIntros (Φ) "Hl HΦ".
    wp_pures.
    unseal; rewrite Hf.
    rewrite Z.mul_1_r.
    wp_load.
    iApply ("HΦ" with "[$]").
  - iIntros (Φ) "Hl HΦ".
    wp_pures.
    iDestruct (struct_field_pointsto_none with "Hl") as %->; auto.
    iApply ("HΦ" with "[$]").
Qed.

Lemma tac_wp_loadField Δ Δ' s E i l dq d f v Φ is_pers:
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (is_pers, struct_field_pointsto l dq d f v)%I →
  envs_entails Δ' (Φ v) →
  envs_entails Δ (WP (struct.loadF d f (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? HΦ.
  eapply bi.wand_apply; first by apply bi.wand_entails, wp_loadField.
  rewrite into_laterN_env_sound -bi.later_sep envs_lookup_split //; simpl.
  destruct is_pers.
  {
    apply bi.later_mono. simpl.
    rewrite -> bi.intuitionistically_sep_dup at 1. rewrite -bi.sep_assoc.
    eapply bi.entails_po; first by apply bi.sep_mono_l, bi.intuitionistically_elim.
    eapply bi.sep_mono_r, bi.entails_po, bi.wand_intro_l; first by apply bi.wand_elim_r.
    rewrite HΦ. apply bi.sep_elim_r, _.
  }
  by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
Qed.

Theorem wp_load_ro l t v :
  {{{ readonly (struct_pointsto l (DfracOwn 1) t v) }}}
    load_ty t #l
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ) "#Hro HΦ".
  iMod (readonly_load with "Hro") as (q) "Hl".
  wp_apply (wp_LoadAt with "Hl"); iIntros "_".
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_loadField_ro {stk E} l d f fv :
  {{{ readonly (struct_field_pointsto l (DfracOwn 1) d f fv) }}}
    struct.loadF d f #l @ stk; E
  {{{ RET fv; True }}}.
Proof.
  iIntros (Φ) "#Hro HΦ".
  iMod (readonly_load with "Hro") as (q) "Hl".
  wp_apply (wp_loadField with "Hl"); iIntros "_".
  iApply ("HΦ" with "[//]").
Qed.

Lemma tac_wp_loadField_ro {E} Δ s i l d f v Φ :
  envs_lookup i Δ = Some (true, readonly (struct_field_pointsto l (DfracOwn 1) d f v))%I →
  envs_entails Δ (Φ v) →
  envs_entails Δ (WP (struct.loadF d f (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΦ.
  eapply bi.wand_apply; first by apply bi.wand_entails, wp_loadField_ro.
  rewrite envs_lookup_split //; simpl.
  iIntros "[#Hro Henvs]".
  iSplitR; auto.
  iIntros "!> _".
  iApply HΦ.
  iApply ("Henvs" with "Hro").
Qed.

Definition field_ty d f: ty :=
  match field_offset d f with
  | Some (_, t) => t
  | None => unitT
  end.

Theorem wp_storeField stk E l d f fv fv' :
  val_ty fv' (field_ty d f) ->
  {{{ ▷ struct_field_pointsto l (DfracOwn 1) d f fv }}}
    struct.storeF d f #l fv' @ stk; E
  {{{ RET #(); struct_field_pointsto l (DfracOwn 1) d f fv' }}}.
Proof.
  rewrite /storeField /field_ty.
  intros Hty.
  destruct (field_offset d f) as [[z t]|] eqn:Hf.
  - iIntros (Φ) "Hl HΦ".
    wp_pures.
    unseal; rewrite Hf.
    rewrite Z.mul_1_r.
    wp_store.
    iApply ("HΦ" with "[$]").
  - inv_ty Hty.
    iIntros (Φ) "Hl HΦ".
    wp_pures.
    iDestruct (struct_field_pointsto_none with "Hl") as %->; auto.
    iApply ("HΦ" with "[$]").
Qed.

Opaque loadField storeField.

Lemma tac_wp_storeField Δ Δ' Δ'' stk E i l d f v v' Φ :
  val_ty v' (field_ty d f) →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[d :: f] v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦[d :: f] v')) Δ' = Some Δ'' →
  envs_entails Δ'' (Φ (LitV LitUnit)) →
  envs_entails Δ (WP (struct.storeF d f (LitV l) (Val v')) @ stk; E {{ Φ }}).
Proof.
  intros Hty.
  rewrite envs_entails_unseal=> ????.
  eapply bi.wand_apply; first by eapply bi.wand_entails, wp_storeField.
  rewrite into_laterN_env_sound -bi.later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
Qed.

Theorem wp_loadField_struct stk E l q d f v :
  {{{ struct_pointsto l q (struct.t d) v }}}
    struct.loadF d f #l @ stk; E
  {{{ RET (getField_f d f v); struct_pointsto l q (struct.t d) v }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  iDestruct (struct_pointsto_acc_read f with "Hs") as "[Hf Hupd]".
  wp_apply (wp_loadField with "Hf"); iIntros "Hf".
  iApply "HΦ".
  iApply ("Hupd" with "[$]").
Qed.

Theorem wp_storeField_struct stk E l d f v fv' :
  val_ty fv' (field_ty d f) ->
  {{{ struct_pointsto l (DfracOwn 1) (struct.t d) v }}}
    struct.storeF d f #l fv' @ stk; E
  {{{ RET #(); struct_pointsto l (DfracOwn 1) (struct.t d) (setField_f d f fv' v) }}}.
Proof.
  iIntros (Hty Φ) "Hs HΦ".
  iDestruct (struct_pointsto_acc f with "Hs") as "[Hf Hupd]".
  wp_apply (wp_storeField with "Hf"); auto.
  iIntros "Hf".
  iApply "HΦ".
  iApply ("Hupd" with "[$]").
Qed.

End goose_lang.

Typeclasses Opaque struct_pointsto.
Typeclasses Opaque struct_field_pointsto.

Notation "l ↦[ d :: f ] dq v" :=
  (struct_field_pointsto l dq d f%string v%V).

(* Enable solving of val_ty goals where the type is looked up from a struct declaration.
([simple apply] unification is too weak to do this automatically.)
Priority is lower than the [constructor] hint to avoid that one unfolding in
uncontrolled ways. *)
#[global]
Hint Extern 5 (val_ty ?v (field_ty ?t ?f)) =>
  let field_t_expr := constr:(field_ty t f) in
  (* Try to unfold as little as possible. *)
  let field_t := eval cbv [field_ty field_offset] in field_t_expr in
  let field_t2 := eval simpl in field_t in
  change (val_ty v field_t2)
  : core.

Tactic Notation "wp_loadField" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_ :: _] { _ } _)%I) => l end in
    iAssumptionCore || fail 1 "wp_loadField: cannot find" l "↦[d :: f] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      first [wp_bind (struct.loadF _ _ (Val _))
            | fail "wp_loadField: cannot find 'struct.loadF' in" e ]
  | _ => fail "wp_loadField: not a 'wp'"
  end;
  match goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    eapply tac_wp_loadField_ro;
    [iAssumptionCore
    |]
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    eapply tac_wp_loadField;
    [tc_solve
    |solve_pointsto ()
    |]
  end.

Tactic Notation "wp_storeField" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_ :: _]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_storeField: cannot find" l "↦[d :: f] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      first [wp_bind (struct.storeF _ _ (Val _) (Val _))
            | fail "wp_storeField: cannot find 'struct.storeF' in" e ]
  | _ => fail "wp_storeField: not a 'wp'"
  end;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    eapply tac_wp_storeField;
    [val_ty
    |tc_solve
    |solve_pointsto ()
    |pm_reflexivity
    |try (wp_pure_filter (Rec BAnon BAnon _); wp_rec)]
  end.

Ltac iNamedStruct H :=
  iDestruct (struct_fields_split with H) as "_temp_";
  iNamed "_temp_".
