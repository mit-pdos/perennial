From iris.proofmode Require Import coq_tactics reduction.
From iris.base_logic.lib Require Import invariants.
From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang.lib Require Export
     typed_mem persistent_readonly struct.impl.
From Perennial.Helpers Require Import NamedProps.

Close Scope struct_scope.

Set Default Proof Using "Type".

Reserved Notation "l ↦[ d :: f ]{ q } v"
    (at level 20, q at level 50, d at level 50, f at level 50,
    format "l  ↦[ d  ::  f ]{ q }  v").
Reserved Notation "l ↦[ d :: f ] v"
    (at level 20, d at level 50, f at level 50,
    format "l  ↦[ d  ::  f ]  v").

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

Theorem inv_readonly_acc {Σ} `{invG Σ}
        (P: Qp -> iProp Σ)
        `{fractional.Fractional _ P} {Htimeless: forall q, Timeless (P q)}
        N E :
  ↑N ⊆ E →
  ⊢ inv N (∃ q, P q) ={E}=∗ ∃ q, P q.
Proof.
  iIntros (HN) "#Hinv".
  iInv N as (q) ">H" "Hclose".
  rewrite -(Qp_div_2 q).
  iDestruct (H0 (q/2)%Qp (q/2)%Qp with "H") as "[H1 H2]".
  iExists _; iFrame.
  iApply "Hclose".
  iExists _; iFrame.
Qed.

Section goose_lang.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.

Implicit Types (t : ty).
Implicit Types (stk : stuckness).

Transparent struct.alloc.

Theorem wp_allocStruct d stk E v :
  val_ty v (struct.t d) ->
  {{{ True }}}
    struct.alloc d v @ stk; E
  {{{ l, RET #l; l ↦[struct.t d] v }}}.
Proof.
  iIntros (Hty Φ) "_ HΦ".
  wp_call.
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

Definition struct_field_mapsto_def l q (d: descriptor) (f0: string) (fv:val): iProp Σ :=
  match field_offset d f0 with
  | Some (off, t) =>
    (* this struct is for the field type *)
    struct_mapsto (l +ₗ off) q t fv
  | None => ⌜fv = #()⌝
  end.

Definition struct_field_mapsto_aux : seal (@struct_field_mapsto_def). Proof. by eexists. Qed.
Definition struct_field_mapsto := struct_field_mapsto_aux.(unseal).
Definition struct_field_mapsto_eq : @struct_field_mapsto = @struct_field_mapsto_def := struct_field_mapsto_aux.(seal_eq).

Ltac unseal :=
  rewrite struct_field_mapsto_eq /struct_field_mapsto_def.

Global Instance struct_field_mapsto_timeless l d f q v : Timeless (struct_field_mapsto l q d f v).
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p. refine _.
  - refine _.
Qed.

Global Instance struct_field_mapsto_fractional l d f v : fractional.Fractional (λ q : Qp, struct_field_mapsto l q d f v).
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p. refine _.
  - refine _.
Qed.

Global Instance struct_field_mapsto_as_fractional l q d f v : fractional.AsFractional (struct_field_mapsto l q d f v) (λ q0 : Qp, struct_field_mapsto l q0 d f v) q.
Proof.
  split; [ done | apply _ ].
Qed.

Local Fixpoint struct_big_sep l q (d:descriptor) (v:val): iProp Σ :=
  match d with
  | [] => ⌜v = #()⌝
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => struct_mapsto l q t v1 ∗
                    struct_big_sep (l +ₗ ty_size t) q fs v2
    | _ => False
    end
  end.

Local Lemma struct_big_sep_ty l q d v :
  struct_big_sep l q d v -∗ ⌜val_ty v (struct.t d)⌝.
Proof.
  revert v l.
  induction d as [|[f t] fs]; simpl; intros.
  - iIntros (->) "!%".
    val_ty.
  - destruct v; auto.
    iIntros "[Hv1 Hv2]".
    iDestruct (struct_mapsto_ty with "Hv1") as %Hv1ty.
    iDestruct (IHfs with "Hv2") as %Hv2ty.
    iPureIntro.
    constructor; auto.
Qed.

Local Lemma struct_mapsto_to_big l q d v :
  struct_mapsto l q (struct.t d) v ⊣⊢ struct_big_sep l q d v.
Proof.
  apply (bient_pure_wlog (val_ty v (struct.t d))).
  { apply struct_mapsto_ty. }
  { apply struct_big_sep_ty. }
  intros Hty.
  (iInduction (d) as [| [f t] fs] "IH" forall (l v Hty)); simpl.
  - inv_ty Hty.
    rewrite struct_mapsto_eq /struct_mapsto_def /flatten_struct /=.
    rewrite left_id.
    auto.
  - inv_ty Hty.
    rewrite struct_mapsto_prod.
    iSplit; iIntros "[$ Hv2]".
    + iApply ("IH" with "[//] Hv2").
    + iApply ("IH" with "[//] Hv2").
Qed.

Local Fixpoint struct_big_fields_rec l q (d: descriptor) (fs:descriptor) (v:val): iProp Σ :=
  match fs with
  | [] => ⌜v = #()⌝
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => f ∷ struct_field_mapsto l q d f v1 ∗
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
  intros ?%Hnotin.
  apply H0.
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
  apply struct_big_sep_ty.
Qed.

(** This is the big splitting theorem, for converting from a monolithic struct
points-to fact to the individual field pointers. *)
Theorem struct_fields_split l q d {dwf: struct.wf d} v :
  struct_mapsto l q (struct.t d) v ⊣⊢ struct_fields l q d v.
Proof.
  rewrite struct_mapsto_to_big struct_big_sep_to_fields //.
Qed.

Lemma struct_mapsto_field_offset_acc l q d f0 (off: Z) t0 v :
  field_offset d f0 = Some (off, t0) ->
  struct_mapsto l q (struct.t d) v -∗
  (struct_mapsto (l +ₗ off) q t0 (getField_f d f0 v) ∗
   (∀ fv', struct_mapsto (l +ₗ off) q t0 fv' -∗ struct_mapsto l q (struct.t d) (setField_f d f0 fv' v))).
Proof.
  revert l v off t0.
  induction d as [|[f t] fs]; simpl; intros.
  - congruence.
  - iIntros "Hl".
    iDestruct (struct_mapsto_ty with "Hl") as %Hty.
    inv_ty Hty.
    destruct (f =? f0)%string.
    + invc H; simpl.
      rewrite loc_add_0.
      iDestruct (struct_mapsto_prod with "Hl") as "[Hv1 Hv2]".
      iFrame.
      iIntros (fv') "Hv1".
      iDestruct (struct_mapsto_prod with "[$Hv1 $Hv2]") as "$".
    + destruct_with_eqn (field_offset fs f0); try congruence.
      destruct p as [off' t'].
      invc H.
      iDestruct (struct_mapsto_prod with "Hl") as "[Hv1 Hv2]".
      erewrite IHfs by eauto.
      rewrite loc_add_assoc.
      iDestruct "Hv2" as "[Hf Hupd]".
      iFrame "Hf".
      iIntros (fv') "Hf".
      iApply struct_mapsto_prod; iFrame.
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

Lemma struct_mapsto_acc_offset_read l q d f0 (off: Z) t0 v :
  field_offset d f0 = Some (off, t0) ->
  struct_mapsto l q (struct.t d) v -∗
  (struct_mapsto (l +ₗ off) q t0 (getField_f d f0 v) ∗
   (struct_mapsto (l +ₗ off) q t0 (getField_f d f0 v) -∗ struct_mapsto l q (struct.t d) v)).
Proof.
  iIntros (Hf) "Hl".
  iDestruct (struct_mapsto_field_offset_acc with "Hl") as "[Hf Hupd]"; [ eauto | .. ].
  iFrame.
  iIntros "Hf".
  iSpecialize ("Hupd" with "Hf").
  rewrite setField_getField_f_id //.
Qed.

Notation "l ↦[ d :: f ]{ q } v" :=
  (struct_field_mapsto l q d f%string v%V).
Notation "l ↦[ d :: f ] v" :=
  (struct_field_mapsto l 1 d f%string v%V).

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

Lemma struct_mapsto_q l q t v :
  struct_mapsto l q t v ⊣⊢
  struct_mapsto l (q/2) t v ∗
  struct_mapsto l (q/2) t v.
Proof.
  rewrite -typed_mem.struct_mapsto_fractional Qp_div_2. auto.
Qed.

Global Instance struct_mapsto_as_mapsto d l v :
  AsMapsTo (struct_mapsto l 1 d v)
           (fun q => struct_mapsto l q d v).
Proof.
  split; [ done | apply _ | apply _ ].
Qed.

Lemma struct_field_mapsto_q l q d f v :
  struct_field_mapsto l q d f v ⊣⊢
  struct_field_mapsto l (q/2) d f v ∗
  struct_field_mapsto l (q/2) d f v.
Proof.
  unseal.
  destruct (field_offset d f).
  - destruct p.
    rewrite struct_mapsto_q. done.
  - iSplit; iIntros; iPureIntro; intuition.
Qed.

Global Instance struct_field_mapsto_as_mapsto d f l v :
  AsMapsTo (struct_field_mapsto l 1 d f v)
           (fun q => struct_field_mapsto l q d f v).
Proof.
  split; [ done | apply _ | apply _ ].
Qed.

Lemma struct_mapsto_acc f0 l q d v :
  struct_mapsto l q (struct.t d) v -∗
  (struct_field_mapsto l q d f0 (getField_f d f0 v) ∗
   (∀ fv', struct_field_mapsto l q d f0 fv' -∗ struct_mapsto l q (struct.t d) (setField_f d f0 fv' v))).
Proof.
  destruct (field_offset d f0) as [[off t0]|] eqn:Hf.
  - iIntros "Hl".
    iDestruct (struct_mapsto_field_offset_acc with "Hl") as "[Hf Hupd]"; [ eauto | ].
    unseal; rewrite Hf.
    iFrame.
  - unseal; rewrite Hf.
    iIntros "Hl".
    iSplitR; auto.
    { rewrite getField_f_none; auto. }
    iIntros (fv') "_".
    rewrite -> setField_f_none by auto; auto.
Qed.

Lemma struct_mapsto_acc_read f0 l q d v :
  struct_mapsto l q (struct.t d) v -∗
  (struct_field_mapsto l q d f0 (getField_f d f0 v) ∗
   (struct_field_mapsto l q d f0 (getField_f d f0 v) -∗ struct_mapsto l q (struct.t d) v)).
Proof.
  destruct (field_offset d f0) as [[off t0]|] eqn:Hf.
  - iIntros "Hl".
    iDestruct (struct_mapsto_acc_offset_read with "Hl") as "[Hf Hupd]"; [ eauto | ].
    unseal; rewrite Hf.
    iFrame.
  - unseal; rewrite Hf.
    iIntros "Hl".
    rewrite getField_f_none; auto.
Qed.

Theorem struct_field_mapsto_ty l q d z t f v :
  field_offset d f = Some (z, t) ->
  struct_field_mapsto l q d f v -∗ ⌜val_ty v t⌝.
Proof.
  unseal.
  intros ->.
  iIntros "Hl".
  iDestruct (struct_mapsto_ty with "Hl") as %Hty.
  auto.
Qed.

Theorem struct_field_mapsto_none l q d f v :
  field_offset d f = None ->
  struct_field_mapsto l q d f v -∗ ⌜v = #()⌝.
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
  - wp_call; auto.
  - inv_ty Hty.
    destruct (f =? f0)%string.
    + wp_call; auto.
    + wp_apply "IH"; auto.
Qed.

Transparent loadField storeField.

Theorem wp_loadField stk E l q d f fv :
  {{{ ▷ struct_field_mapsto l q d f fv }}}
    struct.loadF d f #l @ stk; E
  {{{ RET fv; struct_field_mapsto l q d f fv }}}.
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
    iDestruct (struct_field_mapsto_none with "Hl") as %->; auto.
    iApply ("HΦ" with "[$]").
Qed.

Lemma tac_wp_loadField Δ Δ' s E i K l q d f v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, struct_field_mapsto l q d f v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (struct.loadF d f (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???.
  rewrite -wp_bind. eapply bi.wand_apply; first exact: wp_loadField.
  rewrite into_laterN_env_sound -bi.later_sep envs_lookup_split //; simpl.
  by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
Qed.

Theorem wp_load_ro l t v :
  {{{ readonly (struct_mapsto l 1%Qp t v) }}}
    load_ty t #l
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ) "#Hro HΦ".
  iMod (readonly_load with "Hro") as (q) "Hl".
  wp_apply (wp_LoadAt with "Hl"); iIntros "_".
  iApply ("HΦ" with "[//]").
Qed.

Theorem wp_loadField_ro {stk E} l d f fv :
  {{{ readonly (struct_field_mapsto l 1%Qp d f fv) }}}
    struct.loadF d f #l @ stk; E
  {{{ RET fv; True }}}.
Proof.
  iIntros (Φ) "#Hro HΦ".
  iMod (readonly_load with "Hro") as (q) "Hl".
  wp_apply (wp_loadField with "Hl"); iIntros "_".
  iApply ("HΦ" with "[//]").
Qed.

Lemma tac_wp_loadField_ro {E} Δ s i K l d f v Φ :
  envs_lookup i Δ = Some (true, readonly (struct_field_mapsto l 1%Qp d f v))%I →
  envs_entails Δ (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (struct.loadF d f (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ? HΦ.
  rewrite -wp_bind. eapply bi.wand_apply; first exact: wp_loadField_ro.
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
  {{{ ▷ struct_field_mapsto l 1 d f fv }}}
    struct.storeF d f #l fv' @ stk; E
  {{{ RET #(); struct_field_mapsto l 1 d f fv' }}}.
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
    iDestruct (struct_field_mapsto_none with "Hl") as %->; auto.
    iApply ("HΦ" with "[$]").
Qed.

Opaque loadField storeField.

Lemma tac_wp_storeField Δ Δ' Δ'' stk E i K l d f v v' Φ :
  val_ty v' (field_ty d f) →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[d :: f] v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦[d :: f] v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ stk; E {{ Φ }}) →
  envs_entails Δ (WP fill K (struct.storeF d f (LitV l) (Val v')) @ stk; E {{ Φ }}).
Proof.
  intros Hty.
  rewrite envs_entails_eq=> ????.
  rewrite -wp_bind. eapply bi.wand_apply; first by eapply wp_storeField.
  rewrite into_laterN_env_sound -bi.later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
Qed.

Theorem wp_loadField_struct stk E l q d f v :
  {{{ struct_mapsto l q (struct.t d) v }}}
    struct.loadF d f #l @ stk; E
  {{{ RET (getField_f d f v); struct_mapsto l q (struct.t d) v }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  iDestruct (struct_mapsto_acc_read f with "Hs") as "[Hf Hupd]".
  wp_apply (wp_loadField with "Hf"); iIntros "Hf".
  iApply "HΦ".
  iApply ("Hupd" with "[$]").
Qed.

Theorem wp_storeField_struct stk E l d f v fv' :
  val_ty fv' (field_ty d f) ->
  {{{ struct_mapsto l 1 (struct.t d) v }}}
    struct.storeF d f #l fv' @ stk; E
  {{{ RET #(); struct_mapsto l 1 (struct.t d) (setField_f d f fv' v) }}}.
Proof.
  iIntros (Hty Φ) "Hs HΦ".
  iDestruct (struct_mapsto_acc f with "Hs") as "[Hf Hupd]".
  wp_apply (wp_storeField with "Hf"); auto.
  iIntros "Hf".
  iApply "HΦ".
  iApply ("Hupd" with "[$]").
Qed.

Theorem wp_loadField_inv N l d f v stk E :
  ↑N ⊆ E →
  {{{ inv N (∃ q, l ↦[d :: f]{q} v) }}}
    struct.loadF d f #l @ stk; E
  {{{ RET v; True }}}.
Proof.
  iIntros (HN Φ) "#Hinv HΦ".
  iMod (inv_readonly_acc with "Hinv") as (q) "Hv"; auto.
  wp_apply (wp_loadField with "Hv"); iIntros "_".
  iApply "HΦ"; done.
Qed.

End goose_lang.

Notation "l ↦[ d :: f ]{ q } v" :=
  (struct_field_mapsto l q d f%string v%V).
Notation "l ↦[ d :: f ] v" :=
  (struct_field_mapsto l 1 d f%string v%V).

Tactic Notation "wp_loadField" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_ :: _]{_} _)%I) => l end in
    iAssumptionCore || fail 1 "wp_load: cannot find" l "↦[d :: f] ?" in
  wp_pures;
  match goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_loadField_ro _ _ _ K))
      |fail 1 "wp_loadField: cannot find 'struct.loadF' in" e];
    [iAssumptionCore
    |wp_finish]
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_loadField _ _ _ _ _ K))
      |fail 2 "wp_loadField: cannot find 'struct.loadF' in" e];
    [iSolveTC
    |solve_mapsto ()
    |wp_finish]
  | _ => fail 1 "wp_loadField: not a 'wp'"
  end.

Tactic Notation "wp_storeField" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_ :: _]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_storeField: cannot find" l "↦[d :: f] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_storeField _ _ _ _ _ _ K))
      |fail 1 "wp_storeField: cannot find 'storeField' in" e];
    [val_ty
    |iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_storeField: not a 'wp'"
  end.
