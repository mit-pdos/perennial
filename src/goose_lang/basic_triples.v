From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export
     lang notation array typing struct
     tactics lifting proofmode.
From Perennial.goose_lang Require Import slice.
Import uPred.

Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types t : ty.
Implicit Types stk : stuckness.
Implicit Types off : nat.

Definition ArbitraryIntUpto: val :=
  λ: "bound",
  let: "z" := ArbitraryInt in
  if: Var "z" < Var "bound" then Var "z" else Var "bound".

Lemma wp_ArbitraryIntUpto stk E (max: u64) :
  {{{ True }}}
    ArbitraryIntUpto #max @ stk; E
  {{{ (x:u64), RET #x; ⌜int.val x <= int.val max⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_ArbitraryInt.
  iIntros (x) "_".
  wp_pures.
  wp_if_destruct.
  - iApply "HΦ".
    iPureIntro.
    word.
  - iApply "HΦ".
    iPureIntro.
    word.
Qed.

Lemma wp_ref_to stk E t v :
  val_ty v t ->
  {{{ True }}} ref_to t (Val v) @ stk; E {{{ l, RET LitV (LitLoc l); l ↦[t] v }}}.
Proof.
  iIntros (Hty Φ) "_ HΦ".
  wp_call.
  iApply wp_alloc; eauto with lia.
Qed.

Lemma tac_wp_alloc Δ Δ' s E j K v t Φ :
  val_ty v t ->
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦[t] v)) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (ref_to t (Val v)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> Hty ? HΔ.
  rewrite -wp_bind /ref_to. eapply wand_apply; first exact: wp_ref_to.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite right_id wand_elim_r.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' s E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ????.
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

(* local version just for this file *)
Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Theorem wp_forBreak (I X: iProp Σ) stk E (body: val) :
  {{{ I }}}
    body #() @ stk; E
  {{{ r, RET #r; I ∗ ⌜r=true⌝ ∨ X ∗ ⌜r=false⌝ }}} -∗
  {{{ I }}}
    (for: (λ: <>, #true)%V ; (λ: <>, (λ: <>, #())%V #())%V :=
       body) @ stk; E
  {{{ RET #(); X }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> I HΦ".
  rewrite /For.
  wp_lam.
  wp_let.
  wp_let.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  iLöb as "IH".
  wp_pures.
  iDestruct ("Hbody" with "I") as "Hbody1".
  wp_bind (body _).
  iApply "Hbody1".
  iNext.
  iIntros (r) "Hr".
  iDestruct "Hr" as "[[I %] | [X %]]"; subst.
  - iDestruct ("IH" with "I HΦ") as "IH1".
    wp_let.
    wp_if.
    wp_lam.
    wp_lam.
    wp_pure (Rec _ _ _).
    wp_lam.
    iApply "IH1".
  - wp_pures.
    iApply "HΦ".
    iApply "X".
Qed.

Theorem wp_forUpto (I: u64 -> iProp Σ) stk E (max:u64) (l:loc) (body: val) :
  (∀ (i:u64),
      {{{ I i ∗ l ↦ #i ∗ ⌜int.val i < int.val max⌝ }}}
        body #() @ stk; E
      {{{ RET #true; I (word.add i (U64 1)) ∗ l ↦ #i }}}) -∗
  {{{ I 0 ∗ l ↦ #0 }}}
    (for: (λ:<>, #max > ![uint64T] #l)%V ; (λ:<>, #l <-[uint64T] ![uint64T] #l + #1)%V :=
       body) @ stk; E
  {{{ RET #(); I max ∗ l ↦ #max }}}.
Proof.
  iIntros "#Hbody".
  iIntros (Φ) "!> (H0 & Hl) HΦ".
  rewrite /For /Continue.
  wp_lam.
  wp_let.
  wp_let.
  wp_pure (Rec _ _ _).
  match goal with
  | |- context[RecV (BNamed "loop") _ ?body] => set (loop:=body)
  end.
  remember (U64 0) as x.
  assert (0 <= int.val x <= int.val max) as Hbounds by (subst; word).
  clear Heqx.
  iDestruct "H0" as "HIx".
  iLöb as "IH" forall (x Hbounds).
  wp_pures.
  wp_load.
  wp_pures.
  wp_if_destruct.
  - wp_apply ("Hbody" with "[$HIx $Hl]").
    { iPureIntro; lia. }
    iIntros "[HIx Hl]".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply (wp_store with "Hl"); iIntros "Hl".
    wp_seq.
    iApply ("IH" with "[] HIx Hl").
    { iPureIntro; word. }
    iFrame.
  - assert (int.val x = int.val max) by word.
    apply word.unsigned_inj in H; subst.
    iApply ("HΦ" with "[$]").
Qed.

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
      econstructor; eauto.
    + destruct_with_eqn (field_offset fs f0); try congruence.
      destruct p as [off t'].
      invc H0.
      inv_ty H.
      econstructor; eauto.
Qed.

Definition struct_field_mapsto l q (d: descriptor) (f0: string) (fv:val): iProp Σ :=
  match field_offset d f0 with
  | Some (off, t) =>
    (* this struct is for the field type *)
    struct_mapsto (l +ₗ off) q t fv
  | None => ⌜fv = #()⌝
  end.

Fixpoint struct_big_sep l q (d:descriptor) (v:val): iProp Σ :=
  match d with
  | [] => emp
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => struct_mapsto l q t v1 ∗
                    struct_big_sep (l +ₗ ty_size t) q fs v2
    | _ => emp
    end
  end.

Theorem struct_mapsto_to_big l q d v :
  val_ty v (struct.t d) ->
  struct_mapsto l q (struct.t d) v ⊣⊢ struct_big_sep l q d v.
Proof.
  intros Hty.
  (iInduction (d) as [| [f t] fs] "IH" forall (l v Hty)); simpl.
  - inv_ty Hty.
    rewrite /struct_mapsto /flatten_struct /=.
    rewrite left_id.
    auto.
  - inv_ty Hty.
    rewrite struct_ptsto_pair_split.
    iSplit; iIntros "[$ Hv2]".
    + iApply ("IH" with "[//] Hv2").
    + iApply ("IH" with "[//] Hv2").
Qed.

Fixpoint struct_big_fields_rec l q (d: descriptor) (fs:descriptor) (v:val): iProp Σ :=
  match fs with
  | [] => emp
  | (f,t)::fs =>
    match v with
    | PairV v1 v2 => struct_field_mapsto l q d f v1 ∗
                    struct_big_fields_rec l q d fs v2
    | _ => emp
    end
  end.

Definition struct_big_fields l q d v : iProp Σ := struct_big_fields_rec l q d d v.

Theorem field_offset_prefix (fs1: descriptor) f t (fs: descriptor) :
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

Theorem NoDup_app_singleton A l (x:A) :
  NoDup (l ++ [x]) ->
  x ∉ l.
Proof.
  intros Hnodup%NoDup_app.
  destruct Hnodup as (_&Hnotin&_).
  intros ?%Hnotin.
  apply H0.
  constructor.
Qed.

Theorem ty_size_struct_app d1 d2 :
  ty_size (struct.t (d1 ++ d2)) =
  ty_size (struct.t d1) + ty_size (struct.t d2).
Proof.
  induction d1 as [|[f t] fs]; simpl; auto.
  rewrite IHfs; lia.
Qed.

Lemma struct_big_sep_to_big_fields_gen l q fs1 fs v :
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
  - rewrite /struct_field_mapsto.
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

Lemma struct_big_sep_to_big_fields l q d {dwf: struct.wf d} v :
  struct_big_fields l q d v = struct_big_sep l q d v.
Proof.
  intros.
  rewrite /struct_big_fields.
  change d with (nil ++ d) at 1.
  rewrite -> struct_big_sep_to_big_fields_gen by apply descriptor_NoDup.
  simpl.
  rewrite loc_add_0 //.
Qed.

Theorem struct_mapsto_field_offset_acc l q d f0 (off: Z) t0 v :
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
      iDestruct (struct_ptsto_pair_split with "Hl") as "[Hv1 Hv2]".
      iFrame.
      iIntros (fv') "Hv1".
      iDestruct (struct_ptsto_pair_split with "[$Hv1 $Hv2]") as "$".
    + destruct_with_eqn (field_offset fs f0); try congruence.
      destruct p as [off' t'].
      invc H.
      iDestruct (struct_ptsto_pair_split with "Hl") as "[Hv1 Hv2]".
      erewrite IHfs by eauto.
      rewrite loc_add_assoc.
      iDestruct "Hv2" as "[Hf Hupd]".
      iFrame "Hf".
      iIntros (fv') "Hf".
      iApply struct_ptsto_pair_split; iFrame.
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

Theorem struct_mapsto_acc_offset_read l q d f0 (off: Z) t0 v :
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
  (struct_field_mapsto l q%Qp d f%string v%V)
    (at level 20, q at level 50, d at level 50, f at level 50,
    format "l  ↦[ d  ::  f ]{ q }  v").
Notation "l ↦[ d :: f ] v" :=
  (struct_field_mapsto l 1%Qp d f%string v%V)
    (at level 20, d at level 50, f at level 50,
    format "l  ↦[ d  ::  f ]  v").

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

Theorem struct_mapsto_acc f0 l q d v :
  struct_mapsto l q (struct.t d) v -∗
  (struct_field_mapsto l q d f0 (getField_f d f0 v) ∗
   (∀ fv', struct_field_mapsto l q d f0 fv' -∗ struct_mapsto l q (struct.t d) (setField_f d f0 fv' v))).
Proof.
  destruct (field_offset d f0) as [[off t0]|] eqn:Hf.
  - iIntros "Hl".
    iDestruct (struct_mapsto_field_offset_acc with "Hl") as "[Hf Hupd]"; [ eauto | ].
    rewrite /struct_field_mapsto Hf.
    iFrame.
  - rewrite /struct_field_mapsto Hf.
    iIntros "Hl".
    iSplitR; auto.
    { rewrite getField_f_none; auto. }
    iIntros (fv') "_".
    rewrite -> setField_f_none by auto; auto.
Qed.

Theorem struct_mapsto_acc_read f0 l q d v :
  struct_mapsto l q (struct.t d) v -∗
  (struct_field_mapsto l q d f0 (getField_f d f0 v) ∗
   (struct_field_mapsto l q d f0 (getField_f d f0 v) -∗ struct_mapsto l q (struct.t d) v)).
Proof.
  destruct (field_offset d f0) as [[off t0]|] eqn:Hf.
  - iIntros "Hl".
    iDestruct (struct_mapsto_acc_offset_read with "Hl") as "[Hf Hupd]"; [ eauto | ].
    rewrite /struct_field_mapsto Hf.
    iFrame.
  - rewrite /struct_field_mapsto Hf.
    iIntros "Hl".
    rewrite getField_f_none; auto.
Qed.

Theorem struct_field_mapsto_ty l q d z t f v :
  field_offset d f = Some (z, t) ->
  struct_field_mapsto l q d f v -∗ ⌜val_ty v t⌝.
Proof.
  rewrite /struct_field_mapsto.
  intros ->.
  iIntros "Hl".
  iDestruct (struct_mapsto_ty with "Hl") as %Hty.
  auto.
Qed.

Theorem struct_field_mapsto_none l q d f v :
  field_offset d f = None ->
  struct_field_mapsto l q d f v -∗ ⌜v = #()⌝.
Proof.
  rewrite /struct_field_mapsto.
  intros ->.
  auto.
Qed.

Transparent loadField storeField.

Theorem wp_loadField stk E l q d f fv :
  {{{ struct_field_mapsto l q d f fv }}}
    struct.loadF d f #l @ stk; E
  {{{ RET fv; struct_field_mapsto l q d f fv }}}.
Proof.
  rewrite /loadField.
  destruct (field_offset d f) as [[z t]|] eqn:Hf.
  - iIntros (Φ) "Hl HΦ".
    wp_pures.
    rewrite /struct_field_mapsto Hf.
    rewrite Z.mul_1_r.
    wp_apply (wp_LoadAt with "Hl"); iIntros "Hl".
    iApply ("HΦ" with "[$]").
  - iIntros (Φ) "Hl HΦ".
    wp_pures.
    iDestruct (struct_field_mapsto_none with "Hl") as %->; auto.
    iApply ("HΦ" with "[$]").
Qed.

Definition field_ty d f: ty :=
  match field_offset d f with
  | Some (_, t) => t
  | None => unitT
  end.

Theorem wp_storeField stk E l d f fv fv' :
  val_ty fv' (field_ty d f) ->
  {{{ struct_field_mapsto l 1 d f fv }}}
    struct.storeF d f #l fv' @ stk; E
  {{{ RET #(); struct_field_mapsto l 1 d f fv' }}}.
Proof.
  rewrite /storeField /field_ty.
  intros Hty.
  destruct (field_offset d f) as [[z t]|] eqn:Hf.
  - iIntros (Φ) "Hl HΦ".
    wp_pures.
    rewrite /struct_field_mapsto Hf.
    rewrite Z.mul_1_r.
    wp_apply (wp_StoreAt with "Hl"); auto.
  - inv_ty Hty.
    iIntros (Φ) "Hl HΦ".
    wp_pures.
    iDestruct (struct_field_mapsto_none with "Hl") as %->; auto.
    iApply ("HΦ" with "[$]").
Qed.

Opaque loadField storeField.

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

(*
Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.
*)

End heap.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" H "not fresh"
        |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc].
     If that fails, it tries to use the lemma [tac_wp_allocN] for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [val_ty
        |iSolveTC
        |finish ()]
    in process_single ()
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".
