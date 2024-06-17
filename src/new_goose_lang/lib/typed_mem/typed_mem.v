From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From Perennial.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang Require Export typed_mem.impl struct.impl slice.
Require Import Coq.Program.Equality.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Program Definition go_type_ind :=
    λ (P : go_type → Prop) (f : P boolT) (f0 : P uint8T) (f1 : P uint16T) (f2 : P uint32T)
      (f3 : P uint64T) (f4 : P int8T) (f5 : P int16T) (f6 : P int32T) (f7 : P int64T)
      (f8 : P stringT) (f9 : ∀ elem : go_type, P elem → P (sliceT elem))
      (f10 : ∀ (decls : list (string * go_type)) (Hfields : ∀ t, In t decls.*2 → P t), P (structT decls))
      (f11 : P ptrT) (f12 : P funcT) (f13 : P interfaceT)
      (f14 : ∀ key : go_type, P key → ∀ elem : go_type, P elem → P (mapT key elem))
      (f15 : ∀ elem : go_type, P elem → P (chanT elem)),
    fix F (g : go_type) : P g :=
      match g as g0 return (P g0) with
      | boolT => f
      | uint8T => f0
      | uint16T => f1
      | uint32T => f2
      | uint64T => f3
      | int8T => f4
      | int16T => f5
      | int32T => f6
      | int64T => f7
      | stringT => f8
      | sliceT elem => f9 elem (F elem)
      | structT decls => f10 decls _
      | ptrT => f11
      | funcT => f12
      | interfaceT => f13
      | mapT key elem => f14 key (F key) elem (F elem)
      | chanT elem => f15 elem (F elem)
      end.
  Obligation 1.
  intros.
  revert H.
  enough (Forall P decls.*2).
  1:{
    intros.
    rewrite List.Forall_forall in H.
    apply H. done.
  }
  induction decls; first done.
  destruct a. apply Forall_cons. split.
  { apply F. }
  { apply IHdecls. }
  Defined.

  Inductive has_go_type : val → go_type → Prop :=
  | has_go_type_bool (b : bool) : has_go_type #b boolT
  | has_go_type_uint64 (x : w64) : has_go_type #x uint64T
  | has_go_type_uint32 (x : w32) : has_go_type #x uint32T
  | has_go_type_uint16 : has_go_type nil uint16T
  | has_go_type_uint8 (x : w8) : has_go_type #x uint8T

  | has_go_type_int64 (x : w64) : has_go_type #x int64T
  | has_go_type_int32 (x : w32) : has_go_type #x int32T
  | has_go_type_int16 : has_go_type nil int16T
  | has_go_type_int8 (x : w8) : has_go_type #x int8T

  | has_go_type_string (s : string) : has_go_type #(str s) stringT
  | has_go_type_slice elem (s : slice.t) : has_go_type (slice_val s) (sliceT elem)
  | has_go_type_slice_nil elem : has_go_type slice_nil (sliceT elem)

  | has_go_type_struct
      (d : descriptor) fvs
      (Hfields : ∀ f t, In (f, t) d → has_go_type (default (zero_val t) (assocl_lookup fvs f)) t)
    : has_go_type (struct.mk_f d fvs) (structT d)
  | has_go_type_ptr (l : loc) : has_go_type #l ptrT
  | has_go_type_func f e v : has_go_type (RecV f e v) funcT
  | has_go_type_func_nil : has_go_type nil funcT

  (* FIXME: interface_val *)
  | has_go_type_interface (s : slice.t) : has_go_type (slice_val s) interfaceT
  | has_go_type_interface_nil : has_go_type interface_nil interfaceT

  | has_go_type_mapT kt vt (l : loc) : has_go_type #l (mapT kt vt)
  | has_go_type_chanT t (l : loc) : has_go_type #l (chanT t)
  .

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    induction t using go_type_ind; try econstructor.
    replace (zero_val (structT decls)) with (struct.mk_f decls []).
    {
      econstructor. intros. simpl. apply Hfields.
      apply in_map_iff. eexists _.
      split; last done. done.
    }
    induction decls.
    { simpl. replace (#()) with (struct.mk_f [] []) by done. econstructor. }
    destruct a. simpl.
    f_equal.
    apply IHdecls.
    intros.
    apply Hfields.
    simpl. right. done.
  Qed.

  Definition typed_pointsto_def l (dq : dfrac) (t : go_type) (v : val) : iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{dq} vj) ∗ ⌜ has_go_type v t ⌝)%I.
  Definition typed_pointsto_aux : seal (@typed_pointsto_def). Proof. by eexists. Qed.
  Definition typed_pointsto := typed_pointsto_aux.(unseal).
  Definition typed_pointsto_eq : @typed_pointsto = @typed_pointsto_def := typed_pointsto_aux.(seal_eq).

  Notation "l ↦[ t ] dq v" := (typed_pointsto l dq t v%V)
                                   (at level 20, dq custom dfrac at level 1, t at level 50,
                                    format "l  ↦[ t ] dq  v") : bi_scope.

  Ltac unseal := rewrite ?typed_pointsto_eq /typed_pointsto_def.

  Global Instance typed_pointsto_timeless l t q v: Timeless (l ↦[t]{q} v).
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_fractional l t v: fractional.Fractional (λ q, l ↦[t]{#q} v)%I.
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_as_fractional l t v q: fractional.AsFractional
                                                     (l ↦[t]{#q} v)
                                                     (λ q, l ↦[t]{#q} v)%I q.
  Proof. constructor; auto. apply _. Qed.

  Definition is_primitive_type (t : go_type) : Prop :=
    match t with
    | structT d => False
    | funcT => False
    | sliceT e => False
    | interfaceT => False
    | _ => True
    end.

  Global Instance typed_pointsto_combine_sep_gives l t dq1 dq2 v1 v2 :
    is_primitive_type t →
    CombineSepGives (l ↦[t]{dq1} v1)%I (l ↦[t]{dq2} v2)%I ⌜ ✓(dq1 ⋅ dq2) ∧ v1 = v2 ⌝%I.
  Proof.
    intros Hprim.
    unfold CombineSepGives.
    unseal.
    iIntros "[[H1 %Hty1] [H2 %Hty2]]".
    inversion Hty1; subst.
    1-10,14-16,19-20: inversion Hty2; subst; rewrite /= ?loc_add_0 ?right_id;
      iDestruct (heap_pointsto_agree with "[$]") as "%H";
      inversion H; subst; iCombine "H1 H2" gives %?; iModIntro; iPureIntro; done.
    all: by exfalso.
  Qed.

  Local Lemma has_go_type_len {v t} :
    has_go_type v t ->
    length (flatten_struct v) = (go_type_size t).
  Proof.
    rewrite go_type_size_unseal.
    induction 1; simpl; auto.
    induction d.
    { done. }
    destruct a. cbn.
    rewrite app_length.
    rewrite IHd.
    { f_equal. apply H. by left. }
    { clear H IHd. intros. apply Hfields. by right. }
    { intros. apply H. simpl. by right. }
  Qed.

  Local Lemma wp_AllocAt t stk E v :
    has_go_type v t ->
    {{{ True }}}
      ref v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_apply wp_allocN_seq; first by word.
    change (uint.nat 1) with 1%nat; simpl.
    iIntros (l) "[Hl _]".
    iApply "HΦ".
    unseal.
    iSplitL; auto.
    rewrite Z.mul_0_r loc_add_0.
    iFrame.
  Qed.

  Lemma wp_ref_ty t stk E v :
    has_go_type v t ->
    {{{ True }}}
      ref_ty t v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    rewrite ref_ty_unseal.
    wp_call.
    wp_apply (wp_AllocAt t); auto.
  Qed.


  Lemma wp_ref_of_zero stk E t :
    {{{ True }}}
      ref (zero_val t) @ stk; E
    {{{ l, RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_AllocAt t); eauto.
    apply zero_val_has_go_type.
  Qed.

  Lemma wp_typed_load stk E q l t v :
    {{{ ▷ l ↦[t]{q} v }}}
      load_ty t #l @ stk; E
    {{{ RET v; l ↦[t]{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    unseal.
    iDestruct "Hl" as "[Hl %Hty]".
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦{q} vj) -∗ Φ v))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    rewrite load_ty_unseal.
    rename l into l'.
    iInduction Hty as [ | | | | | | | | | | | | | | | | | | |] "IH" forall (l' Φ) "HΦ".
    1-10,14-16,19-20: rewrite /= ?loc_add_0 ?right_id; wp_pures;
      wp_apply (wp_load with "[$]"); done.
    1-2,4-5: rewrite /= ?right_id; wp_pures; rewrite Z.mul_0_r;
      iDestruct "Hl" as "(H1 & H2 & H3)";
      wp_apply (wp_load with "[$H1]"); iIntros;
      wp_apply (wp_load with "[$H2]"); iIntros;
      wp_apply (wp_load with "[$H3]"); iIntros;
      wp_pures; iApply "HΦ"; by iFrame.
    - (* case structT *)
      iInduction d as [|] "IH2" forall (l' Φ).
      { wp_pures. iApply "HΦ". by iFrame. }
      destruct a.
      wp_pures.
      iDestruct "Hl" as "[Hf Hl]".
      wp_apply ("IH" with "[] Hf").
      { iPureIntro. by left. }
      iIntros "Hf".
      wp_pures.
      wp_apply ("IH2" with "[] [] [Hl]").
      { iPureIntro. intros. apply Hfields. by right. }
      { iModIntro. iIntros. wp_apply ("IH" with "[] [$] [$]").
        iPureIntro. by right. }
      {
        erewrite has_go_type_len.
        2:{ eapply Hfields. by left. }
        rewrite right_id. setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
        iFrame.
      }
      iIntros "Hl".
      wp_pures.
      iApply "HΦ".
      iFrame.
      erewrite has_go_type_len.
      2:{ eapply Hfields. by left. }
      rewrite right_id. setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      by iFrame.
  Qed.

  Lemma wp_store stk E l v v' :
    {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ stk; E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". rewrite /Store.
    wp_apply (wp_prepare_write with "Hl"); iIntros "[Hl Hl']".
    by wp_apply (wp_finish_store with "[$Hl $Hl']").
  Qed.

  Lemma wp_typed_store stk E l t v v' :
    has_go_type v' t ->
    {{{ ▷ l ↦[t] v }}}
      (#l <-[t] v')%V @ stk; E
    {{{ RET #(); l ↦[t] v' }}}.
  Proof.
    intros Hty.
    iIntros (Φ) ">Hl HΦ".
    unseal.
    iDestruct "Hl" as "[Hl %Hty_old]".
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v', (l +ₗ j)↦ vj) -∗ Φ #()))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    rename l into l'.
    rewrite store_ty_unseal.
    iInduction Hty_old as [ | | | | | | | | | | | | | | | | | | |] "IH" forall (v' Hty l' Φ) "HΦ".
    1-10,14-16,19-20:
      simpl; rewrite ?loc_add_0 ?right_id; wp_pures; wp_apply (wp_store with "[$]");
      iIntros "H"; iApply "HΦ"; inversion Hty; subst;
      simpl; rewrite ?loc_add_0 ?right_id; wp_pures; iFrame.
    1-2,4-5: (* non-nil slice, nil slice, non-nil interface, nil interface *)
      simpl; wp_pures; iDestruct "Hl" as "(H1 & H2 & H3)";
      inversion Hty; subst;
        wp_pures; rewrite ?loc_add_0 ?right_id;
        (* FIXME: unnamed H1-H3 don't work with ["[$]"] *)
        wp_apply (wp_store with "[$H1]"); iIntros;
        wp_apply (wp_store with "[$H2]"); iIntros;
        wp_apply (wp_store with "[$H3]"); iIntros;
        iApply "HΦ"; rewrite /= ?loc_add_0 ?right_id; iFrame.
    - (* struct *)
      iInduction d as [|] "IH2" forall (l' v' Hty).
      { simpl. wp_pures. iApply "HΦ". inversion Hty; subst. done. }
      destruct a. inversion Hty; subst.
      wp_pures.
      iDestruct "Hl" as "[Hf Hl]".
      erewrite has_go_type_len.
      2:{ eapply Hfields. by left. }
      setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      wp_apply ("IH" with "[] [] [$Hf]").
      { iPureIntro. simpl. by left. }
      { iPureIntro. apply Hfields0. by left. }
      iIntros "Hf".
      wp_pures.
      wp_apply ("IH2" with "[] [] [] [Hl]").
      { iPureIntro. intros. apply Hfields. by right. }
      { iPureIntro. econstructor. intros. apply Hfields0. by right. }
      { iModIntro. iIntros. wp_apply ("IH" with "[] [//] [$] [$]"). iPureIntro. by right. }
      { rewrite ?right_id.  iFrame. }
      iIntros "Hl".
      iApply "HΦ".
      iFrame.
      erewrite has_go_type_len.
      2:{ eapply Hfields0. by left. }
      setoid_rewrite Nat2Z.inj_add. setoid_rewrite <- loc_add_assoc.
      rewrite ?right_id. iFrame.
  Qed.

  Lemma tac_wp_load_ty Δ Δ' s E i K l q t v Φ is_pers :
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (is_pers, typed_pointsto l q t v)%I →
    envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (load_ty t (LitV l)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal=> ? ? Hwp.
    rewrite -wp_bind. eapply bi.wand_apply; first by apply bi.wand_entails, wp_typed_load.
    iIntros "H".
    rewrite into_laterN_env_sound -bi.later_sep envs_lookup_split //; simpl.
    iNext.
    destruct is_pers; simpl.
    + iDestruct "H" as "[#? H]". iFrame "#". iIntros.
      iSpecialize ("H" with "[$]"). by wp_apply Hwp.
    + iDestruct "H" as "[? H]". iFrame. iIntros.
      iSpecialize ("H" with "[$]"). by wp_apply Hwp.
  Qed.

  Lemma tac_wp_store_ty Δ Δ' Δ'' stk E i K l t v v' Φ :
    has_go_type v' t ->
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦[t] v)%I →
    envs_simple_replace i false (Esnoc Enil i (l ↦[t] v')) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ stk; E {{ Φ }}) →
    envs_entails Δ (WP fill K (store_ty t (PairV (LitV l) v')) @ stk; E {{ Φ }}).
  Proof.
    intros Hty.
    rewrite envs_entails_unseal=> ????.
    rewrite -wp_bind. eapply bi.wand_apply; first by eapply bi.wand_entails, wp_typed_store.
    rewrite into_laterN_env_sound -bi.later_sep envs_simple_replace_sound //; simpl.
    rewrite right_id. by apply bi.later_mono, bi.sep_mono_r, bi.wand_mono.
  Qed.

Lemma wp_typed_cmpxchg_fail s E l dq v' v1 v2 t :
  is_primitive_type t →
  has_go_type v1 t →
  v' ≠ v1 →
  {{{ ▷ l ↦[t]{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦[t]{dq} v' }}}.
Proof.
  intros Hprim Hty Hne.
  iIntros (?) "Hl HΦ". unseal.
  iDestruct "Hl" as "[H >%Hty_old]".
  destruct t; try by exfalso.
  1-13: inversion Hty_old; subst;
    inversion Hty; subst;
    simpl; rewrite loc_add_0 right_id;
    wp_apply (wp_cmpxchg_fail with "[$]"); first done; first (by econstructor);
    iIntros; iApply "HΦ";
    iFrame; done.
Qed.

Lemma wp_typed_cmpxchg_suc s E l v' v1 v2 t :
  is_primitive_type t →
  has_go_type v2 t →
  v' = v1 →
  {{{ ▷ l ↦[t] v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦[t] v2 }}}.
Proof.
  intros Hprim Hty Heq.
  iIntros (?) "Hl HΦ". unseal.
  iDestruct "Hl" as "[H >%Hty_old]".
  destruct t; try by exfalso.
  1-13: inversion Hty_old; subst;
    inversion Hty; subst;
    simpl; rewrite loc_add_0 right_id;
    wp_apply (wp_cmpxchg_suc with "[$H]"); first done; first (by econstructor);
    iIntros; iApply "HΦ"; iFrame; done.
Qed.

End goose_lang.

Notation "l ↦[ t ] dq v" := (typed_pointsto l dq t v%V)
                              (at level 20, dq custom dfrac at level 50, t at level 50,
                               format "l  ↦[ t ] dq  v") : bi_scope.

Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    ( first
        [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load_ty _ _ _ _ _ K))
        |fail 1 "wp_load: cannot find 'load_ty' in" e];
      [tc_solve
      |solve_pointsto ()
      |wp_finish] )
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_] _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦[t] ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store_ty _ _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'store_ty' in" e];
    [(tc_solve || fail "could not establish [has_go_type]") (* solve [has_go_type v' t] *)
    |tc_solve
    |solve_pointsto ()
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Hint Extern 1 (is_primitive_type _) => refine I: typeclass_instances.
